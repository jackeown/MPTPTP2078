%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:04 EST 2020

% Result     : Theorem 6.39s
% Output     : CNFRefutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 218 expanded)
%              Number of leaves         :   37 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :  167 ( 444 expanded)
%              Number of equality atoms :   65 ( 142 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_299,plain,(
    ~ v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1297,plain,(
    ! [A_120,B_121] :
      ( m1_subset_1(k2_pre_topc(A_120,B_121),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ l1_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_54,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_128,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_746,plain,(
    ! [A_101,B_102,C_103] :
      ( m1_subset_1(k7_subset_1(A_101,B_102,C_103),k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_757,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_746])).

tff(c_815,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_757])).

tff(c_1300,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1297,c_815])).

tff(c_1309,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1300])).

tff(c_1311,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_757])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] :
      ( k7_subset_1(A_24,B_25,C_26) = k4_xboole_0(B_25,C_26)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1675,plain,(
    ! [C_133] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_133) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_133) ),
    inference(resolution,[status(thm)],[c_1311,c_24])).

tff(c_1684,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1675,c_128])).

tff(c_12,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_333,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_354,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_333])).

tff(c_358,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_354])).

tff(c_20,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    ! [A_67,B_68] : k1_setfam_1(k2_tarski(A_67,B_68)) = k3_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    ! [B_69,A_70] : k1_setfam_1(k2_tarski(B_69,A_70)) = k3_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_139])).

tff(c_26,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_160,plain,(
    ! [B_69,A_70] : k3_xboole_0(B_69,A_70) = k3_xboole_0(A_70,B_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_26])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_393,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_425,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k3_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_393])).

tff(c_434,plain,(
    ! [A_11] : k4_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_425])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k4_xboole_0(k3_xboole_0(A_16,B_17),C_18) = k3_xboole_0(A_16,k4_xboole_0(B_17,C_18)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1424,plain,(
    ! [A_126,B_127,C_128] : k5_xboole_0(k3_xboole_0(A_126,B_127),k3_xboole_0(C_128,B_127)) = k3_xboole_0(k5_xboole_0(A_126,C_128),B_127) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1435,plain,(
    ! [A_126,B_127] : k3_xboole_0(k5_xboole_0(A_126,k3_xboole_0(A_126,B_127)),B_127) = k4_xboole_0(k3_xboole_0(A_126,B_127),B_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_1424,c_4])).

tff(c_1500,plain,(
    ! [B_129,A_130] : k3_xboole_0(B_129,k4_xboole_0(A_130,B_129)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_160,c_4,c_434,c_18,c_1435])).

tff(c_1533,plain,(
    ! [B_129,A_130] : k4_xboole_0(B_129,k4_xboole_0(A_130,B_129)) = k5_xboole_0(B_129,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1500,c_4])).

tff(c_1576,plain,(
    ! [B_129,A_130] : k4_xboole_0(B_129,k4_xboole_0(A_130,B_129)) = B_129 ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_1533])).

tff(c_1999,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1684,c_1576])).

tff(c_597,plain,(
    ! [A_93,B_94,C_95] :
      ( k7_subset_1(A_93,B_94,C_95) = k4_xboole_0(B_94,C_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_603,plain,(
    ! [C_95] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_95) = k4_xboole_0('#skF_2',C_95) ),
    inference(resolution,[status(thm)],[c_42,c_597])).

tff(c_2162,plain,(
    ! [A_143,B_144] :
      ( k7_subset_1(u1_struct_0(A_143),B_144,k2_tops_1(A_143,B_144)) = k1_tops_1(A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2184,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2162])).

tff(c_2208,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1999,c_603,c_2184])).

tff(c_16,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_754,plain,(
    ! [C_95] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_95),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_746])).

tff(c_762,plain,(
    ! [C_104] : m1_subset_1(k4_xboole_0('#skF_2',C_104),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_754])).

tff(c_1387,plain,(
    ! [B_125] : m1_subset_1(k3_xboole_0('#skF_2',B_125),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_762])).

tff(c_1408,plain,(
    ! [A_70] : m1_subset_1(k3_xboole_0(A_70,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_1387])).

tff(c_36,plain,(
    ! [C_48,A_36,D_50,B_44] :
      ( v3_pre_topc(C_48,A_36)
      | k1_tops_1(A_36,C_48) != C_48
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0(B_44)))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(B_44)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_6082,plain,(
    ! [D_199,B_200] :
      ( ~ m1_subset_1(D_199,k1_zfmisc_1(u1_struct_0(B_200)))
      | ~ l1_pre_topc(B_200) ) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_6085,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1408,c_6082])).

tff(c_6115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6085])).

tff(c_6984,plain,(
    ! [C_210,A_211] :
      ( v3_pre_topc(C_210,A_211)
      | k1_tops_1(A_211,C_210) != C_210
      | ~ m1_subset_1(C_210,k1_zfmisc_1(u1_struct_0(A_211)))
      | ~ l1_pre_topc(A_211)
      | ~ v2_pre_topc(A_211) ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_7016,plain,
    ( v3_pre_topc('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_6984])).

tff(c_7040,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_2208,c_7016])).

tff(c_7042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_299,c_7040])).

tff(c_7043,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_7190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7043,c_128])).

tff(c_7191,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_7363,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7191,c_48])).

tff(c_7949,plain,(
    ! [A_260,B_261,C_262] :
      ( k7_subset_1(A_260,B_261,C_262) = k4_xboole_0(B_261,C_262)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(A_260)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_7958,plain,(
    ! [C_262] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_262) = k4_xboole_0('#skF_2',C_262) ),
    inference(resolution,[status(thm)],[c_42,c_7949])).

tff(c_9195,plain,(
    ! [A_298,B_299] :
      ( k7_subset_1(u1_struct_0(A_298),B_299,k2_tops_1(A_298,B_299)) = k1_tops_1(A_298,B_299)
      | ~ m1_subset_1(B_299,k1_zfmisc_1(u1_struct_0(A_298)))
      | ~ l1_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_9213,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_9195])).

tff(c_9231,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7958,c_9213])).

tff(c_8040,plain,(
    ! [C_265] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_265) = k4_xboole_0('#skF_2',C_265) ),
    inference(resolution,[status(thm)],[c_42,c_7949])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] :
      ( m1_subset_1(k7_subset_1(A_21,B_22,C_23),k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8046,plain,(
    ! [C_265] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_265),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8040,c_22])).

tff(c_8052,plain,(
    ! [C_265] : m1_subset_1(k4_xboole_0('#skF_2',C_265),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8046])).

tff(c_9249,plain,(
    m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_9231,c_8052])).

tff(c_38,plain,(
    ! [B_44,D_50,C_48,A_36] :
      ( k1_tops_1(B_44,D_50) = D_50
      | ~ v3_pre_topc(D_50,B_44)
      | ~ m1_subset_1(D_50,k1_zfmisc_1(u1_struct_0(B_44)))
      | ~ m1_subset_1(C_48,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(B_44)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_11316,plain,(
    ! [C_323,A_324] :
      ( ~ m1_subset_1(C_323,k1_zfmisc_1(u1_struct_0(A_324)))
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324) ) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_11319,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_9249,c_11316])).

tff(c_11349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_11319])).

tff(c_12566,plain,(
    ! [B_339,D_340] :
      ( k1_tops_1(B_339,D_340) = D_340
      | ~ v3_pre_topc(D_340,B_339)
      | ~ m1_subset_1(D_340,k1_zfmisc_1(u1_struct_0(B_339)))
      | ~ l1_pre_topc(B_339) ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_12595,plain,
    ( k1_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_12566])).

tff(c_12616,plain,(
    k1_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_7191,c_12595])).

tff(c_34,plain,(
    ! [A_33,B_35] :
      ( k7_subset_1(u1_struct_0(A_33),k2_pre_topc(A_33,B_35),k1_tops_1(A_33,B_35)) = k2_tops_1(A_33,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12635,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12616,c_34])).

tff(c_12639,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_12635])).

tff(c_12641,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7363,c_12639])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:42:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.39/2.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.48  
% 6.39/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.48  %$ v3_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.39/2.48  
% 6.39/2.48  %Foreground sorts:
% 6.39/2.48  
% 6.39/2.48  
% 6.39/2.48  %Background operators:
% 6.39/2.48  
% 6.39/2.48  
% 6.39/2.48  %Foreground operators:
% 6.39/2.48  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.39/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.39/2.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.39/2.48  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.39/2.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.39/2.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.39/2.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.39/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.39/2.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.39/2.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.39/2.48  tff('#skF_2', type, '#skF_2': $i).
% 6.39/2.48  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.39/2.48  tff('#skF_1', type, '#skF_1': $i).
% 6.39/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.39/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.39/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.39/2.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.39/2.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.39/2.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.39/2.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.39/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.39/2.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.39/2.48  
% 6.39/2.50  tff(f_112, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 6.39/2.50  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 6.39/2.50  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 6.39/2.50  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.39/2.50  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.39/2.50  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.39/2.50  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.39/2.50  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.39/2.50  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.39/2.50  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.39/2.50  tff(f_43, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.39/2.50  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 6.39/2.50  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 6.39/2.50  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 6.39/2.50  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 6.39/2.50  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.39/2.50  tff(c_299, plain, (~v3_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 6.39/2.50  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.39/2.50  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.39/2.50  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.39/2.50  tff(c_1297, plain, (![A_120, B_121]: (m1_subset_1(k2_pre_topc(A_120, B_121), k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_subset_1(B_121, k1_zfmisc_1(u1_struct_0(A_120))) | ~l1_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.39/2.50  tff(c_54, plain, (v3_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.39/2.50  tff(c_128, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 6.39/2.50  tff(c_746, plain, (![A_101, B_102, C_103]: (m1_subset_1(k7_subset_1(A_101, B_102, C_103), k1_zfmisc_1(A_101)) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.39/2.50  tff(c_757, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_128, c_746])).
% 6.39/2.50  tff(c_815, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_757])).
% 6.39/2.50  tff(c_1300, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1297, c_815])).
% 6.39/2.50  tff(c_1309, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1300])).
% 6.39/2.50  tff(c_1311, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_757])).
% 6.39/2.50  tff(c_24, plain, (![A_24, B_25, C_26]: (k7_subset_1(A_24, B_25, C_26)=k4_xboole_0(B_25, C_26) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.50  tff(c_1675, plain, (![C_133]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_133)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_133))), inference(resolution, [status(thm)], [c_1311, c_24])).
% 6.39/2.50  tff(c_1684, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1675, c_128])).
% 6.39/2.50  tff(c_12, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.39/2.50  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.39/2.50  tff(c_333, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.39/2.50  tff(c_354, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_333])).
% 6.39/2.50  tff(c_358, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_354])).
% 6.39/2.50  tff(c_20, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.39/2.50  tff(c_139, plain, (![A_67, B_68]: (k1_setfam_1(k2_tarski(A_67, B_68))=k3_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.39/2.50  tff(c_154, plain, (![B_69, A_70]: (k1_setfam_1(k2_tarski(B_69, A_70))=k3_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_20, c_139])).
% 6.39/2.50  tff(c_26, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.39/2.50  tff(c_160, plain, (![B_69, A_70]: (k3_xboole_0(B_69, A_70)=k3_xboole_0(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_154, c_26])).
% 6.39/2.50  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.39/2.50  tff(c_393, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.39/2.50  tff(c_425, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k3_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_393])).
% 6.39/2.50  tff(c_434, plain, (![A_11]: (k4_xboole_0(A_11, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_425])).
% 6.39/2.50  tff(c_18, plain, (![A_16, B_17, C_18]: (k4_xboole_0(k3_xboole_0(A_16, B_17), C_18)=k3_xboole_0(A_16, k4_xboole_0(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.39/2.50  tff(c_1424, plain, (![A_126, B_127, C_128]: (k5_xboole_0(k3_xboole_0(A_126, B_127), k3_xboole_0(C_128, B_127))=k3_xboole_0(k5_xboole_0(A_126, C_128), B_127))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.39/2.50  tff(c_1435, plain, (![A_126, B_127]: (k3_xboole_0(k5_xboole_0(A_126, k3_xboole_0(A_126, B_127)), B_127)=k4_xboole_0(k3_xboole_0(A_126, B_127), B_127))), inference(superposition, [status(thm), theory('equality')], [c_1424, c_4])).
% 6.39/2.50  tff(c_1500, plain, (![B_129, A_130]: (k3_xboole_0(B_129, k4_xboole_0(A_130, B_129))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_160, c_4, c_434, c_18, c_1435])).
% 6.39/2.50  tff(c_1533, plain, (![B_129, A_130]: (k4_xboole_0(B_129, k4_xboole_0(A_130, B_129))=k5_xboole_0(B_129, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1500, c_4])).
% 6.39/2.50  tff(c_1576, plain, (![B_129, A_130]: (k4_xboole_0(B_129, k4_xboole_0(A_130, B_129))=B_129)), inference(demodulation, [status(thm), theory('equality')], [c_358, c_1533])).
% 6.39/2.50  tff(c_1999, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1684, c_1576])).
% 6.39/2.50  tff(c_597, plain, (![A_93, B_94, C_95]: (k7_subset_1(A_93, B_94, C_95)=k4_xboole_0(B_94, C_95) | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.50  tff(c_603, plain, (![C_95]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_95)=k4_xboole_0('#skF_2', C_95))), inference(resolution, [status(thm)], [c_42, c_597])).
% 6.39/2.50  tff(c_2162, plain, (![A_143, B_144]: (k7_subset_1(u1_struct_0(A_143), B_144, k2_tops_1(A_143, B_144))=k1_tops_1(A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.39/2.50  tff(c_2184, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2162])).
% 6.39/2.50  tff(c_2208, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1999, c_603, c_2184])).
% 6.39/2.50  tff(c_16, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.39/2.50  tff(c_754, plain, (![C_95]: (m1_subset_1(k4_xboole_0('#skF_2', C_95), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_603, c_746])).
% 6.39/2.50  tff(c_762, plain, (![C_104]: (m1_subset_1(k4_xboole_0('#skF_2', C_104), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_754])).
% 6.39/2.50  tff(c_1387, plain, (![B_125]: (m1_subset_1(k3_xboole_0('#skF_2', B_125), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_16, c_762])).
% 6.39/2.50  tff(c_1408, plain, (![A_70]: (m1_subset_1(k3_xboole_0(A_70, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_160, c_1387])).
% 6.39/2.50  tff(c_36, plain, (![C_48, A_36, D_50, B_44]: (v3_pre_topc(C_48, A_36) | k1_tops_1(A_36, C_48)!=C_48 | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0(B_44))) | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(B_44) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.39/2.50  tff(c_6082, plain, (![D_199, B_200]: (~m1_subset_1(D_199, k1_zfmisc_1(u1_struct_0(B_200))) | ~l1_pre_topc(B_200))), inference(splitLeft, [status(thm)], [c_36])).
% 6.39/2.50  tff(c_6085, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1408, c_6082])).
% 6.39/2.50  tff(c_6115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_6085])).
% 6.39/2.50  tff(c_6984, plain, (![C_210, A_211]: (v3_pre_topc(C_210, A_211) | k1_tops_1(A_211, C_210)!=C_210 | ~m1_subset_1(C_210, k1_zfmisc_1(u1_struct_0(A_211))) | ~l1_pre_topc(A_211) | ~v2_pre_topc(A_211))), inference(splitRight, [status(thm)], [c_36])).
% 6.39/2.50  tff(c_7016, plain, (v3_pre_topc('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_6984])).
% 6.39/2.50  tff(c_7040, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_2208, c_7016])).
% 6.39/2.50  tff(c_7042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_299, c_7040])).
% 6.39/2.50  tff(c_7043, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 6.39/2.50  tff(c_7190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7043, c_128])).
% 6.39/2.50  tff(c_7191, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 6.39/2.50  tff(c_7363, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7191, c_48])).
% 6.39/2.50  tff(c_7949, plain, (![A_260, B_261, C_262]: (k7_subset_1(A_260, B_261, C_262)=k4_xboole_0(B_261, C_262) | ~m1_subset_1(B_261, k1_zfmisc_1(A_260)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.39/2.50  tff(c_7958, plain, (![C_262]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_262)=k4_xboole_0('#skF_2', C_262))), inference(resolution, [status(thm)], [c_42, c_7949])).
% 6.39/2.50  tff(c_9195, plain, (![A_298, B_299]: (k7_subset_1(u1_struct_0(A_298), B_299, k2_tops_1(A_298, B_299))=k1_tops_1(A_298, B_299) | ~m1_subset_1(B_299, k1_zfmisc_1(u1_struct_0(A_298))) | ~l1_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.39/2.50  tff(c_9213, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_9195])).
% 6.39/2.50  tff(c_9231, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7958, c_9213])).
% 6.39/2.50  tff(c_8040, plain, (![C_265]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_265)=k4_xboole_0('#skF_2', C_265))), inference(resolution, [status(thm)], [c_42, c_7949])).
% 6.39/2.50  tff(c_22, plain, (![A_21, B_22, C_23]: (m1_subset_1(k7_subset_1(A_21, B_22, C_23), k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.39/2.50  tff(c_8046, plain, (![C_265]: (m1_subset_1(k4_xboole_0('#skF_2', C_265), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_8040, c_22])).
% 6.39/2.50  tff(c_8052, plain, (![C_265]: (m1_subset_1(k4_xboole_0('#skF_2', C_265), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8046])).
% 6.39/2.50  tff(c_9249, plain, (m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_9231, c_8052])).
% 6.39/2.50  tff(c_38, plain, (![B_44, D_50, C_48, A_36]: (k1_tops_1(B_44, D_50)=D_50 | ~v3_pre_topc(D_50, B_44) | ~m1_subset_1(D_50, k1_zfmisc_1(u1_struct_0(B_44))) | ~m1_subset_1(C_48, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(B_44) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.39/2.50  tff(c_11316, plain, (![C_323, A_324]: (~m1_subset_1(C_323, k1_zfmisc_1(u1_struct_0(A_324))) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324))), inference(splitLeft, [status(thm)], [c_38])).
% 6.39/2.50  tff(c_11319, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_9249, c_11316])).
% 6.39/2.50  tff(c_11349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_11319])).
% 6.39/2.50  tff(c_12566, plain, (![B_339, D_340]: (k1_tops_1(B_339, D_340)=D_340 | ~v3_pre_topc(D_340, B_339) | ~m1_subset_1(D_340, k1_zfmisc_1(u1_struct_0(B_339))) | ~l1_pre_topc(B_339))), inference(splitRight, [status(thm)], [c_38])).
% 6.39/2.50  tff(c_12595, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2' | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_12566])).
% 6.39/2.50  tff(c_12616, plain, (k1_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_7191, c_12595])).
% 6.39/2.50  tff(c_34, plain, (![A_33, B_35]: (k7_subset_1(u1_struct_0(A_33), k2_pre_topc(A_33, B_35), k1_tops_1(A_33, B_35))=k2_tops_1(A_33, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.39/2.50  tff(c_12635, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12616, c_34])).
% 6.39/2.50  tff(c_12639, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_12635])).
% 6.39/2.50  tff(c_12641, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7363, c_12639])).
% 6.39/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.39/2.50  
% 6.39/2.50  Inference rules
% 6.39/2.50  ----------------------
% 6.39/2.50  #Ref     : 0
% 6.39/2.50  #Sup     : 3127
% 6.39/2.50  #Fact    : 0
% 6.39/2.50  #Define  : 0
% 6.39/2.50  #Split   : 6
% 6.39/2.50  #Chain   : 0
% 6.39/2.50  #Close   : 0
% 6.39/2.50  
% 6.39/2.50  Ordering : KBO
% 6.39/2.50  
% 6.39/2.50  Simplification rules
% 6.39/2.50  ----------------------
% 6.39/2.50  #Subsume      : 10
% 6.39/2.50  #Demod        : 3651
% 6.39/2.50  #Tautology    : 2344
% 6.39/2.50  #SimpNegUnit  : 3
% 6.39/2.50  #BackRed      : 12
% 6.39/2.50  
% 6.39/2.50  #Partial instantiations: 0
% 6.39/2.50  #Strategies tried      : 1
% 6.39/2.50  
% 6.39/2.50  Timing (in seconds)
% 6.39/2.50  ----------------------
% 6.39/2.50  Preprocessing        : 0.35
% 6.39/2.50  Parsing              : 0.20
% 6.39/2.50  CNF conversion       : 0.02
% 6.39/2.50  Main loop            : 1.36
% 6.39/2.50  Inferencing          : 0.37
% 6.39/2.50  Reduction            : 0.69
% 6.39/2.50  Demodulation         : 0.58
% 6.39/2.50  BG Simplification    : 0.04
% 6.39/2.50  Subsumption          : 0.18
% 6.39/2.50  Abstraction          : 0.07
% 6.39/2.50  MUC search           : 0.00
% 6.39/2.50  Cooper               : 0.00
% 6.39/2.50  Total                : 1.76
% 6.39/2.50  Index Insertion      : 0.00
% 6.39/2.50  Index Deletion       : 0.00
% 6.39/2.50  Index Matching       : 0.00
% 6.39/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
