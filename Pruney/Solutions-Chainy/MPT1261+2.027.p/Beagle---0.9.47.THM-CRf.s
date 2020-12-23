%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:15 EST 2020

% Result     : Theorem 7.09s
% Output     : CNFRefutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 228 expanded)
%              Number of leaves         :   43 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  150 ( 381 expanded)
%              Number of equality atoms :   70 ( 143 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_135,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_69,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_8945,plain,(
    ! [A_395,B_396,C_397] :
      ( k7_subset_1(A_395,B_396,C_397) = k4_xboole_0(B_396,C_397)
      | ~ m1_subset_1(B_396,k1_zfmisc_1(A_395)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8965,plain,(
    ! [C_397] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_397) = k4_xboole_0('#skF_2',C_397) ),
    inference(resolution,[status(thm)],[c_52,c_8945])).

tff(c_58,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_129,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1611,plain,(
    ! [B_169,A_170] :
      ( v4_pre_topc(B_169,A_170)
      | k2_pre_topc(A_170,B_169) != B_169
      | ~ v2_pre_topc(A_170)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_170)))
      | ~ l1_pre_topc(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1640,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1611])).

tff(c_1656,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_1640])).

tff(c_1657,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_1656])).

tff(c_704,plain,(
    ! [A_125,B_126,C_127] :
      ( k7_subset_1(A_125,B_126,C_127) = k4_xboole_0(B_126,C_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_822,plain,(
    ! [C_138] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_138) = k4_xboole_0('#skF_2',C_138) ),
    inference(resolution,[status(thm)],[c_52,c_704])).

tff(c_64,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_203,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_64])).

tff(c_828,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_203])).

tff(c_28,plain,(
    ! [A_27,B_28] : k6_subset_1(A_27,B_28) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_20,B_21] : m1_subset_1(k6_subset_1(A_20,B_21),k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_65,plain,(
    ! [A_20,B_21] : m1_subset_1(k4_xboole_0(A_20,B_21),k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22])).

tff(c_130,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,B_64)
      | ~ m1_subset_1(A_63,k1_zfmisc_1(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_140,plain,(
    ! [A_20,B_21] : r1_tarski(k4_xboole_0(A_20,B_21),A_20) ),
    inference(resolution,[status(thm)],[c_65,c_130])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_552,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(A_116,B_117) = k3_subset_1(A_116,B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_564,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_subset_1(A_20,k4_xboole_0(A_20,B_21)) ),
    inference(resolution,[status(thm)],[c_65,c_552])).

tff(c_575,plain,(
    ! [A_20,B_21] : k3_subset_1(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_564])).

tff(c_36,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(A_34,k1_zfmisc_1(B_35))
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_442,plain,(
    ! [A_101,B_102] :
      ( k3_subset_1(A_101,k3_subset_1(A_101,B_102)) = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1919,plain,(
    ! [B_181,A_182] :
      ( k3_subset_1(B_181,k3_subset_1(B_181,A_182)) = A_182
      | ~ r1_tarski(A_182,B_181) ) ),
    inference(resolution,[status(thm)],[c_36,c_442])).

tff(c_1941,plain,(
    ! [A_20,B_21] :
      ( k3_subset_1(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21)
      | ~ r1_tarski(k4_xboole_0(A_20,B_21),A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_575,c_1919])).

tff(c_1965,plain,(
    ! [A_20,B_21] : k3_subset_1(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1941])).

tff(c_345,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k4_xboole_0(A_87,B_88)) = k3_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_354,plain,(
    ! [A_87,B_88] : r1_tarski(k3_xboole_0(A_87,B_88),A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_140])).

tff(c_2064,plain,(
    ! [B_190,A_191] :
      ( k4_xboole_0(B_190,A_191) = k3_subset_1(B_190,A_191)
      | ~ r1_tarski(A_191,B_190) ) ),
    inference(resolution,[status(thm)],[c_36,c_552])).

tff(c_2133,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k3_subset_1(A_87,k3_xboole_0(A_87,B_88)) ),
    inference(resolution,[status(thm)],[c_354,c_2064])).

tff(c_2173,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_2133])).

tff(c_360,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,k4_xboole_0(A_10,B_11)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_345])).

tff(c_2683,plain,(
    ! [A_201,B_202] : k3_xboole_0(A_201,k4_xboole_0(A_201,B_202)) = k4_xboole_0(A_201,B_202) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2173,c_360])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k3_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2827,plain,(
    ! [A_203,B_204] : k2_xboole_0(A_203,k4_xboole_0(A_203,B_204)) = A_203 ),
    inference(superposition,[status(thm),theory(equality)],[c_2683,c_6])).

tff(c_2858,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_2827])).

tff(c_1853,plain,(
    ! [A_178,B_179] :
      ( k4_subset_1(u1_struct_0(A_178),B_179,k2_tops_1(A_178,B_179)) = k2_pre_topc(A_178,B_179)
      | ~ m1_subset_1(B_179,k1_zfmisc_1(u1_struct_0(A_178)))
      | ~ l1_pre_topc(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1874,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_1853])).

tff(c_1889,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1874])).

tff(c_459,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_442])).

tff(c_12,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_165,plain,(
    ! [A_72,B_73] : k1_setfam_1(k2_tarski(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_242,plain,(
    ! [A_78,B_79] : k1_setfam_1(k2_tarski(A_78,B_79)) = k3_xboole_0(B_79,A_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_165])).

tff(c_32,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_248,plain,(
    ! [B_79,A_78] : k3_xboole_0(B_79,A_78) = k3_xboole_0(A_78,B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_32])).

tff(c_576,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_552])).

tff(c_837,plain,(
    ! [A_139,B_140] : k3_subset_1(A_139,k4_xboole_0(A_139,B_140)) = k3_xboole_0(A_139,B_140) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_564])).

tff(c_849,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_837])).

tff(c_858,plain,(
    k3_xboole_0('#skF_2',u1_struct_0('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_248,c_849])).

tff(c_304,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(A_82,k2_xboole_0(C_83,B_84))
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_470,plain,(
    ! [A_104,A_105,B_106] :
      ( r1_tarski(A_104,A_105)
      | ~ r1_tarski(A_104,k3_xboole_0(A_105,B_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_304])).

tff(c_498,plain,(
    ! [A_107,B_108,B_109] : r1_tarski(k4_xboole_0(k3_xboole_0(A_107,B_108),B_109),A_107) ),
    inference(resolution,[status(thm)],[c_140,c_470])).

tff(c_512,plain,(
    ! [A_78,B_79,B_109] : r1_tarski(k4_xboole_0(k3_xboole_0(A_78,B_79),B_109),B_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_498])).

tff(c_967,plain,(
    ! [B_109] : r1_tarski(k4_xboole_0('#skF_2',B_109),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_512])).

tff(c_1181,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_967])).

tff(c_1426,plain,(
    ! [A_161,B_162,C_163] :
      ( k4_subset_1(A_161,B_162,C_163) = k2_xboole_0(B_162,C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(A_161))
      | ~ m1_subset_1(B_162,k1_zfmisc_1(A_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8070,plain,(
    ! [B_330,B_331,A_332] :
      ( k4_subset_1(B_330,B_331,A_332) = k2_xboole_0(B_331,A_332)
      | ~ m1_subset_1(B_331,k1_zfmisc_1(B_330))
      | ~ r1_tarski(A_332,B_330) ) ),
    inference(resolution,[status(thm)],[c_36,c_1426])).

tff(c_8168,plain,(
    ! [A_335] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_335) = k2_xboole_0('#skF_2',A_335)
      | ~ r1_tarski(A_335,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_8070])).

tff(c_8290,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1181,c_8168])).

tff(c_8392,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2858,c_1889,c_8290])).

tff(c_8394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1657,c_8392])).

tff(c_8395,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_9020,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8965,c_8395])).

tff(c_8396,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_9461,plain,(
    ! [A_424,B_425] :
      ( k2_pre_topc(A_424,B_425) = B_425
      | ~ v4_pre_topc(B_425,A_424)
      | ~ m1_subset_1(B_425,k1_zfmisc_1(u1_struct_0(A_424)))
      | ~ l1_pre_topc(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_9490,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_9461])).

tff(c_9506,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_8396,c_9490])).

tff(c_10325,plain,(
    ! [A_457,B_458] :
      ( k7_subset_1(u1_struct_0(A_457),k2_pre_topc(A_457,B_458),k1_tops_1(A_457,B_458)) = k2_tops_1(A_457,B_458)
      | ~ m1_subset_1(B_458,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ l1_pre_topc(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10334,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9506,c_10325])).

tff(c_10338,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_8965,c_10334])).

tff(c_10340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9020,c_10338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:32:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.09/2.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/2.68  
% 7.09/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/2.68  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 7.09/2.68  
% 7.09/2.68  %Foreground sorts:
% 7.09/2.68  
% 7.09/2.68  
% 7.09/2.68  %Background operators:
% 7.09/2.68  
% 7.09/2.68  
% 7.09/2.68  %Foreground operators:
% 7.09/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.09/2.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.09/2.68  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.09/2.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.09/2.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.09/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.09/2.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.09/2.68  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.09/2.68  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.09/2.68  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.09/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.09/2.68  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.09/2.68  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 7.09/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.09/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.09/2.68  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.09/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.09/2.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.09/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.09/2.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.09/2.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.09/2.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.09/2.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.09/2.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.09/2.68  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.09/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.09/2.68  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.09/2.68  
% 7.09/2.70  tff(f_135, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 7.09/2.70  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.09/2.70  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.09/2.70  tff(f_63, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 7.09/2.70  tff(f_51, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 7.09/2.70  tff(f_73, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.09/2.70  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.09/2.70  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.09/2.70  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.09/2.70  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 7.09/2.70  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 7.09/2.70  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.09/2.70  tff(f_69, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.09/2.70  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.09/2.70  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.09/2.70  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 7.09/2.70  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.09/2.70  tff(c_8945, plain, (![A_395, B_396, C_397]: (k7_subset_1(A_395, B_396, C_397)=k4_xboole_0(B_396, C_397) | ~m1_subset_1(B_396, k1_zfmisc_1(A_395)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.09/2.70  tff(c_8965, plain, (![C_397]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_397)=k4_xboole_0('#skF_2', C_397))), inference(resolution, [status(thm)], [c_52, c_8945])).
% 7.09/2.70  tff(c_58, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.09/2.70  tff(c_129, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_58])).
% 7.09/2.70  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.09/2.70  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.09/2.70  tff(c_1611, plain, (![B_169, A_170]: (v4_pre_topc(B_169, A_170) | k2_pre_topc(A_170, B_169)!=B_169 | ~v2_pre_topc(A_170) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_170))) | ~l1_pre_topc(A_170))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.09/2.70  tff(c_1640, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1611])).
% 7.09/2.70  tff(c_1656, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_1640])).
% 7.09/2.70  tff(c_1657, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_129, c_1656])).
% 7.09/2.70  tff(c_704, plain, (![A_125, B_126, C_127]: (k7_subset_1(A_125, B_126, C_127)=k4_xboole_0(B_126, C_127) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.09/2.70  tff(c_822, plain, (![C_138]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_138)=k4_xboole_0('#skF_2', C_138))), inference(resolution, [status(thm)], [c_52, c_704])).
% 7.09/2.70  tff(c_64, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.09/2.70  tff(c_203, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_129, c_64])).
% 7.09/2.70  tff(c_828, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_822, c_203])).
% 7.09/2.70  tff(c_28, plain, (![A_27, B_28]: (k6_subset_1(A_27, B_28)=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.09/2.70  tff(c_22, plain, (![A_20, B_21]: (m1_subset_1(k6_subset_1(A_20, B_21), k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.09/2.70  tff(c_65, plain, (![A_20, B_21]: (m1_subset_1(k4_xboole_0(A_20, B_21), k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22])).
% 7.09/2.70  tff(c_130, plain, (![A_63, B_64]: (r1_tarski(A_63, B_64) | ~m1_subset_1(A_63, k1_zfmisc_1(B_64)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.09/2.70  tff(c_140, plain, (![A_20, B_21]: (r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(resolution, [status(thm)], [c_65, c_130])).
% 7.09/2.70  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.09/2.70  tff(c_552, plain, (![A_116, B_117]: (k4_xboole_0(A_116, B_117)=k3_subset_1(A_116, B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.09/2.70  tff(c_564, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_subset_1(A_20, k4_xboole_0(A_20, B_21)))), inference(resolution, [status(thm)], [c_65, c_552])).
% 7.09/2.70  tff(c_575, plain, (![A_20, B_21]: (k3_subset_1(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_564])).
% 7.09/2.70  tff(c_36, plain, (![A_34, B_35]: (m1_subset_1(A_34, k1_zfmisc_1(B_35)) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.09/2.70  tff(c_442, plain, (![A_101, B_102]: (k3_subset_1(A_101, k3_subset_1(A_101, B_102))=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.09/2.70  tff(c_1919, plain, (![B_181, A_182]: (k3_subset_1(B_181, k3_subset_1(B_181, A_182))=A_182 | ~r1_tarski(A_182, B_181))), inference(resolution, [status(thm)], [c_36, c_442])).
% 7.09/2.70  tff(c_1941, plain, (![A_20, B_21]: (k3_subset_1(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21) | ~r1_tarski(k4_xboole_0(A_20, B_21), A_20))), inference(superposition, [status(thm), theory('equality')], [c_575, c_1919])).
% 7.09/2.70  tff(c_1965, plain, (![A_20, B_21]: (k3_subset_1(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1941])).
% 7.09/2.70  tff(c_345, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k4_xboole_0(A_87, B_88))=k3_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.09/2.70  tff(c_354, plain, (![A_87, B_88]: (r1_tarski(k3_xboole_0(A_87, B_88), A_87))), inference(superposition, [status(thm), theory('equality')], [c_345, c_140])).
% 7.09/2.70  tff(c_2064, plain, (![B_190, A_191]: (k4_xboole_0(B_190, A_191)=k3_subset_1(B_190, A_191) | ~r1_tarski(A_191, B_190))), inference(resolution, [status(thm)], [c_36, c_552])).
% 7.09/2.70  tff(c_2133, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k3_subset_1(A_87, k3_xboole_0(A_87, B_88)))), inference(resolution, [status(thm)], [c_354, c_2064])).
% 7.09/2.70  tff(c_2173, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_2133])).
% 7.09/2.70  tff(c_360, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k3_xboole_0(A_10, k4_xboole_0(A_10, B_11)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_345])).
% 7.09/2.70  tff(c_2683, plain, (![A_201, B_202]: (k3_xboole_0(A_201, k4_xboole_0(A_201, B_202))=k4_xboole_0(A_201, B_202))), inference(demodulation, [status(thm), theory('equality')], [c_2173, c_360])).
% 7.09/2.70  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k3_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.09/2.70  tff(c_2827, plain, (![A_203, B_204]: (k2_xboole_0(A_203, k4_xboole_0(A_203, B_204))=A_203)), inference(superposition, [status(thm), theory('equality')], [c_2683, c_6])).
% 7.09/2.70  tff(c_2858, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_828, c_2827])).
% 7.09/2.70  tff(c_1853, plain, (![A_178, B_179]: (k4_subset_1(u1_struct_0(A_178), B_179, k2_tops_1(A_178, B_179))=k2_pre_topc(A_178, B_179) | ~m1_subset_1(B_179, k1_zfmisc_1(u1_struct_0(A_178))) | ~l1_pre_topc(A_178))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.09/2.70  tff(c_1874, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_1853])).
% 7.09/2.70  tff(c_1889, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1874])).
% 7.09/2.70  tff(c_459, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_52, c_442])).
% 7.09/2.70  tff(c_12, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.09/2.70  tff(c_165, plain, (![A_72, B_73]: (k1_setfam_1(k2_tarski(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.09/2.70  tff(c_242, plain, (![A_78, B_79]: (k1_setfam_1(k2_tarski(A_78, B_79))=k3_xboole_0(B_79, A_78))), inference(superposition, [status(thm), theory('equality')], [c_12, c_165])).
% 7.09/2.70  tff(c_32, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.09/2.70  tff(c_248, plain, (![B_79, A_78]: (k3_xboole_0(B_79, A_78)=k3_xboole_0(A_78, B_79))), inference(superposition, [status(thm), theory('equality')], [c_242, c_32])).
% 7.09/2.70  tff(c_576, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_52, c_552])).
% 7.09/2.70  tff(c_837, plain, (![A_139, B_140]: (k3_subset_1(A_139, k4_xboole_0(A_139, B_140))=k3_xboole_0(A_139, B_140))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_564])).
% 7.09/2.70  tff(c_849, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_576, c_837])).
% 7.09/2.70  tff(c_858, plain, (k3_xboole_0('#skF_2', u1_struct_0('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_459, c_248, c_849])).
% 7.09/2.70  tff(c_304, plain, (![A_82, C_83, B_84]: (r1_tarski(A_82, k2_xboole_0(C_83, B_84)) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.09/2.70  tff(c_470, plain, (![A_104, A_105, B_106]: (r1_tarski(A_104, A_105) | ~r1_tarski(A_104, k3_xboole_0(A_105, B_106)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_304])).
% 7.09/2.70  tff(c_498, plain, (![A_107, B_108, B_109]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_107, B_108), B_109), A_107))), inference(resolution, [status(thm)], [c_140, c_470])).
% 7.09/2.70  tff(c_512, plain, (![A_78, B_79, B_109]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_78, B_79), B_109), B_79))), inference(superposition, [status(thm), theory('equality')], [c_248, c_498])).
% 7.09/2.70  tff(c_967, plain, (![B_109]: (r1_tarski(k4_xboole_0('#skF_2', B_109), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_858, c_512])).
% 7.09/2.70  tff(c_1181, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_828, c_967])).
% 7.09/2.70  tff(c_1426, plain, (![A_161, B_162, C_163]: (k4_subset_1(A_161, B_162, C_163)=k2_xboole_0(B_162, C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(A_161)) | ~m1_subset_1(B_162, k1_zfmisc_1(A_161)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.09/2.70  tff(c_8070, plain, (![B_330, B_331, A_332]: (k4_subset_1(B_330, B_331, A_332)=k2_xboole_0(B_331, A_332) | ~m1_subset_1(B_331, k1_zfmisc_1(B_330)) | ~r1_tarski(A_332, B_330))), inference(resolution, [status(thm)], [c_36, c_1426])).
% 7.09/2.70  tff(c_8168, plain, (![A_335]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_335)=k2_xboole_0('#skF_2', A_335) | ~r1_tarski(A_335, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_8070])).
% 7.09/2.70  tff(c_8290, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1181, c_8168])).
% 7.09/2.70  tff(c_8392, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2858, c_1889, c_8290])).
% 7.09/2.70  tff(c_8394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1657, c_8392])).
% 7.09/2.70  tff(c_8395, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 7.09/2.70  tff(c_9020, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8965, c_8395])).
% 7.09/2.70  tff(c_8396, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 7.09/2.70  tff(c_9461, plain, (![A_424, B_425]: (k2_pre_topc(A_424, B_425)=B_425 | ~v4_pre_topc(B_425, A_424) | ~m1_subset_1(B_425, k1_zfmisc_1(u1_struct_0(A_424))) | ~l1_pre_topc(A_424))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.09/2.70  tff(c_9490, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_52, c_9461])).
% 7.09/2.70  tff(c_9506, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_8396, c_9490])).
% 7.09/2.70  tff(c_10325, plain, (![A_457, B_458]: (k7_subset_1(u1_struct_0(A_457), k2_pre_topc(A_457, B_458), k1_tops_1(A_457, B_458))=k2_tops_1(A_457, B_458) | ~m1_subset_1(B_458, k1_zfmisc_1(u1_struct_0(A_457))) | ~l1_pre_topc(A_457))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.09/2.70  tff(c_10334, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9506, c_10325])).
% 7.09/2.70  tff(c_10338, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_8965, c_10334])).
% 7.09/2.70  tff(c_10340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9020, c_10338])).
% 7.09/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/2.70  
% 7.09/2.70  Inference rules
% 7.09/2.70  ----------------------
% 7.09/2.70  #Ref     : 0
% 7.09/2.70  #Sup     : 2445
% 7.09/2.70  #Fact    : 0
% 7.09/2.70  #Define  : 0
% 7.09/2.70  #Split   : 1
% 7.09/2.70  #Chain   : 0
% 7.09/2.70  #Close   : 0
% 7.09/2.70  
% 7.09/2.70  Ordering : KBO
% 7.09/2.70  
% 7.09/2.70  Simplification rules
% 7.09/2.70  ----------------------
% 7.09/2.70  #Subsume      : 68
% 7.09/2.70  #Demod        : 1552
% 7.09/2.70  #Tautology    : 1284
% 7.09/2.70  #SimpNegUnit  : 5
% 7.09/2.70  #BackRed      : 2
% 7.09/2.70  
% 7.09/2.70  #Partial instantiations: 0
% 7.09/2.70  #Strategies tried      : 1
% 7.09/2.70  
% 7.09/2.70  Timing (in seconds)
% 7.09/2.70  ----------------------
% 7.09/2.70  Preprocessing        : 0.33
% 7.09/2.70  Parsing              : 0.17
% 7.09/2.70  CNF conversion       : 0.02
% 7.09/2.70  Main loop            : 1.60
% 7.09/2.70  Inferencing          : 0.42
% 7.09/2.70  Reduction            : 0.71
% 7.09/2.70  Demodulation         : 0.58
% 7.09/2.70  BG Simplification    : 0.05
% 7.09/2.70  Subsumption          : 0.30
% 7.09/2.70  Abstraction          : 0.07
% 7.09/2.70  MUC search           : 0.00
% 7.09/2.70  Cooper               : 0.00
% 7.09/2.70  Total                : 1.97
% 7.09/2.70  Index Insertion      : 0.00
% 7.09/2.70  Index Deletion       : 0.00
% 7.09/2.70  Index Matching       : 0.00
% 7.09/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
