%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:23 EST 2020

% Result     : Theorem 5.27s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 183 expanded)
%              Number of leaves         :   36 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 311 expanded)
%              Number of equality atoms :   60 ( 139 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v4_pre_topc(B,A)
             => k2_pre_topc(A,B) = B )
            & ( ( v2_pre_topc(A)
                & k2_pre_topc(A,B) = B )
             => v4_pre_topc(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3748,plain,(
    ! [A_177,B_178,C_179] :
      ( k7_subset_1(A_177,B_178,C_179) = k4_xboole_0(B_178,C_179)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(A_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3751,plain,(
    ! [C_179] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_179) = k4_xboole_0('#skF_2',C_179) ),
    inference(resolution,[status(thm)],[c_32,c_3748])).

tff(c_44,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_179,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_281,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1398,plain,(
    ! [B_103,A_104] :
      ( v4_pre_topc(B_103,A_104)
      | k2_pre_topc(A_104,B_103) != B_103
      | ~ v2_pre_topc(A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1404,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1398])).

tff(c_1408,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36,c_1404])).

tff(c_1409,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_1408])).

tff(c_1583,plain,(
    ! [A_110,B_111] :
      ( k4_subset_1(u1_struct_0(A_110),B_111,k2_tops_1(A_110,B_111)) = k2_pre_topc(A_110,B_111)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_110)))
      | ~ l1_pre_topc(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1587,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1583])).

tff(c_1591,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1587])).

tff(c_419,plain,(
    ! [A_66,B_67,C_68] :
      ( k7_subset_1(A_66,B_67,C_68) = k4_xboole_0(B_67,C_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_423,plain,(
    ! [C_69] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_69) = k4_xboole_0('#skF_2',C_69) ),
    inference(resolution,[status(thm)],[c_32,c_419])).

tff(c_429,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_179])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_102,plain,(
    ! [A_41,B_42] : k3_tarski(k2_tarski(A_41,B_42)) = k2_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_208,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(B_50,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_102])).

tff(c_14,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_214,plain,(
    ! [B_50,A_49] : k2_xboole_0(B_50,A_49) = k2_xboole_0(A_49,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_14])).

tff(c_297,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(B_58,A_57)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_306,plain,(
    ! [A_7,B_8] : k2_xboole_0(k3_xboole_0(A_7,B_8),k4_xboole_0(A_7,B_8)) = k2_xboole_0(k3_xboole_0(A_7,B_8),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_297])).

tff(c_363,plain,(
    ! [A_62,B_63] : k2_xboole_0(k3_xboole_0(A_62,B_63),k4_xboole_0(A_62,B_63)) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_214,c_306])).

tff(c_620,plain,(
    ! [A_78,B_79] : k2_xboole_0(k3_xboole_0(A_78,k3_xboole_0(A_78,B_79)),k4_xboole_0(A_78,B_79)) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_363])).

tff(c_635,plain,(
    ! [A_78,B_79] : k2_xboole_0(k4_xboole_0(A_78,B_79),k3_xboole_0(A_78,k3_xboole_0(A_78,B_79))) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_214])).

tff(c_889,plain,(
    ! [A_86,B_87] : k2_xboole_0(k4_xboole_0(A_86,B_87),k3_xboole_0(A_86,k3_xboole_0(A_86,B_87))) = A_86 ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_214])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_904,plain,(
    ! [A_86,B_87] : k2_xboole_0(k4_xboole_0(A_86,B_87),k3_xboole_0(A_86,k3_xboole_0(A_86,B_87))) = k2_xboole_0(k4_xboole_0(A_86,B_87),A_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_10])).

tff(c_960,plain,(
    ! [A_88,B_89] : k2_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_635,c_214,c_904])).

tff(c_985,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_960])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k2_tops_1(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1029,plain,(
    ! [A_90,B_91,C_92] :
      ( k4_subset_1(A_90,B_91,C_92) = k2_xboole_0(B_91,C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3313,plain,(
    ! [A_143,B_144,B_145] :
      ( k4_subset_1(u1_struct_0(A_143),B_144,k2_tops_1(A_143,B_145)) = k2_xboole_0(B_144,k2_tops_1(A_143,B_145))
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(resolution,[status(thm)],[c_26,c_1029])).

tff(c_3317,plain,(
    ! [B_145] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_145)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_145))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_3313])).

tff(c_3325,plain,(
    ! [B_146] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_146)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_146))
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3317])).

tff(c_3332,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_3325])).

tff(c_3337,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_985,c_3332])).

tff(c_3339,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1409,c_3337])).

tff(c_3340,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_3509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_3340])).

tff(c_3510,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_3613,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3510,c_38])).

tff(c_3752,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3751,c_3613])).

tff(c_3902,plain,(
    ! [A_189,B_190] :
      ( k2_pre_topc(A_189,B_190) = B_190
      | ~ v4_pre_topc(B_190,A_189)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(u1_struct_0(A_189)))
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3908,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3902])).

tff(c_3912,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_3510,c_3908])).

tff(c_4500,plain,(
    ! [A_220,B_221] :
      ( k7_subset_1(u1_struct_0(A_220),k2_pre_topc(A_220,B_221),k1_tops_1(A_220,B_221)) = k2_tops_1(A_220,B_221)
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0(A_220)))
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4509,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3912,c_4500])).

tff(c_4513,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_3751,c_4509])).

tff(c_4515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3752,c_4513])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.27/2.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/2.06  
% 5.27/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/2.07  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.27/2.07  
% 5.27/2.07  %Foreground sorts:
% 5.27/2.07  
% 5.27/2.07  
% 5.27/2.07  %Background operators:
% 5.27/2.07  
% 5.27/2.07  
% 5.27/2.07  %Foreground operators:
% 5.27/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.27/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.27/2.07  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.27/2.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.27/2.07  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.27/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.27/2.07  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.27/2.07  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.27/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.27/2.07  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.27/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.27/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.27/2.07  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.27/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.27/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.27/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.27/2.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.27/2.07  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.27/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.27/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.27/2.07  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.27/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.27/2.07  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.27/2.07  
% 5.27/2.08  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.27/2.08  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.27/2.08  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.27/2.08  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.27/2.08  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 5.27/2.08  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.27/2.08  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.27/2.08  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.27/2.08  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.27/2.08  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_xboole_1)).
% 5.27/2.08  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.27/2.08  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.27/2.08  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.27/2.08  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.27/2.08  tff(c_3748, plain, (![A_177, B_178, C_179]: (k7_subset_1(A_177, B_178, C_179)=k4_xboole_0(B_178, C_179) | ~m1_subset_1(B_178, k1_zfmisc_1(A_177)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.27/2.08  tff(c_3751, plain, (![C_179]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_179)=k4_xboole_0('#skF_2', C_179))), inference(resolution, [status(thm)], [c_32, c_3748])).
% 5.27/2.08  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.27/2.08  tff(c_179, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_44])).
% 5.27/2.08  tff(c_38, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.27/2.08  tff(c_281, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 5.27/2.08  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.27/2.08  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.27/2.08  tff(c_1398, plain, (![B_103, A_104]: (v4_pre_topc(B_103, A_104) | k2_pre_topc(A_104, B_103)!=B_103 | ~v2_pre_topc(A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.27/2.08  tff(c_1404, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1398])).
% 5.27/2.08  tff(c_1408, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36, c_1404])).
% 5.27/2.08  tff(c_1409, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_281, c_1408])).
% 5.27/2.08  tff(c_1583, plain, (![A_110, B_111]: (k4_subset_1(u1_struct_0(A_110), B_111, k2_tops_1(A_110, B_111))=k2_pre_topc(A_110, B_111) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_110))) | ~l1_pre_topc(A_110))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.27/2.08  tff(c_1587, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1583])).
% 5.27/2.08  tff(c_1591, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1587])).
% 5.27/2.08  tff(c_419, plain, (![A_66, B_67, C_68]: (k7_subset_1(A_66, B_67, C_68)=k4_xboole_0(B_67, C_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.27/2.08  tff(c_423, plain, (![C_69]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_69)=k4_xboole_0('#skF_2', C_69))), inference(resolution, [status(thm)], [c_32, c_419])).
% 5.27/2.08  tff(c_429, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_423, c_179])).
% 5.27/2.08  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.27/2.08  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.27/2.08  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.27/2.08  tff(c_102, plain, (![A_41, B_42]: (k3_tarski(k2_tarski(A_41, B_42))=k2_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.27/2.08  tff(c_208, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(B_50, A_49))), inference(superposition, [status(thm), theory('equality')], [c_12, c_102])).
% 5.27/2.08  tff(c_14, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.27/2.08  tff(c_214, plain, (![B_50, A_49]: (k2_xboole_0(B_50, A_49)=k2_xboole_0(A_49, B_50))), inference(superposition, [status(thm), theory('equality')], [c_208, c_14])).
% 5.27/2.08  tff(c_297, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(B_58, A_57))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.27/2.08  tff(c_306, plain, (![A_7, B_8]: (k2_xboole_0(k3_xboole_0(A_7, B_8), k4_xboole_0(A_7, B_8))=k2_xboole_0(k3_xboole_0(A_7, B_8), A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_297])).
% 5.27/2.08  tff(c_363, plain, (![A_62, B_63]: (k2_xboole_0(k3_xboole_0(A_62, B_63), k4_xboole_0(A_62, B_63))=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_214, c_306])).
% 5.27/2.08  tff(c_620, plain, (![A_78, B_79]: (k2_xboole_0(k3_xboole_0(A_78, k3_xboole_0(A_78, B_79)), k4_xboole_0(A_78, B_79))=A_78)), inference(superposition, [status(thm), theory('equality')], [c_8, c_363])).
% 5.27/2.08  tff(c_635, plain, (![A_78, B_79]: (k2_xboole_0(k4_xboole_0(A_78, B_79), k3_xboole_0(A_78, k3_xboole_0(A_78, B_79)))=A_78)), inference(superposition, [status(thm), theory('equality')], [c_620, c_214])).
% 5.27/2.08  tff(c_889, plain, (![A_86, B_87]: (k2_xboole_0(k4_xboole_0(A_86, B_87), k3_xboole_0(A_86, k3_xboole_0(A_86, B_87)))=A_86)), inference(superposition, [status(thm), theory('equality')], [c_620, c_214])).
% 5.27/2.08  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.27/2.08  tff(c_904, plain, (![A_86, B_87]: (k2_xboole_0(k4_xboole_0(A_86, B_87), k3_xboole_0(A_86, k3_xboole_0(A_86, B_87)))=k2_xboole_0(k4_xboole_0(A_86, B_87), A_86))), inference(superposition, [status(thm), theory('equality')], [c_889, c_10])).
% 5.27/2.08  tff(c_960, plain, (![A_88, B_89]: (k2_xboole_0(A_88, k4_xboole_0(A_88, B_89))=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_635, c_214, c_904])).
% 5.27/2.08  tff(c_985, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_429, c_960])).
% 5.27/2.08  tff(c_26, plain, (![A_26, B_27]: (m1_subset_1(k2_tops_1(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.27/2.08  tff(c_1029, plain, (![A_90, B_91, C_92]: (k4_subset_1(A_90, B_91, C_92)=k2_xboole_0(B_91, C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(A_90)) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.27/2.08  tff(c_3313, plain, (![A_143, B_144, B_145]: (k4_subset_1(u1_struct_0(A_143), B_144, k2_tops_1(A_143, B_145))=k2_xboole_0(B_144, k2_tops_1(A_143, B_145)) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(resolution, [status(thm)], [c_26, c_1029])).
% 5.27/2.08  tff(c_3317, plain, (![B_145]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_145))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_145)) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_3313])).
% 5.27/2.08  tff(c_3325, plain, (![B_146]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_146))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_146)) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3317])).
% 5.27/2.08  tff(c_3332, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_3325])).
% 5.27/2.08  tff(c_3337, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_985, c_3332])).
% 5.27/2.08  tff(c_3339, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1409, c_3337])).
% 5.27/2.08  tff(c_3340, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 5.27/2.08  tff(c_3509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_3340])).
% 5.27/2.08  tff(c_3510, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.27/2.08  tff(c_3613, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3510, c_38])).
% 5.27/2.08  tff(c_3752, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3751, c_3613])).
% 5.27/2.08  tff(c_3902, plain, (![A_189, B_190]: (k2_pre_topc(A_189, B_190)=B_190 | ~v4_pre_topc(B_190, A_189) | ~m1_subset_1(B_190, k1_zfmisc_1(u1_struct_0(A_189))) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.27/2.08  tff(c_3908, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3902])).
% 5.27/2.08  tff(c_3912, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_3510, c_3908])).
% 5.27/2.08  tff(c_4500, plain, (![A_220, B_221]: (k7_subset_1(u1_struct_0(A_220), k2_pre_topc(A_220, B_221), k1_tops_1(A_220, B_221))=k2_tops_1(A_220, B_221) | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0(A_220))) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.27/2.08  tff(c_4509, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3912, c_4500])).
% 5.27/2.08  tff(c_4513, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_3751, c_4509])).
% 5.27/2.08  tff(c_4515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3752, c_4513])).
% 5.27/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.27/2.08  
% 5.27/2.08  Inference rules
% 5.27/2.08  ----------------------
% 5.27/2.08  #Ref     : 0
% 5.27/2.08  #Sup     : 1104
% 5.27/2.08  #Fact    : 0
% 5.27/2.08  #Define  : 0
% 5.27/2.08  #Split   : 3
% 5.27/2.08  #Chain   : 0
% 5.27/2.08  #Close   : 0
% 5.27/2.08  
% 5.27/2.08  Ordering : KBO
% 5.27/2.08  
% 5.27/2.08  Simplification rules
% 5.27/2.08  ----------------------
% 5.27/2.08  #Subsume      : 23
% 5.27/2.08  #Demod        : 1696
% 5.27/2.08  #Tautology    : 791
% 5.27/2.08  #SimpNegUnit  : 3
% 5.27/2.08  #BackRed      : 1
% 5.27/2.08  
% 5.27/2.08  #Partial instantiations: 0
% 5.27/2.08  #Strategies tried      : 1
% 5.27/2.08  
% 5.27/2.08  Timing (in seconds)
% 5.27/2.08  ----------------------
% 5.27/2.08  Preprocessing        : 0.35
% 5.27/2.08  Parsing              : 0.19
% 5.27/2.08  CNF conversion       : 0.02
% 5.27/2.08  Main loop            : 0.92
% 5.27/2.09  Inferencing          : 0.27
% 5.27/2.09  Reduction            : 0.46
% 5.27/2.09  Demodulation         : 0.40
% 5.27/2.09  BG Simplification    : 0.03
% 5.27/2.09  Subsumption          : 0.11
% 5.27/2.09  Abstraction          : 0.05
% 5.27/2.09  MUC search           : 0.00
% 5.27/2.09  Cooper               : 0.00
% 5.27/2.09  Total                : 1.30
% 5.27/2.09  Index Insertion      : 0.00
% 5.27/2.09  Index Deletion       : 0.00
% 5.27/2.09  Index Matching       : 0.00
% 5.27/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
