%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:25 EST 2020

% Result     : Theorem 16.48s
% Output     : CNFRefutation 16.51s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 314 expanded)
%              Number of leaves         :   43 ( 124 expanded)
%              Depth                    :   11
%              Number of atoms          :  187 ( 540 expanded)
%              Number of equality atoms :   92 ( 228 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_86,axiom,(
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

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40505,plain,(
    ! [A_609,B_610,C_611] :
      ( k7_subset_1(A_609,B_610,C_611) = k4_xboole_0(B_610,C_611)
      | ~ m1_subset_1(B_610,k1_zfmisc_1(A_609)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40514,plain,(
    ! [C_611] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_611) = k4_xboole_0('#skF_2',C_611) ),
    inference(resolution,[status(thm)],[c_46,c_40505])).

tff(c_58,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_150,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_237,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_48,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_50,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2091,plain,(
    ! [B_125,A_126] :
      ( v4_pre_topc(B_125,A_126)
      | k2_pre_topc(A_126,B_125) != B_125
      | ~ v2_pre_topc(A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2105,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2091])).

tff(c_2111,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50,c_2105])).

tff(c_2112,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_2111])).

tff(c_606,plain,(
    ! [A_86,B_87,C_88] :
      ( k7_subset_1(A_86,B_87,C_88) = k4_xboole_0(B_87,C_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_615,plain,(
    ! [C_88] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_88) = k4_xboole_0('#skF_2',C_88) ),
    inference(resolution,[status(thm)],[c_46,c_606])).

tff(c_2373,plain,(
    ! [A_129,B_130] :
      ( k7_subset_1(u1_struct_0(A_129),B_130,k2_tops_1(A_129,B_130)) = k1_tops_1(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2383,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2373])).

tff(c_2389,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_615,c_2383])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_145,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_149,plain,(
    ! [A_9,B_10] : k3_xboole_0(k4_xboole_0(A_9,B_10),A_9) = k4_xboole_0(A_9,B_10) ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_2405,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2389,c_149])).

tff(c_2421,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2389,c_4,c_2405])).

tff(c_413,plain,(
    ! [A_76,B_77] : k3_xboole_0(k4_xboole_0(A_76,B_77),A_76) = k4_xboole_0(A_76,B_77) ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_457,plain,(
    ! [A_3,B_77] : k3_xboole_0(A_3,k4_xboole_0(A_3,B_77)) = k4_xboole_0(A_3,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_413])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_211,plain,(
    ! [A_66,B_67] : k4_xboole_0(A_66,k4_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [A_66,B_67] : k2_xboole_0(k4_xboole_0(A_66,B_67),k3_xboole_0(A_66,B_67)) = k2_xboole_0(k4_xboole_0(A_66,B_67),A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_12])).

tff(c_4062,plain,(
    ! [A_156,B_157] : k2_xboole_0(k4_xboole_0(A_156,B_157),k3_xboole_0(A_156,B_157)) = k2_xboole_0(A_156,k4_xboole_0(A_156,B_157)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_220])).

tff(c_4164,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),k3_xboole_0(A_13,k4_xboole_0(A_13,B_14))) = k2_xboole_0(A_13,k4_xboole_0(A_13,k4_xboole_0(A_13,B_14))) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_4062])).

tff(c_4209,plain,(
    ! [A_13,B_14] : k2_xboole_0(k3_xboole_0(A_13,B_14),k4_xboole_0(A_13,B_14)) = k2_xboole_0(A_13,k3_xboole_0(A_13,B_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_14,c_4164])).

tff(c_4071,plain,(
    ! [A_156,B_157] : k2_xboole_0(k3_xboole_0(A_156,B_157),k4_xboole_0(A_156,B_157)) = k2_xboole_0(A_156,k4_xboole_0(A_156,B_157)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4062,c_2])).

tff(c_11607,plain,(
    ! [A_156,B_157] : k2_xboole_0(A_156,k4_xboole_0(A_156,B_157)) = k2_xboole_0(A_156,k3_xboole_0(A_156,B_157)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4209,c_4071])).

tff(c_234,plain,(
    ! [A_66,B_67] : k2_xboole_0(k4_xboole_0(A_66,B_67),k3_xboole_0(A_66,B_67)) = k2_xboole_0(A_66,k4_xboole_0(A_66,B_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_220])).

tff(c_11608,plain,(
    ! [A_66,B_67] : k2_xboole_0(k4_xboole_0(A_66,B_67),k3_xboole_0(A_66,B_67)) = k2_xboole_0(A_66,k3_xboole_0(A_66,B_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11607,c_234])).

tff(c_223,plain,(
    ! [A_66,B_67] : r1_tarski(k3_xboole_0(A_66,B_67),A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_10])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1804,plain,(
    ! [A_116,B_117,C_118] :
      ( k4_subset_1(A_116,B_117,C_118) = k2_xboole_0(B_117,C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(A_116))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4541,plain,(
    ! [B_168,B_169,A_170] :
      ( k4_subset_1(B_168,B_169,A_170) = k2_xboole_0(B_169,A_170)
      | ~ m1_subset_1(B_169,k1_zfmisc_1(B_168))
      | ~ r1_tarski(A_170,B_168) ) ),
    inference(resolution,[status(thm)],[c_32,c_1804])).

tff(c_13837,plain,(
    ! [B_313,A_314,A_315] :
      ( k4_subset_1(B_313,A_314,A_315) = k2_xboole_0(A_314,A_315)
      | ~ r1_tarski(A_315,B_313)
      | ~ r1_tarski(A_314,B_313) ) ),
    inference(resolution,[status(thm)],[c_32,c_4541])).

tff(c_38530,plain,(
    ! [A_545,A_546,B_547] :
      ( k4_subset_1(A_545,A_546,k3_xboole_0(A_545,B_547)) = k2_xboole_0(A_546,k3_xboole_0(A_545,B_547))
      | ~ r1_tarski(A_546,A_545) ) ),
    inference(resolution,[status(thm)],[c_223,c_13837])).

tff(c_288,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k3_subset_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2640,plain,(
    ! [B_133,A_134] :
      ( k4_xboole_0(B_133,A_134) = k3_subset_1(B_133,A_134)
      | ~ r1_tarski(A_134,B_133) ) ),
    inference(resolution,[status(thm)],[c_32,c_288])).

tff(c_2682,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_subset_1(A_9,k4_xboole_0(A_9,B_10)) ),
    inference(resolution,[status(thm)],[c_10,c_2640])).

tff(c_2703,plain,(
    ! [A_9,B_10] : k3_subset_1(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2682])).

tff(c_16,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [A_26,B_27] :
      ( k4_subset_1(A_26,B_27,k3_subset_1(A_26,B_27)) = k2_subset_1(A_26)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_842,plain,(
    ! [A_94,B_95] :
      ( k4_subset_1(A_94,B_95,k3_subset_1(A_94,B_95)) = A_94
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26])).

tff(c_3104,plain,(
    ! [B_141,A_142] :
      ( k4_subset_1(B_141,A_142,k3_subset_1(B_141,A_142)) = B_141
      | ~ r1_tarski(A_142,B_141) ) ),
    inference(resolution,[status(thm)],[c_32,c_842])).

tff(c_3125,plain,(
    ! [A_9,B_10] :
      ( k4_subset_1(A_9,k4_xboole_0(A_9,B_10),k3_xboole_0(A_9,B_10)) = A_9
      | ~ r1_tarski(k4_xboole_0(A_9,B_10),A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2703,c_3104])).

tff(c_3141,plain,(
    ! [A_9,B_10] : k4_subset_1(A_9,k4_xboole_0(A_9,B_10),k3_xboole_0(A_9,B_10)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_3125])).

tff(c_38581,plain,(
    ! [A_545,B_547] :
      ( k2_xboole_0(k4_xboole_0(A_545,B_547),k3_xboole_0(A_545,B_547)) = A_545
      | ~ r1_tarski(k4_xboole_0(A_545,B_547),A_545) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38530,c_3141])).

tff(c_38900,plain,(
    ! [A_549,B_550] : k2_xboole_0(A_549,k3_xboole_0(A_549,B_550)) = A_549 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_11608,c_38581])).

tff(c_38996,plain,(
    k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2421,c_38900])).

tff(c_2608,plain,(
    ! [A_131,B_132] :
      ( k4_subset_1(u1_struct_0(A_131),B_132,k2_tops_1(A_131,B_132)) = k2_pre_topc(A_131,B_132)
      | ~ m1_subset_1(B_132,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ l1_pre_topc(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2618,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_2608])).

tff(c_2624,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2618])).

tff(c_38,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k2_tops_1(A_35,B_36),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9262,plain,(
    ! [A_242,B_243,B_244] :
      ( k4_subset_1(u1_struct_0(A_242),B_243,k2_tops_1(A_242,B_244)) = k2_xboole_0(B_243,k2_tops_1(A_242,B_244))
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(resolution,[status(thm)],[c_38,c_1804])).

tff(c_9272,plain,(
    ! [B_244] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_244)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_244))
      | ~ m1_subset_1(B_244,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_46,c_9262])).

tff(c_9351,plain,(
    ! [B_248] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_248)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_248))
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_9272])).

tff(c_9366,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_9351])).

tff(c_9373,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2624,c_9366])).

tff(c_616,plain,(
    ! [C_89] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_89) = k4_xboole_0('#skF_2',C_89) ),
    inference(resolution,[status(thm)],[c_46,c_606])).

tff(c_628,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_616])).

tff(c_782,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_149])).

tff(c_797,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_4,c_782])).

tff(c_11609,plain,(
    ! [A_288,B_289] : k2_xboole_0(A_288,k4_xboole_0(A_288,B_289)) = k2_xboole_0(A_288,k3_xboole_0(A_288,B_289)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4209,c_4071])).

tff(c_11643,plain,(
    k2_xboole_0('#skF_2',k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2389,c_11609])).

tff(c_11671,plain,(
    k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9373,c_797,c_11643])).

tff(c_39257,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38996,c_11671])).

tff(c_39259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2112,c_39257])).

tff(c_39260,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_39590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_39260])).

tff(c_39591,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_39604,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_39591,c_52])).

tff(c_40515,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40514,c_39604])).

tff(c_41425,plain,(
    ! [A_633,B_634] :
      ( r1_tarski(k2_tops_1(A_633,B_634),B_634)
      | ~ v4_pre_topc(B_634,A_633)
      | ~ m1_subset_1(B_634,k1_zfmisc_1(u1_struct_0(A_633)))
      | ~ l1_pre_topc(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_41435,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_41425])).

tff(c_41441,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_39591,c_41435])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41445,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_41441,c_8])).

tff(c_41507,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_41445])).

tff(c_41910,plain,(
    ! [A_640,B_641] :
      ( k7_subset_1(u1_struct_0(A_640),B_641,k2_tops_1(A_640,B_641)) = k1_tops_1(A_640,B_641)
      | ~ m1_subset_1(B_641,k1_zfmisc_1(u1_struct_0(A_640)))
      | ~ l1_pre_topc(A_640) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_41920,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_41910])).

tff(c_41926,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40514,c_41920])).

tff(c_41945,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_41926,c_14])).

tff(c_41959,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41507,c_41945])).

tff(c_41961,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40515,c_41959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:23:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.48/8.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.51/8.75  
% 16.51/8.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.51/8.75  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 16.51/8.75  
% 16.51/8.75  %Foreground sorts:
% 16.51/8.75  
% 16.51/8.75  
% 16.51/8.75  %Background operators:
% 16.51/8.75  
% 16.51/8.75  
% 16.51/8.75  %Foreground operators:
% 16.51/8.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.51/8.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.51/8.75  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 16.51/8.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.51/8.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.51/8.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.51/8.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.51/8.75  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 16.51/8.75  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 16.51/8.75  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 16.51/8.75  tff('#skF_2', type, '#skF_2': $i).
% 16.51/8.75  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 16.51/8.75  tff('#skF_1', type, '#skF_1': $i).
% 16.51/8.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.51/8.75  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 16.51/8.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.51/8.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.51/8.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.51/8.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.51/8.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.51/8.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.51/8.75  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 16.51/8.75  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 16.51/8.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.51/8.75  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.51/8.75  
% 16.51/8.78  tff(f_127, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 16.51/8.78  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 16.51/8.78  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 16.51/8.78  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 16.51/8.78  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 16.51/8.78  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 16.51/8.78  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 16.51/8.78  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 16.51/8.78  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 16.51/8.78  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 16.51/8.78  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 16.51/8.78  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 16.51/8.78  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 16.51/8.78  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 16.51/8.78  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 16.51/8.78  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 16.51/8.78  tff(f_92, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 16.51/8.78  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 16.51/8.78  tff(c_46, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 16.51/8.78  tff(c_40505, plain, (![A_609, B_610, C_611]: (k7_subset_1(A_609, B_610, C_611)=k4_xboole_0(B_610, C_611) | ~m1_subset_1(B_610, k1_zfmisc_1(A_609)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.51/8.78  tff(c_40514, plain, (![C_611]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_611)=k4_xboole_0('#skF_2', C_611))), inference(resolution, [status(thm)], [c_46, c_40505])).
% 16.51/8.78  tff(c_58, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 16.51/8.78  tff(c_150, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_58])).
% 16.51/8.78  tff(c_52, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 16.51/8.78  tff(c_237, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 16.51/8.78  tff(c_48, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 16.51/8.78  tff(c_50, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_127])).
% 16.51/8.78  tff(c_2091, plain, (![B_125, A_126]: (v4_pre_topc(B_125, A_126) | k2_pre_topc(A_126, B_125)!=B_125 | ~v2_pre_topc(A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_86])).
% 16.51/8.78  tff(c_2105, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_2091])).
% 16.51/8.78  tff(c_2111, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50, c_2105])).
% 16.51/8.78  tff(c_2112, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_237, c_2111])).
% 16.51/8.78  tff(c_606, plain, (![A_86, B_87, C_88]: (k7_subset_1(A_86, B_87, C_88)=k4_xboole_0(B_87, C_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.51/8.78  tff(c_615, plain, (![C_88]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_88)=k4_xboole_0('#skF_2', C_88))), inference(resolution, [status(thm)], [c_46, c_606])).
% 16.51/8.78  tff(c_2373, plain, (![A_129, B_130]: (k7_subset_1(u1_struct_0(A_129), B_130, k2_tops_1(A_129, B_130))=k1_tops_1(A_129, B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.51/8.78  tff(c_2383, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_2373])).
% 16.51/8.78  tff(c_2389, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_615, c_2383])).
% 16.51/8.78  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.51/8.78  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.51/8.78  tff(c_145, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.51/8.78  tff(c_149, plain, (![A_9, B_10]: (k3_xboole_0(k4_xboole_0(A_9, B_10), A_9)=k4_xboole_0(A_9, B_10))), inference(resolution, [status(thm)], [c_10, c_145])).
% 16.51/8.78  tff(c_2405, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2389, c_149])).
% 16.51/8.78  tff(c_2421, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2389, c_4, c_2405])).
% 16.51/8.78  tff(c_413, plain, (![A_76, B_77]: (k3_xboole_0(k4_xboole_0(A_76, B_77), A_76)=k4_xboole_0(A_76, B_77))), inference(resolution, [status(thm)], [c_10, c_145])).
% 16.51/8.78  tff(c_457, plain, (![A_3, B_77]: (k3_xboole_0(A_3, k4_xboole_0(A_3, B_77))=k4_xboole_0(A_3, B_77))), inference(superposition, [status(thm), theory('equality')], [c_4, c_413])).
% 16.51/8.78  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.51/8.78  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.51/8.78  tff(c_211, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k4_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_41])).
% 16.51/8.78  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.51/8.78  tff(c_220, plain, (![A_66, B_67]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k3_xboole_0(A_66, B_67))=k2_xboole_0(k4_xboole_0(A_66, B_67), A_66))), inference(superposition, [status(thm), theory('equality')], [c_211, c_12])).
% 16.51/8.78  tff(c_4062, plain, (![A_156, B_157]: (k2_xboole_0(k4_xboole_0(A_156, B_157), k3_xboole_0(A_156, B_157))=k2_xboole_0(A_156, k4_xboole_0(A_156, B_157)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_220])).
% 16.51/8.78  tff(c_4164, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k3_xboole_0(A_13, k4_xboole_0(A_13, B_14)))=k2_xboole_0(A_13, k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))))), inference(superposition, [status(thm), theory('equality')], [c_14, c_4062])).
% 16.51/8.78  tff(c_4209, plain, (![A_13, B_14]: (k2_xboole_0(k3_xboole_0(A_13, B_14), k4_xboole_0(A_13, B_14))=k2_xboole_0(A_13, k3_xboole_0(A_13, B_14)))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_14, c_4164])).
% 16.51/8.78  tff(c_4071, plain, (![A_156, B_157]: (k2_xboole_0(k3_xboole_0(A_156, B_157), k4_xboole_0(A_156, B_157))=k2_xboole_0(A_156, k4_xboole_0(A_156, B_157)))), inference(superposition, [status(thm), theory('equality')], [c_4062, c_2])).
% 16.51/8.78  tff(c_11607, plain, (![A_156, B_157]: (k2_xboole_0(A_156, k4_xboole_0(A_156, B_157))=k2_xboole_0(A_156, k3_xboole_0(A_156, B_157)))), inference(demodulation, [status(thm), theory('equality')], [c_4209, c_4071])).
% 16.51/8.78  tff(c_234, plain, (![A_66, B_67]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k3_xboole_0(A_66, B_67))=k2_xboole_0(A_66, k4_xboole_0(A_66, B_67)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_220])).
% 16.51/8.78  tff(c_11608, plain, (![A_66, B_67]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k3_xboole_0(A_66, B_67))=k2_xboole_0(A_66, k3_xboole_0(A_66, B_67)))), inference(demodulation, [status(thm), theory('equality')], [c_11607, c_234])).
% 16.51/8.78  tff(c_223, plain, (![A_66, B_67]: (r1_tarski(k3_xboole_0(A_66, B_67), A_66))), inference(superposition, [status(thm), theory('equality')], [c_211, c_10])).
% 16.51/8.78  tff(c_32, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_71])).
% 16.51/8.78  tff(c_1804, plain, (![A_116, B_117, C_118]: (k4_subset_1(A_116, B_117, C_118)=k2_xboole_0(B_117, C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(A_116)) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.51/8.78  tff(c_4541, plain, (![B_168, B_169, A_170]: (k4_subset_1(B_168, B_169, A_170)=k2_xboole_0(B_169, A_170) | ~m1_subset_1(B_169, k1_zfmisc_1(B_168)) | ~r1_tarski(A_170, B_168))), inference(resolution, [status(thm)], [c_32, c_1804])).
% 16.51/8.78  tff(c_13837, plain, (![B_313, A_314, A_315]: (k4_subset_1(B_313, A_314, A_315)=k2_xboole_0(A_314, A_315) | ~r1_tarski(A_315, B_313) | ~r1_tarski(A_314, B_313))), inference(resolution, [status(thm)], [c_32, c_4541])).
% 16.51/8.78  tff(c_38530, plain, (![A_545, A_546, B_547]: (k4_subset_1(A_545, A_546, k3_xboole_0(A_545, B_547))=k2_xboole_0(A_546, k3_xboole_0(A_545, B_547)) | ~r1_tarski(A_546, A_545))), inference(resolution, [status(thm)], [c_223, c_13837])).
% 16.51/8.78  tff(c_288, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k3_subset_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 16.51/8.78  tff(c_2640, plain, (![B_133, A_134]: (k4_xboole_0(B_133, A_134)=k3_subset_1(B_133, A_134) | ~r1_tarski(A_134, B_133))), inference(resolution, [status(thm)], [c_32, c_288])).
% 16.51/8.78  tff(c_2682, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_subset_1(A_9, k4_xboole_0(A_9, B_10)))), inference(resolution, [status(thm)], [c_10, c_2640])).
% 16.51/8.78  tff(c_2703, plain, (![A_9, B_10]: (k3_subset_1(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2682])).
% 16.51/8.78  tff(c_16, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.51/8.78  tff(c_26, plain, (![A_26, B_27]: (k4_subset_1(A_26, B_27, k3_subset_1(A_26, B_27))=k2_subset_1(A_26) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.51/8.78  tff(c_842, plain, (![A_94, B_95]: (k4_subset_1(A_94, B_95, k3_subset_1(A_94, B_95))=A_94 | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26])).
% 16.51/8.78  tff(c_3104, plain, (![B_141, A_142]: (k4_subset_1(B_141, A_142, k3_subset_1(B_141, A_142))=B_141 | ~r1_tarski(A_142, B_141))), inference(resolution, [status(thm)], [c_32, c_842])).
% 16.51/8.78  tff(c_3125, plain, (![A_9, B_10]: (k4_subset_1(A_9, k4_xboole_0(A_9, B_10), k3_xboole_0(A_9, B_10))=A_9 | ~r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(superposition, [status(thm), theory('equality')], [c_2703, c_3104])).
% 16.51/8.78  tff(c_3141, plain, (![A_9, B_10]: (k4_subset_1(A_9, k4_xboole_0(A_9, B_10), k3_xboole_0(A_9, B_10))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_3125])).
% 16.51/8.78  tff(c_38581, plain, (![A_545, B_547]: (k2_xboole_0(k4_xboole_0(A_545, B_547), k3_xboole_0(A_545, B_547))=A_545 | ~r1_tarski(k4_xboole_0(A_545, B_547), A_545))), inference(superposition, [status(thm), theory('equality')], [c_38530, c_3141])).
% 16.51/8.78  tff(c_38900, plain, (![A_549, B_550]: (k2_xboole_0(A_549, k3_xboole_0(A_549, B_550))=A_549)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_11608, c_38581])).
% 16.51/8.78  tff(c_38996, plain, (k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2421, c_38900])).
% 16.51/8.78  tff(c_2608, plain, (![A_131, B_132]: (k4_subset_1(u1_struct_0(A_131), B_132, k2_tops_1(A_131, B_132))=k2_pre_topc(A_131, B_132) | ~m1_subset_1(B_132, k1_zfmisc_1(u1_struct_0(A_131))) | ~l1_pre_topc(A_131))), inference(cnfTransformation, [status(thm)], [f_99])).
% 16.51/8.78  tff(c_2618, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_2608])).
% 16.51/8.78  tff(c_2624, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2618])).
% 16.51/8.78  tff(c_38, plain, (![A_35, B_36]: (m1_subset_1(k2_tops_1(A_35, B_36), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_subset_1(B_36, k1_zfmisc_1(u1_struct_0(A_35))) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.51/8.78  tff(c_9262, plain, (![A_242, B_243, B_244]: (k4_subset_1(u1_struct_0(A_242), B_243, k2_tops_1(A_242, B_244))=k2_xboole_0(B_243, k2_tops_1(A_242, B_244)) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242))), inference(resolution, [status(thm)], [c_38, c_1804])).
% 16.51/8.78  tff(c_9272, plain, (![B_244]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_244))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_244)) | ~m1_subset_1(B_244, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_9262])).
% 16.51/8.78  tff(c_9351, plain, (![B_248]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_248))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_248)) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_9272])).
% 16.51/8.78  tff(c_9366, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_46, c_9351])).
% 16.51/8.78  tff(c_9373, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2624, c_9366])).
% 16.51/8.78  tff(c_616, plain, (![C_89]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_89)=k4_xboole_0('#skF_2', C_89))), inference(resolution, [status(thm)], [c_46, c_606])).
% 16.51/8.78  tff(c_628, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_150, c_616])).
% 16.51/8.78  tff(c_782, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_628, c_149])).
% 16.51/8.78  tff(c_797, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_628, c_4, c_782])).
% 16.51/8.78  tff(c_11609, plain, (![A_288, B_289]: (k2_xboole_0(A_288, k4_xboole_0(A_288, B_289))=k2_xboole_0(A_288, k3_xboole_0(A_288, B_289)))), inference(demodulation, [status(thm), theory('equality')], [c_4209, c_4071])).
% 16.51/8.78  tff(c_11643, plain, (k2_xboole_0('#skF_2', k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2389, c_11609])).
% 16.51/8.78  tff(c_11671, plain, (k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9373, c_797, c_11643])).
% 16.51/8.78  tff(c_39257, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38996, c_11671])).
% 16.51/8.78  tff(c_39259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2112, c_39257])).
% 16.51/8.78  tff(c_39260, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 16.51/8.78  tff(c_39590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_39260])).
% 16.51/8.78  tff(c_39591, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_58])).
% 16.51/8.78  tff(c_39604, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_39591, c_52])).
% 16.51/8.78  tff(c_40515, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40514, c_39604])).
% 16.51/8.78  tff(c_41425, plain, (![A_633, B_634]: (r1_tarski(k2_tops_1(A_633, B_634), B_634) | ~v4_pre_topc(B_634, A_633) | ~m1_subset_1(B_634, k1_zfmisc_1(u1_struct_0(A_633))) | ~l1_pre_topc(A_633))), inference(cnfTransformation, [status(thm)], [f_108])).
% 16.51/8.78  tff(c_41435, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_41425])).
% 16.51/8.78  tff(c_41441, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_39591, c_41435])).
% 16.51/8.78  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.51/8.78  tff(c_41445, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_41441, c_8])).
% 16.51/8.78  tff(c_41507, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_41445])).
% 16.51/8.78  tff(c_41910, plain, (![A_640, B_641]: (k7_subset_1(u1_struct_0(A_640), B_641, k2_tops_1(A_640, B_641))=k1_tops_1(A_640, B_641) | ~m1_subset_1(B_641, k1_zfmisc_1(u1_struct_0(A_640))) | ~l1_pre_topc(A_640))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.51/8.78  tff(c_41920, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_46, c_41910])).
% 16.51/8.78  tff(c_41926, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40514, c_41920])).
% 16.51/8.78  tff(c_41945, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_41926, c_14])).
% 16.51/8.78  tff(c_41959, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_41507, c_41945])).
% 16.51/8.78  tff(c_41961, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40515, c_41959])).
% 16.51/8.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.51/8.78  
% 16.51/8.78  Inference rules
% 16.51/8.78  ----------------------
% 16.51/8.78  #Ref     : 0
% 16.51/8.78  #Sup     : 10301
% 16.51/8.78  #Fact    : 0
% 16.51/8.78  #Define  : 0
% 16.51/8.78  #Split   : 6
% 16.51/8.78  #Chain   : 0
% 16.51/8.78  #Close   : 0
% 16.51/8.78  
% 16.51/8.78  Ordering : KBO
% 16.51/8.78  
% 16.51/8.78  Simplification rules
% 16.51/8.78  ----------------------
% 16.51/8.78  #Subsume      : 926
% 16.51/8.78  #Demod        : 16306
% 16.51/8.78  #Tautology    : 5762
% 16.51/8.78  #SimpNegUnit  : 25
% 16.51/8.78  #BackRed      : 42
% 16.51/8.78  
% 16.51/8.78  #Partial instantiations: 0
% 16.51/8.78  #Strategies tried      : 1
% 16.51/8.78  
% 16.51/8.78  Timing (in seconds)
% 16.51/8.78  ----------------------
% 16.51/8.78  Preprocessing        : 0.44
% 16.51/8.78  Parsing              : 0.24
% 16.51/8.78  CNF conversion       : 0.03
% 16.51/8.78  Main loop            : 7.47
% 16.51/8.78  Inferencing          : 1.17
% 16.51/8.78  Reduction            : 4.61
% 16.51/8.78  Demodulation         : 4.15
% 16.51/8.78  BG Simplification    : 0.13
% 16.51/8.78  Subsumption          : 1.23
% 16.51/8.78  Abstraction          : 0.28
% 16.51/8.78  MUC search           : 0.00
% 16.51/8.78  Cooper               : 0.00
% 16.51/8.78  Total                : 7.96
% 16.51/8.78  Index Insertion      : 0.00
% 16.51/8.78  Index Deletion       : 0.00
% 16.51/8.78  Index Matching       : 0.00
% 16.51/8.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
