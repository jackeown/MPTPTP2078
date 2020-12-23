%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:19 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 191 expanded)
%              Number of leaves         :   45 (  82 expanded)
%              Depth                    :   15
%              Number of atoms          :  160 ( 322 expanded)
%              Number of equality atoms :   85 ( 132 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_65,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_11295,plain,(
    ! [A_334,B_335,C_336] :
      ( k7_subset_1(A_334,B_335,C_336) = k4_xboole_0(B_335,C_336)
      | ~ m1_subset_1(B_335,k1_zfmisc_1(A_334)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_11301,plain,(
    ! [C_336] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_336) = k4_xboole_0('#skF_2',C_336) ),
    inference(resolution,[status(thm)],[c_48,c_11295])).

tff(c_54,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_104,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1952,plain,(
    ! [B_144,A_145] :
      ( v4_pre_topc(B_144,A_145)
      | k2_pre_topc(A_145,B_144) != B_144
      | ~ v2_pre_topc(A_145)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1962,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1952])).

tff(c_1967,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_1962])).

tff(c_1968,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_1967])).

tff(c_904,plain,(
    ! [A_104,B_105,C_106] :
      ( k7_subset_1(A_104,B_105,C_106) = k4_xboole_0(B_105,C_106)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1057,plain,(
    ! [C_113] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_113) = k4_xboole_0('#skF_2',C_113) ),
    inference(resolution,[status(thm)],[c_48,c_904])).

tff(c_60,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_200,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_60])).

tff(c_1063,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1057,c_200])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k2_xboole_0(A_53,B_54)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_91])).

tff(c_310,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_319,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k2_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_310])).

tff(c_328,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_319])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_368,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k4_xboole_0(A_76,B_77)) = k3_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_392,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_368])).

tff(c_399,plain,(
    ! [A_9,B_10] : k3_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_392])).

tff(c_501,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_514,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k5_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_501])).

tff(c_537,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_514])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(A_31,k1_zfmisc_1(B_32))
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_670,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = k3_subset_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1791,plain,(
    ! [B_137,A_138] :
      ( k4_xboole_0(B_137,A_138) = k3_subset_1(B_137,A_138)
      | ~ r1_tarski(A_138,B_137) ) ),
    inference(resolution,[status(thm)],[c_34,c_670])).

tff(c_1824,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_subset_1(A_6,k4_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_8,c_1791])).

tff(c_1901,plain,(
    ! [A_142,B_143] : k3_subset_1(A_142,k4_xboole_0(A_142,B_143)) = k3_xboole_0(A_142,B_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1824])).

tff(c_625,plain,(
    ! [A_89,B_90] :
      ( k3_subset_1(A_89,k3_subset_1(A_89,B_90)) = B_90
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_630,plain,(
    ! [B_32,A_31] :
      ( k3_subset_1(B_32,k3_subset_1(B_32,A_31)) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(resolution,[status(thm)],[c_34,c_625])).

tff(c_1907,plain,(
    ! [A_142,B_143] :
      ( k3_subset_1(A_142,k3_xboole_0(A_142,B_143)) = k4_xboole_0(A_142,B_143)
      | ~ r1_tarski(k4_xboole_0(A_142,B_143),A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1901,c_630])).

tff(c_1943,plain,(
    ! [A_142,B_143] : k3_subset_1(A_142,k3_xboole_0(A_142,B_143)) = k4_xboole_0(A_142,B_143) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1907])).

tff(c_380,plain,(
    ! [A_76,B_77] : r1_tarski(k3_xboole_0(A_76,B_77),A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_8])).

tff(c_1833,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k3_subset_1(A_76,k3_xboole_0(A_76,B_77)) ),
    inference(resolution,[status(thm)],[c_380,c_1791])).

tff(c_2665,plain,(
    ! [A_76,B_77] : k4_xboole_0(A_76,k3_xboole_0(A_76,B_77)) = k4_xboole_0(A_76,B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1943,c_1833])).

tff(c_383,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_368])).

tff(c_2736,plain,(
    ! [A_174,B_175] : k3_xboole_0(A_174,k4_xboole_0(A_174,B_175)) = k4_xboole_0(A_174,B_175) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2665,c_383])).

tff(c_18,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_160,plain,(
    ! [A_59,B_60] : k1_setfam_1(k2_tarski(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_205,plain,(
    ! [A_67,B_68] : k1_setfam_1(k2_tarski(A_67,B_68)) = k3_xboole_0(B_68,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_160])).

tff(c_30,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_211,plain,(
    ! [B_68,A_67] : k3_xboole_0(B_68,A_67) = k3_xboole_0(A_67,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_30])).

tff(c_527,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(B_68,A_67)) = k4_xboole_0(A_67,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_501])).

tff(c_2751,plain,(
    ! [A_174,B_175] : k5_xboole_0(k4_xboole_0(A_174,B_175),k4_xboole_0(A_174,B_175)) = k4_xboole_0(k4_xboole_0(A_174,B_175),A_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_2736,c_527])).

tff(c_2831,plain,(
    ! [A_176,B_177] : k4_xboole_0(k4_xboole_0(A_176,B_177),A_176) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_537,c_2751])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2848,plain,(
    ! [A_176,B_177] : k2_xboole_0(A_176,k4_xboole_0(A_176,B_177)) = k5_xboole_0(A_176,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2831,c_16])).

tff(c_2922,plain,(
    ! [A_178,B_179] : k2_xboole_0(A_178,k4_xboole_0(A_178,B_179)) = A_178 ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_2848])).

tff(c_3004,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1063,c_2922])).

tff(c_2181,plain,(
    ! [A_149,B_150] :
      ( k4_subset_1(u1_struct_0(A_149),B_150,k2_tops_1(A_149,B_150)) = k2_pre_topc(A_149,B_150)
      | ~ m1_subset_1(B_150,k1_zfmisc_1(u1_struct_0(A_149)))
      | ~ l1_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2188,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2181])).

tff(c_2193,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2188])).

tff(c_40,plain,(
    ! [A_36,B_37] :
      ( m1_subset_1(k2_tops_1(A_36,B_37),k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(u1_struct_0(A_36)))
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1745,plain,(
    ! [A_132,B_133,C_134] :
      ( k4_subset_1(A_132,B_133,C_134) = k2_xboole_0(B_133,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(A_132))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10327,plain,(
    ! [A_277,B_278,B_279] :
      ( k4_subset_1(u1_struct_0(A_277),B_278,k2_tops_1(A_277,B_279)) = k2_xboole_0(B_278,k2_tops_1(A_277,B_279))
      | ~ m1_subset_1(B_278,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ l1_pre_topc(A_277) ) ),
    inference(resolution,[status(thm)],[c_40,c_1745])).

tff(c_10334,plain,(
    ! [B_279] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_279)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_279))
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_10327])).

tff(c_10343,plain,(
    ! [B_280] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_280)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_280))
      | ~ m1_subset_1(B_280,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10334])).

tff(c_10354,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_10343])).

tff(c_10360,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3004,c_2193,c_10354])).

tff(c_10362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1968,c_10360])).

tff(c_10363,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_11303,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11301,c_10363])).

tff(c_10364,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_11530,plain,(
    ! [A_344,B_345] :
      ( k2_pre_topc(A_344,B_345) = B_345
      | ~ v4_pre_topc(B_345,A_344)
      | ~ m1_subset_1(B_345,k1_zfmisc_1(u1_struct_0(A_344)))
      | ~ l1_pre_topc(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_11537,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_11530])).

tff(c_11541,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_10364,c_11537])).

tff(c_12917,plain,(
    ! [A_399,B_400] :
      ( k7_subset_1(u1_struct_0(A_399),k2_pre_topc(A_399,B_400),k1_tops_1(A_399,B_400)) = k2_tops_1(A_399,B_400)
      | ~ m1_subset_1(B_400,k1_zfmisc_1(u1_struct_0(A_399)))
      | ~ l1_pre_topc(A_399) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12926,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11541,c_12917])).

tff(c_12930,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_11301,c_12926])).

tff(c_12932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11303,c_12930])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.57  
% 7.21/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.57  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.21/2.57  
% 7.21/2.57  %Foreground sorts:
% 7.21/2.57  
% 7.21/2.57  
% 7.21/2.57  %Background operators:
% 7.21/2.57  
% 7.21/2.57  
% 7.21/2.57  %Foreground operators:
% 7.21/2.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.21/2.57  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.21/2.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.21/2.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.21/2.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.21/2.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.21/2.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.21/2.57  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.21/2.57  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.21/2.57  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.21/2.57  tff('#skF_2', type, '#skF_2': $i).
% 7.21/2.57  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.21/2.57  tff('#skF_1', type, '#skF_1': $i).
% 7.21/2.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.21/2.57  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.21/2.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.21/2.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.21/2.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.21/2.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.21/2.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.21/2.57  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.21/2.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.21/2.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.21/2.57  
% 7.21/2.59  tff(f_124, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 7.21/2.59  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.21/2.59  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.21/2.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 7.21/2.59  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.21/2.59  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.21/2.59  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.21/2.59  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.21/2.59  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.21/2.59  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.21/2.59  tff(f_69, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.21/2.59  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.21/2.59  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.21/2.59  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.21/2.59  tff(f_65, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.21/2.59  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 7.21/2.59  tff(f_90, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 7.21/2.59  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.21/2.59  tff(f_105, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 7.21/2.59  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.21/2.59  tff(c_11295, plain, (![A_334, B_335, C_336]: (k7_subset_1(A_334, B_335, C_336)=k4_xboole_0(B_335, C_336) | ~m1_subset_1(B_335, k1_zfmisc_1(A_334)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.21/2.59  tff(c_11301, plain, (![C_336]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_336)=k4_xboole_0('#skF_2', C_336))), inference(resolution, [status(thm)], [c_48, c_11295])).
% 7.21/2.59  tff(c_54, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.21/2.59  tff(c_104, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 7.21/2.59  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.21/2.59  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.21/2.59  tff(c_1952, plain, (![B_144, A_145]: (v4_pre_topc(B_144, A_145) | k2_pre_topc(A_145, B_144)!=B_144 | ~v2_pre_topc(A_145) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.21/2.59  tff(c_1962, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1952])).
% 7.21/2.59  tff(c_1967, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_1962])).
% 7.21/2.59  tff(c_1968, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_104, c_1967])).
% 7.21/2.59  tff(c_904, plain, (![A_104, B_105, C_106]: (k7_subset_1(A_104, B_105, C_106)=k4_xboole_0(B_105, C_106) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.21/2.59  tff(c_1057, plain, (![C_113]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_113)=k4_xboole_0('#skF_2', C_113))), inference(resolution, [status(thm)], [c_48, c_904])).
% 7.21/2.59  tff(c_60, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.21/2.59  tff(c_200, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_104, c_60])).
% 7.21/2.59  tff(c_1063, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1057, c_200])).
% 7.21/2.59  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.21/2.59  tff(c_91, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k2_xboole_0(A_53, B_54))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.21/2.59  tff(c_101, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_91])).
% 7.21/2.59  tff(c_310, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.21/2.59  tff(c_319, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k2_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_101, c_310])).
% 7.21/2.59  tff(c_328, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_319])).
% 7.21/2.59  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.21/2.59  tff(c_10, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.21/2.59  tff(c_368, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k4_xboole_0(A_76, B_77))=k3_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.21/2.59  tff(c_392, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k4_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_368])).
% 7.21/2.59  tff(c_399, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k2_xboole_0(A_9, B_10))=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_392])).
% 7.21/2.59  tff(c_501, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.21/2.59  tff(c_514, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k5_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_399, c_501])).
% 7.21/2.59  tff(c_537, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_514])).
% 7.21/2.59  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.21/2.59  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.21/2.59  tff(c_34, plain, (![A_31, B_32]: (m1_subset_1(A_31, k1_zfmisc_1(B_32)) | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_69])).
% 7.21/2.59  tff(c_670, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=k3_subset_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.21/2.59  tff(c_1791, plain, (![B_137, A_138]: (k4_xboole_0(B_137, A_138)=k3_subset_1(B_137, A_138) | ~r1_tarski(A_138, B_137))), inference(resolution, [status(thm)], [c_34, c_670])).
% 7.21/2.59  tff(c_1824, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_subset_1(A_6, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_8, c_1791])).
% 7.21/2.59  tff(c_1901, plain, (![A_142, B_143]: (k3_subset_1(A_142, k4_xboole_0(A_142, B_143))=k3_xboole_0(A_142, B_143))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1824])).
% 7.21/2.59  tff(c_625, plain, (![A_89, B_90]: (k3_subset_1(A_89, k3_subset_1(A_89, B_90))=B_90 | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.21/2.59  tff(c_630, plain, (![B_32, A_31]: (k3_subset_1(B_32, k3_subset_1(B_32, A_31))=A_31 | ~r1_tarski(A_31, B_32))), inference(resolution, [status(thm)], [c_34, c_625])).
% 7.21/2.59  tff(c_1907, plain, (![A_142, B_143]: (k3_subset_1(A_142, k3_xboole_0(A_142, B_143))=k4_xboole_0(A_142, B_143) | ~r1_tarski(k4_xboole_0(A_142, B_143), A_142))), inference(superposition, [status(thm), theory('equality')], [c_1901, c_630])).
% 7.21/2.59  tff(c_1943, plain, (![A_142, B_143]: (k3_subset_1(A_142, k3_xboole_0(A_142, B_143))=k4_xboole_0(A_142, B_143))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1907])).
% 7.21/2.59  tff(c_380, plain, (![A_76, B_77]: (r1_tarski(k3_xboole_0(A_76, B_77), A_76))), inference(superposition, [status(thm), theory('equality')], [c_368, c_8])).
% 7.21/2.59  tff(c_1833, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k3_subset_1(A_76, k3_xboole_0(A_76, B_77)))), inference(resolution, [status(thm)], [c_380, c_1791])).
% 7.21/2.59  tff(c_2665, plain, (![A_76, B_77]: (k4_xboole_0(A_76, k3_xboole_0(A_76, B_77))=k4_xboole_0(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_1943, c_1833])).
% 7.21/2.59  tff(c_383, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_368])).
% 7.21/2.59  tff(c_2736, plain, (![A_174, B_175]: (k3_xboole_0(A_174, k4_xboole_0(A_174, B_175))=k4_xboole_0(A_174, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_2665, c_383])).
% 7.21/2.59  tff(c_18, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.21/2.59  tff(c_160, plain, (![A_59, B_60]: (k1_setfam_1(k2_tarski(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.21/2.59  tff(c_205, plain, (![A_67, B_68]: (k1_setfam_1(k2_tarski(A_67, B_68))=k3_xboole_0(B_68, A_67))), inference(superposition, [status(thm), theory('equality')], [c_18, c_160])).
% 7.21/2.59  tff(c_30, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.21/2.59  tff(c_211, plain, (![B_68, A_67]: (k3_xboole_0(B_68, A_67)=k3_xboole_0(A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_205, c_30])).
% 7.21/2.59  tff(c_527, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(B_68, A_67))=k4_xboole_0(A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_211, c_501])).
% 7.21/2.59  tff(c_2751, plain, (![A_174, B_175]: (k5_xboole_0(k4_xboole_0(A_174, B_175), k4_xboole_0(A_174, B_175))=k4_xboole_0(k4_xboole_0(A_174, B_175), A_174))), inference(superposition, [status(thm), theory('equality')], [c_2736, c_527])).
% 7.21/2.59  tff(c_2831, plain, (![A_176, B_177]: (k4_xboole_0(k4_xboole_0(A_176, B_177), A_176)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_537, c_2751])).
% 7.21/2.59  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.21/2.59  tff(c_2848, plain, (![A_176, B_177]: (k2_xboole_0(A_176, k4_xboole_0(A_176, B_177))=k5_xboole_0(A_176, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2831, c_16])).
% 7.21/2.59  tff(c_2922, plain, (![A_178, B_179]: (k2_xboole_0(A_178, k4_xboole_0(A_178, B_179))=A_178)), inference(demodulation, [status(thm), theory('equality')], [c_328, c_2848])).
% 7.21/2.59  tff(c_3004, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1063, c_2922])).
% 7.21/2.59  tff(c_2181, plain, (![A_149, B_150]: (k4_subset_1(u1_struct_0(A_149), B_150, k2_tops_1(A_149, B_150))=k2_pre_topc(A_149, B_150) | ~m1_subset_1(B_150, k1_zfmisc_1(u1_struct_0(A_149))) | ~l1_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.21/2.59  tff(c_2188, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2181])).
% 7.21/2.59  tff(c_2193, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2188])).
% 7.21/2.59  tff(c_40, plain, (![A_36, B_37]: (m1_subset_1(k2_tops_1(A_36, B_37), k1_zfmisc_1(u1_struct_0(A_36))) | ~m1_subset_1(B_37, k1_zfmisc_1(u1_struct_0(A_36))) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.21/2.59  tff(c_1745, plain, (![A_132, B_133, C_134]: (k4_subset_1(A_132, B_133, C_134)=k2_xboole_0(B_133, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(A_132)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.21/2.59  tff(c_10327, plain, (![A_277, B_278, B_279]: (k4_subset_1(u1_struct_0(A_277), B_278, k2_tops_1(A_277, B_279))=k2_xboole_0(B_278, k2_tops_1(A_277, B_279)) | ~m1_subset_1(B_278, k1_zfmisc_1(u1_struct_0(A_277))) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_277))) | ~l1_pre_topc(A_277))), inference(resolution, [status(thm)], [c_40, c_1745])).
% 7.21/2.59  tff(c_10334, plain, (![B_279]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_279))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_279)) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_10327])).
% 7.21/2.59  tff(c_10343, plain, (![B_280]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_280))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_280)) | ~m1_subset_1(B_280, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_10334])).
% 7.21/2.59  tff(c_10354, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_10343])).
% 7.21/2.59  tff(c_10360, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3004, c_2193, c_10354])).
% 7.21/2.59  tff(c_10362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1968, c_10360])).
% 7.21/2.59  tff(c_10363, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 7.21/2.59  tff(c_11303, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_11301, c_10363])).
% 7.21/2.59  tff(c_10364, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_54])).
% 7.21/2.59  tff(c_11530, plain, (![A_344, B_345]: (k2_pre_topc(A_344, B_345)=B_345 | ~v4_pre_topc(B_345, A_344) | ~m1_subset_1(B_345, k1_zfmisc_1(u1_struct_0(A_344))) | ~l1_pre_topc(A_344))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.21/2.59  tff(c_11537, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_11530])).
% 7.21/2.59  tff(c_11541, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_10364, c_11537])).
% 7.21/2.59  tff(c_12917, plain, (![A_399, B_400]: (k7_subset_1(u1_struct_0(A_399), k2_pre_topc(A_399, B_400), k1_tops_1(A_399, B_400))=k2_tops_1(A_399, B_400) | ~m1_subset_1(B_400, k1_zfmisc_1(u1_struct_0(A_399))) | ~l1_pre_topc(A_399))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.21/2.59  tff(c_12926, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11541, c_12917])).
% 7.21/2.59  tff(c_12930, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_11301, c_12926])).
% 7.21/2.59  tff(c_12932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11303, c_12930])).
% 7.21/2.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.59  
% 7.21/2.59  Inference rules
% 7.21/2.59  ----------------------
% 7.21/2.59  #Ref     : 0
% 7.21/2.59  #Sup     : 3174
% 7.21/2.59  #Fact    : 0
% 7.21/2.59  #Define  : 0
% 7.21/2.59  #Split   : 2
% 7.21/2.59  #Chain   : 0
% 7.21/2.59  #Close   : 0
% 7.21/2.59  
% 7.21/2.59  Ordering : KBO
% 7.21/2.59  
% 7.21/2.59  Simplification rules
% 7.21/2.59  ----------------------
% 7.21/2.59  #Subsume      : 63
% 7.21/2.59  #Demod        : 3724
% 7.21/2.59  #Tautology    : 2583
% 7.21/2.59  #SimpNegUnit  : 6
% 7.21/2.59  #BackRed      : 9
% 7.21/2.59  
% 7.21/2.59  #Partial instantiations: 0
% 7.21/2.59  #Strategies tried      : 1
% 7.21/2.59  
% 7.21/2.59  Timing (in seconds)
% 7.21/2.59  ----------------------
% 7.21/2.59  Preprocessing        : 0.33
% 7.21/2.59  Parsing              : 0.18
% 7.21/2.59  CNF conversion       : 0.02
% 7.21/2.59  Main loop            : 1.50
% 7.21/2.59  Inferencing          : 0.41
% 7.21/2.59  Reduction            : 0.75
% 7.21/2.59  Demodulation         : 0.63
% 7.21/2.59  BG Simplification    : 0.04
% 7.21/2.59  Subsumption          : 0.21
% 7.21/2.59  Abstraction          : 0.07
% 7.21/2.59  MUC search           : 0.00
% 7.21/2.59  Cooper               : 0.00
% 7.21/2.59  Total                : 1.87
% 7.21/2.59  Index Insertion      : 0.00
% 7.21/2.59  Index Deletion       : 0.00
% 7.21/2.59  Index Matching       : 0.00
% 7.21/2.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
