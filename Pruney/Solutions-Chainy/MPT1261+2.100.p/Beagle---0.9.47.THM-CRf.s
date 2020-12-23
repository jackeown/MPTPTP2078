%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:26 EST 2020

% Result     : Theorem 10.02s
% Output     : CNFRefutation 10.18s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 259 expanded)
%              Number of leaves         :   42 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          :  177 ( 453 expanded)
%              Number of equality atoms :   88 ( 168 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_92,axiom,(
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

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_19151,plain,(
    ! [A_408,B_409,C_410] :
      ( k7_subset_1(A_408,B_409,C_410) = k4_xboole_0(B_409,C_410)
      | ~ m1_subset_1(B_409,k1_zfmisc_1(A_408)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_19159,plain,(
    ! [C_410] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_410) = k4_xboole_0('#skF_2',C_410) ),
    inference(resolution,[status(thm)],[c_50,c_19151])).

tff(c_56,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_160,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1698,plain,(
    ! [B_143,A_144] :
      ( v4_pre_topc(B_143,A_144)
      | k2_pre_topc(A_144,B_143) != B_143
      | ~ v2_pre_topc(A_144)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1708,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1698])).

tff(c_1717,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_54,c_1708])).

tff(c_1718,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_1717])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_165,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_177,plain,(
    ! [A_27] : r1_tarski(k1_xboole_0,A_27) ),
    inference(resolution,[status(thm)],[c_30,c_165])).

tff(c_231,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_247,plain,(
    ! [A_66] :
      ( k1_xboole_0 = A_66
      | ~ r1_tarski(A_66,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_177,c_231])).

tff(c_262,plain,(
    ! [B_9] : k4_xboole_0(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_335,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_344,plain,(
    ! [B_9] : k5_xboole_0(B_9,k1_xboole_0) = k2_xboole_0(B_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_335])).

tff(c_350,plain,(
    ! [B_9] : k5_xboole_0(B_9,k1_xboole_0) = B_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_344])).

tff(c_552,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,B_98) = k3_subset_1(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_565,plain,(
    ! [A_99] : k4_xboole_0(A_99,k1_xboole_0) = k3_subset_1(A_99,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_552])).

tff(c_587,plain,(
    ! [A_99] : r1_tarski(k3_subset_1(A_99,k1_xboole_0),A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_14])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_179,plain,(
    ! [A_60,B_61] :
      ( k3_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_195,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_179])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_76,plain,(
    ! [B_52,A_53] : k2_xboole_0(B_52,A_53) = k2_xboole_0(A_53,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_53] : k2_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_10])).

tff(c_564,plain,(
    ! [A_27] : k4_xboole_0(A_27,k1_xboole_0) = k3_subset_1(A_27,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_552])).

tff(c_741,plain,(
    ! [A_104,B_105,C_106] : k4_xboole_0(k4_xboole_0(A_104,B_105),C_106) = k4_xboole_0(A_104,k2_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_793,plain,(
    ! [A_27,C_106] : k4_xboole_0(k3_subset_1(A_27,k1_xboole_0),C_106) = k4_xboole_0(A_27,k2_xboole_0(k1_xboole_0,C_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_741])).

tff(c_875,plain,(
    ! [A_109,C_110] : k4_xboole_0(k3_subset_1(A_109,k1_xboole_0),C_110) = k4_xboole_0(A_109,C_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_793])).

tff(c_946,plain,(
    ! [A_111,C_112] : r1_tarski(k4_xboole_0(A_111,C_112),k3_subset_1(A_111,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_14])).

tff(c_993,plain,(
    ! [A_113,B_114] : r1_tarski(k3_xboole_0(A_113,B_114),k3_subset_1(A_113,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_946])).

tff(c_1110,plain,(
    ! [B_120] : r1_tarski(B_120,k3_subset_1(B_120,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_993])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1112,plain,(
    ! [B_120] :
      ( k3_subset_1(B_120,k1_xboole_0) = B_120
      | ~ r1_tarski(k3_subset_1(B_120,k1_xboole_0),B_120) ) ),
    inference(resolution,[status(thm)],[c_1110,c_4])).

tff(c_1127,plain,(
    ! [B_120] : k3_subset_1(B_120,k1_xboole_0) = B_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_1112])).

tff(c_448,plain,(
    ! [A_87,B_88] :
      ( k3_subset_1(A_87,k3_subset_1(A_87,B_88)) = B_88
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_457,plain,(
    ! [A_27] : k3_subset_1(A_27,k3_subset_1(A_27,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_448])).

tff(c_1160,plain,(
    ! [A_27] : k3_subset_1(A_27,A_27) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1127,c_457])).

tff(c_62,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_196,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_62])).

tff(c_1091,plain,(
    ! [A_115,B_116,C_117] :
      ( k7_subset_1(A_115,B_116,C_117) = k4_xboole_0(B_116,C_117)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1132,plain,(
    ! [C_121] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_121) = k4_xboole_0('#skF_2',C_121) ),
    inference(resolution,[status(thm)],[c_50,c_1091])).

tff(c_1144,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_1132])).

tff(c_194,plain,(
    ! [A_8,B_9] : k3_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k4_xboole_0(A_8,B_9) ),
    inference(resolution,[status(thm)],[c_14,c_179])).

tff(c_1376,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1144,c_194])).

tff(c_1389,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_1376])).

tff(c_34,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(A_28,k1_zfmisc_1(B_29))
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1808,plain,(
    ! [B_150,A_151] :
      ( k4_xboole_0(B_150,A_151) = k3_subset_1(B_150,A_151)
      | ~ r1_tarski(A_151,B_150) ) ),
    inference(resolution,[status(thm)],[c_34,c_552])).

tff(c_1826,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_subset_1(A_8,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_14,c_1808])).

tff(c_2299,plain,(
    ! [A_167,B_168] : k3_subset_1(A_167,k4_xboole_0(A_167,B_168)) = k3_xboole_0(A_167,B_168) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1826])).

tff(c_455,plain,(
    ! [B_29,A_28] :
      ( k3_subset_1(B_29,k3_subset_1(B_29,A_28)) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(resolution,[status(thm)],[c_34,c_448])).

tff(c_2305,plain,(
    ! [A_167,B_168] :
      ( k3_subset_1(A_167,k3_xboole_0(A_167,B_168)) = k4_xboole_0(A_167,B_168)
      | ~ r1_tarski(k4_xboole_0(A_167,B_168),A_167) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2299,c_455])).

tff(c_2375,plain,(
    ! [A_169,B_170] : k3_subset_1(A_169,k3_xboole_0(A_169,B_170)) = k4_xboole_0(A_169,B_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2305])).

tff(c_2399,plain,(
    k3_subset_1(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1389,c_2375])).

tff(c_2423,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1160,c_2399])).

tff(c_20,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2666,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2423,c_20])).

tff(c_2679,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_350,c_2666])).

tff(c_1900,plain,(
    ! [A_153,B_154] :
      ( k4_subset_1(u1_struct_0(A_153),B_154,k2_tops_1(A_153,B_154)) = k2_pre_topc(A_153,B_154)
      | ~ m1_subset_1(B_154,k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1907,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_1900])).

tff(c_1915,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1907])).

tff(c_563,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_552])).

tff(c_626,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_18])).

tff(c_456,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_50,c_448])).

tff(c_629,plain,(
    r1_tarski(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_14])).

tff(c_1814,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_629,c_1808])).

tff(c_1832,plain,(
    k3_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_456,c_1814])).

tff(c_8227,plain,(
    ! [A_249,B_250,C_251] : k4_xboole_0(A_249,k2_xboole_0(k4_xboole_0(A_249,B_250),C_251)) = k4_xboole_0(k3_xboole_0(A_249,B_250),C_251) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_741])).

tff(c_8545,plain,(
    ! [A_252,B_253,C_254] : r1_tarski(k4_xboole_0(k3_xboole_0(A_252,B_253),C_254),A_252) ),
    inference(superposition,[status(thm),theory(equality)],[c_8227,c_14])).

tff(c_8696,plain,(
    ! [C_255] : r1_tarski(k4_xboole_0('#skF_2',C_255),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1832,c_8545])).

tff(c_8746,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1144,c_8696])).

tff(c_1531,plain,(
    ! [A_134,B_135,C_136] :
      ( k4_subset_1(A_134,B_135,C_136) = k2_xboole_0(B_135,C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(A_134))
      | ~ m1_subset_1(B_135,k1_zfmisc_1(A_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_17688,plain,(
    ! [B_336,B_337,A_338] :
      ( k4_subset_1(B_336,B_337,A_338) = k2_xboole_0(B_337,A_338)
      | ~ m1_subset_1(B_337,k1_zfmisc_1(B_336))
      | ~ r1_tarski(A_338,B_336) ) ),
    inference(resolution,[status(thm)],[c_34,c_1531])).

tff(c_17835,plain,(
    ! [A_342] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_342) = k2_xboole_0('#skF_2',A_342)
      | ~ r1_tarski(A_342,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_50,c_17688])).

tff(c_17868,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_8746,c_17835])).

tff(c_17916,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2679,c_1915,c_17868])).

tff(c_17918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1718,c_17916])).

tff(c_17919,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_19193,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19159,c_17919])).

tff(c_17920,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_19481,plain,(
    ! [A_425,B_426] :
      ( k2_pre_topc(A_425,B_426) = B_426
      | ~ v4_pre_topc(B_426,A_425)
      | ~ m1_subset_1(B_426,k1_zfmisc_1(u1_struct_0(A_425)))
      | ~ l1_pre_topc(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_19488,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_19481])).

tff(c_19496,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_17920,c_19488])).

tff(c_20781,plain,(
    ! [A_460,B_461] :
      ( k7_subset_1(u1_struct_0(A_460),k2_pre_topc(A_460,B_461),k1_tops_1(A_460,B_461)) = k2_tops_1(A_460,B_461)
      | ~ m1_subset_1(B_461,k1_zfmisc_1(u1_struct_0(A_460)))
      | ~ l1_pre_topc(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20790,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_19496,c_20781])).

tff(c_20794,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_19159,c_20790])).

tff(c_20796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19193,c_20794])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.02/3.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.02/3.80  
% 10.02/3.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.18/3.80  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 10.18/3.80  
% 10.18/3.80  %Foreground sorts:
% 10.18/3.80  
% 10.18/3.80  
% 10.18/3.80  %Background operators:
% 10.18/3.80  
% 10.18/3.80  
% 10.18/3.80  %Foreground operators:
% 10.18/3.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.18/3.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.18/3.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.18/3.80  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 10.18/3.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.18/3.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.18/3.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.18/3.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.18/3.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.18/3.80  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 10.18/3.80  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 10.18/3.80  tff('#skF_2', type, '#skF_2': $i).
% 10.18/3.80  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 10.18/3.80  tff('#skF_1', type, '#skF_1': $i).
% 10.18/3.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.18/3.80  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 10.18/3.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.18/3.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.18/3.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.18/3.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.18/3.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.18/3.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.18/3.80  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 10.18/3.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.18/3.80  
% 10.18/3.82  tff(f_132, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 10.18/3.82  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 10.18/3.82  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 10.18/3.82  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 10.18/3.82  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.18/3.82  tff(f_67, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 10.18/3.82  tff(f_71, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.18/3.82  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.18/3.82  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 10.18/3.82  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 10.18/3.82  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.18/3.82  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.18/3.82  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.18/3.82  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.18/3.82  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.18/3.82  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 10.18/3.82  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 10.18/3.82  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 10.18/3.82  tff(c_50, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.18/3.82  tff(c_19151, plain, (![A_408, B_409, C_410]: (k7_subset_1(A_408, B_409, C_410)=k4_xboole_0(B_409, C_410) | ~m1_subset_1(B_409, k1_zfmisc_1(A_408)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.18/3.82  tff(c_19159, plain, (![C_410]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_410)=k4_xboole_0('#skF_2', C_410))), inference(resolution, [status(thm)], [c_50, c_19151])).
% 10.18/3.82  tff(c_56, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.18/3.82  tff(c_160, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 10.18/3.82  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.18/3.82  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.18/3.82  tff(c_1698, plain, (![B_143, A_144]: (v4_pre_topc(B_143, A_144) | k2_pre_topc(A_144, B_143)!=B_143 | ~v2_pre_topc(A_144) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.18/3.82  tff(c_1708, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1698])).
% 10.18/3.82  tff(c_1717, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_54, c_1708])).
% 10.18/3.82  tff(c_1718, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_160, c_1717])).
% 10.18/3.82  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.18/3.82  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.18/3.82  tff(c_30, plain, (![A_27]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.18/3.82  tff(c_165, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.18/3.82  tff(c_177, plain, (![A_27]: (r1_tarski(k1_xboole_0, A_27))), inference(resolution, [status(thm)], [c_30, c_165])).
% 10.18/3.82  tff(c_231, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.18/3.82  tff(c_247, plain, (![A_66]: (k1_xboole_0=A_66 | ~r1_tarski(A_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_177, c_231])).
% 10.18/3.82  tff(c_262, plain, (![B_9]: (k4_xboole_0(k1_xboole_0, B_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_247])).
% 10.18/3.82  tff(c_335, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.18/3.82  tff(c_344, plain, (![B_9]: (k5_xboole_0(B_9, k1_xboole_0)=k2_xboole_0(B_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_262, c_335])).
% 10.18/3.82  tff(c_350, plain, (![B_9]: (k5_xboole_0(B_9, k1_xboole_0)=B_9)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_344])).
% 10.18/3.82  tff(c_552, plain, (![A_97, B_98]: (k4_xboole_0(A_97, B_98)=k3_subset_1(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.18/3.82  tff(c_565, plain, (![A_99]: (k4_xboole_0(A_99, k1_xboole_0)=k3_subset_1(A_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_552])).
% 10.18/3.82  tff(c_587, plain, (![A_99]: (r1_tarski(k3_subset_1(A_99, k1_xboole_0), A_99))), inference(superposition, [status(thm), theory('equality')], [c_565, c_14])).
% 10.18/3.82  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.18/3.82  tff(c_179, plain, (![A_60, B_61]: (k3_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.18/3.82  tff(c_195, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_179])).
% 10.18/3.82  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.18/3.82  tff(c_76, plain, (![B_52, A_53]: (k2_xboole_0(B_52, A_53)=k2_xboole_0(A_53, B_52))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.18/3.82  tff(c_92, plain, (![A_53]: (k2_xboole_0(k1_xboole_0, A_53)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_76, c_10])).
% 10.18/3.82  tff(c_564, plain, (![A_27]: (k4_xboole_0(A_27, k1_xboole_0)=k3_subset_1(A_27, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_552])).
% 10.18/3.82  tff(c_741, plain, (![A_104, B_105, C_106]: (k4_xboole_0(k4_xboole_0(A_104, B_105), C_106)=k4_xboole_0(A_104, k2_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.18/3.82  tff(c_793, plain, (![A_27, C_106]: (k4_xboole_0(k3_subset_1(A_27, k1_xboole_0), C_106)=k4_xboole_0(A_27, k2_xboole_0(k1_xboole_0, C_106)))), inference(superposition, [status(thm), theory('equality')], [c_564, c_741])).
% 10.18/3.82  tff(c_875, plain, (![A_109, C_110]: (k4_xboole_0(k3_subset_1(A_109, k1_xboole_0), C_110)=k4_xboole_0(A_109, C_110))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_793])).
% 10.18/3.82  tff(c_946, plain, (![A_111, C_112]: (r1_tarski(k4_xboole_0(A_111, C_112), k3_subset_1(A_111, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_875, c_14])).
% 10.18/3.82  tff(c_993, plain, (![A_113, B_114]: (r1_tarski(k3_xboole_0(A_113, B_114), k3_subset_1(A_113, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_946])).
% 10.18/3.82  tff(c_1110, plain, (![B_120]: (r1_tarski(B_120, k3_subset_1(B_120, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_195, c_993])).
% 10.18/3.82  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.18/3.82  tff(c_1112, plain, (![B_120]: (k3_subset_1(B_120, k1_xboole_0)=B_120 | ~r1_tarski(k3_subset_1(B_120, k1_xboole_0), B_120))), inference(resolution, [status(thm)], [c_1110, c_4])).
% 10.18/3.82  tff(c_1127, plain, (![B_120]: (k3_subset_1(B_120, k1_xboole_0)=B_120)), inference(demodulation, [status(thm), theory('equality')], [c_587, c_1112])).
% 10.18/3.82  tff(c_448, plain, (![A_87, B_88]: (k3_subset_1(A_87, k3_subset_1(A_87, B_88))=B_88 | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.18/3.82  tff(c_457, plain, (![A_27]: (k3_subset_1(A_27, k3_subset_1(A_27, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_448])).
% 10.18/3.82  tff(c_1160, plain, (![A_27]: (k3_subset_1(A_27, A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1127, c_457])).
% 10.18/3.82  tff(c_62, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.18/3.82  tff(c_196, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_160, c_62])).
% 10.18/3.82  tff(c_1091, plain, (![A_115, B_116, C_117]: (k7_subset_1(A_115, B_116, C_117)=k4_xboole_0(B_116, C_117) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.18/3.82  tff(c_1132, plain, (![C_121]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_121)=k4_xboole_0('#skF_2', C_121))), inference(resolution, [status(thm)], [c_50, c_1091])).
% 10.18/3.82  tff(c_1144, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_196, c_1132])).
% 10.18/3.82  tff(c_194, plain, (![A_8, B_9]: (k3_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k4_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_14, c_179])).
% 10.18/3.82  tff(c_1376, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1144, c_194])).
% 10.18/3.82  tff(c_1389, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1144, c_1376])).
% 10.18/3.82  tff(c_34, plain, (![A_28, B_29]: (m1_subset_1(A_28, k1_zfmisc_1(B_29)) | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.18/3.82  tff(c_1808, plain, (![B_150, A_151]: (k4_xboole_0(B_150, A_151)=k3_subset_1(B_150, A_151) | ~r1_tarski(A_151, B_150))), inference(resolution, [status(thm)], [c_34, c_552])).
% 10.18/3.82  tff(c_1826, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_subset_1(A_8, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_14, c_1808])).
% 10.18/3.82  tff(c_2299, plain, (![A_167, B_168]: (k3_subset_1(A_167, k4_xboole_0(A_167, B_168))=k3_xboole_0(A_167, B_168))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1826])).
% 10.18/3.82  tff(c_455, plain, (![B_29, A_28]: (k3_subset_1(B_29, k3_subset_1(B_29, A_28))=A_28 | ~r1_tarski(A_28, B_29))), inference(resolution, [status(thm)], [c_34, c_448])).
% 10.18/3.82  tff(c_2305, plain, (![A_167, B_168]: (k3_subset_1(A_167, k3_xboole_0(A_167, B_168))=k4_xboole_0(A_167, B_168) | ~r1_tarski(k4_xboole_0(A_167, B_168), A_167))), inference(superposition, [status(thm), theory('equality')], [c_2299, c_455])).
% 10.18/3.82  tff(c_2375, plain, (![A_169, B_170]: (k3_subset_1(A_169, k3_xboole_0(A_169, B_170))=k4_xboole_0(A_169, B_170))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2305])).
% 10.18/3.82  tff(c_2399, plain, (k3_subset_1(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1389, c_2375])).
% 10.18/3.82  tff(c_2423, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1160, c_2399])).
% 10.18/3.82  tff(c_20, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.18/3.82  tff(c_2666, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2423, c_20])).
% 10.18/3.82  tff(c_2679, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_350, c_2666])).
% 10.18/3.82  tff(c_1900, plain, (![A_153, B_154]: (k4_subset_1(u1_struct_0(A_153), B_154, k2_tops_1(A_153, B_154))=k2_pre_topc(A_153, B_154) | ~m1_subset_1(B_154, k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_120])).
% 10.18/3.82  tff(c_1907, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_1900])).
% 10.18/3.82  tff(c_1915, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1907])).
% 10.18/3.82  tff(c_563, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_50, c_552])).
% 10.18/3.82  tff(c_626, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_563, c_18])).
% 10.18/3.82  tff(c_456, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_50, c_448])).
% 10.18/3.82  tff(c_629, plain, (r1_tarski(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_563, c_14])).
% 10.18/3.82  tff(c_1814, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_629, c_1808])).
% 10.18/3.82  tff(c_1832, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_626, c_456, c_1814])).
% 10.18/3.82  tff(c_8227, plain, (![A_249, B_250, C_251]: (k4_xboole_0(A_249, k2_xboole_0(k4_xboole_0(A_249, B_250), C_251))=k4_xboole_0(k3_xboole_0(A_249, B_250), C_251))), inference(superposition, [status(thm), theory('equality')], [c_18, c_741])).
% 10.18/3.82  tff(c_8545, plain, (![A_252, B_253, C_254]: (r1_tarski(k4_xboole_0(k3_xboole_0(A_252, B_253), C_254), A_252))), inference(superposition, [status(thm), theory('equality')], [c_8227, c_14])).
% 10.18/3.82  tff(c_8696, plain, (![C_255]: (r1_tarski(k4_xboole_0('#skF_2', C_255), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1832, c_8545])).
% 10.18/3.82  tff(c_8746, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1144, c_8696])).
% 10.18/3.82  tff(c_1531, plain, (![A_134, B_135, C_136]: (k4_subset_1(A_134, B_135, C_136)=k2_xboole_0(B_135, C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(A_134)) | ~m1_subset_1(B_135, k1_zfmisc_1(A_134)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.18/3.82  tff(c_17688, plain, (![B_336, B_337, A_338]: (k4_subset_1(B_336, B_337, A_338)=k2_xboole_0(B_337, A_338) | ~m1_subset_1(B_337, k1_zfmisc_1(B_336)) | ~r1_tarski(A_338, B_336))), inference(resolution, [status(thm)], [c_34, c_1531])).
% 10.18/3.82  tff(c_17835, plain, (![A_342]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_342)=k2_xboole_0('#skF_2', A_342) | ~r1_tarski(A_342, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_50, c_17688])).
% 10.18/3.82  tff(c_17868, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_8746, c_17835])).
% 10.18/3.82  tff(c_17916, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2679, c_1915, c_17868])).
% 10.18/3.82  tff(c_17918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1718, c_17916])).
% 10.18/3.82  tff(c_17919, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_56])).
% 10.18/3.82  tff(c_19193, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19159, c_17919])).
% 10.18/3.82  tff(c_17920, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 10.18/3.82  tff(c_19481, plain, (![A_425, B_426]: (k2_pre_topc(A_425, B_426)=B_426 | ~v4_pre_topc(B_426, A_425) | ~m1_subset_1(B_426, k1_zfmisc_1(u1_struct_0(A_425))) | ~l1_pre_topc(A_425))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.18/3.82  tff(c_19488, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_19481])).
% 10.18/3.82  tff(c_19496, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_17920, c_19488])).
% 10.18/3.82  tff(c_20781, plain, (![A_460, B_461]: (k7_subset_1(u1_struct_0(A_460), k2_pre_topc(A_460, B_461), k1_tops_1(A_460, B_461))=k2_tops_1(A_460, B_461) | ~m1_subset_1(B_461, k1_zfmisc_1(u1_struct_0(A_460))) | ~l1_pre_topc(A_460))), inference(cnfTransformation, [status(thm)], [f_113])).
% 10.18/3.82  tff(c_20790, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_19496, c_20781])).
% 10.18/3.82  tff(c_20794, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_19159, c_20790])).
% 10.18/3.82  tff(c_20796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19193, c_20794])).
% 10.18/3.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.18/3.82  
% 10.18/3.82  Inference rules
% 10.18/3.82  ----------------------
% 10.18/3.82  #Ref     : 0
% 10.18/3.82  #Sup     : 5142
% 10.18/3.82  #Fact    : 0
% 10.18/3.82  #Define  : 0
% 10.18/3.82  #Split   : 3
% 10.18/3.82  #Chain   : 0
% 10.18/3.82  #Close   : 0
% 10.18/3.82  
% 10.18/3.82  Ordering : KBO
% 10.18/3.82  
% 10.18/3.82  Simplification rules
% 10.18/3.82  ----------------------
% 10.18/3.82  #Subsume      : 69
% 10.18/3.82  #Demod        : 5294
% 10.18/3.82  #Tautology    : 3623
% 10.18/3.82  #SimpNegUnit  : 5
% 10.18/3.82  #BackRed      : 35
% 10.18/3.83  
% 10.18/3.83  #Partial instantiations: 0
% 10.18/3.83  #Strategies tried      : 1
% 10.18/3.83  
% 10.18/3.83  Timing (in seconds)
% 10.18/3.83  ----------------------
% 10.18/3.83  Preprocessing        : 0.40
% 10.18/3.83  Parsing              : 0.22
% 10.18/3.83  CNF conversion       : 0.02
% 10.18/3.83  Main loop            : 2.59
% 10.18/3.83  Inferencing          : 0.62
% 10.18/3.83  Reduction            : 1.32
% 10.18/3.83  Demodulation         : 1.12
% 10.18/3.83  BG Simplification    : 0.07
% 10.18/3.83  Subsumption          : 0.42
% 10.18/3.83  Abstraction          : 0.11
% 10.18/3.83  MUC search           : 0.00
% 10.18/3.83  Cooper               : 0.00
% 10.18/3.83  Total                : 3.04
% 10.18/3.83  Index Insertion      : 0.00
% 10.18/3.83  Index Deletion       : 0.00
% 10.18/3.83  Index Matching       : 0.00
% 10.18/3.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
