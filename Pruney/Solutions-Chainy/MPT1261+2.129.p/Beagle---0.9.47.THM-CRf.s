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
% DateTime   : Thu Dec  3 10:21:30 EST 2020

% Result     : Theorem 5.54s
% Output     : CNFRefutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 205 expanded)
%              Number of leaves         :   34 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  158 ( 405 expanded)
%              Number of equality atoms :   47 ( 106 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3600,plain,(
    ! [A_213,B_214,C_215] :
      ( k7_subset_1(A_213,B_214,C_215) = k4_xboole_0(B_214,C_215)
      | ~ m1_subset_1(B_214,k1_zfmisc_1(A_213)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3606,plain,(
    ! [C_215] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_215) = k4_xboole_0('#skF_2',C_215) ),
    inference(resolution,[status(thm)],[c_30,c_3600])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_160,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1099,plain,(
    ! [A_114,B_115] :
      ( k4_subset_1(u1_struct_0(A_114),B_115,k2_tops_1(A_114,B_115)) = k2_pre_topc(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1104,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1099])).

tff(c_1108,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1104])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_115,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_387,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_471,plain,(
    ! [C_88] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_88) = k4_xboole_0('#skF_2',C_88) ),
    inference(resolution,[status(thm)],[c_30,c_387])).

tff(c_483,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_471])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_41,B_42] : k2_xboole_0(k4_xboole_0(A_41,B_42),A_41) = A_41 ),
    inference(resolution,[status(thm)],[c_10,c_77])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_41,B_42] : k2_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_2])).

tff(c_793,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_88])).

tff(c_118,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_122,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_118])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_126,plain,(
    k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_122,c_6])).

tff(c_145,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(B_53,C_52)
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_161,plain,(
    ! [A_55,A_56,B_57] :
      ( r1_tarski(A_55,A_56)
      | ~ r1_tarski(A_55,k4_xboole_0(A_56,B_57)) ) ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_166,plain,(
    ! [A_56,B_57,B_11] : r1_tarski(k4_xboole_0(k4_xboole_0(A_56,B_57),B_11),A_56) ),
    inference(resolution,[status(thm)],[c_10,c_161])).

tff(c_212,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,k2_xboole_0(B_68,C_69))
      | ~ r1_tarski(k4_xboole_0(A_67,B_68),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_346,plain,(
    ! [A_76,B_77,B_78] : r1_tarski(k4_xboole_0(A_76,B_77),k2_xboole_0(B_78,A_76)) ),
    inference(resolution,[status(thm)],[c_166,c_212])).

tff(c_417,plain,(
    ! [A_84,B_85,B_86] : r1_tarski(k4_xboole_0(A_84,B_85),k2_xboole_0(A_84,B_86)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_346])).

tff(c_437,plain,(
    ! [B_85] : r1_tarski(k4_xboole_0('#skF_2',B_85),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_417])).

tff(c_766,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_437])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_893,plain,(
    ! [A_102,B_103,C_104] :
      ( k4_subset_1(A_102,B_103,C_104) = k2_xboole_0(B_103,C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(A_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2831,plain,(
    ! [B_151,B_152,A_153] :
      ( k4_subset_1(B_151,B_152,A_153) = k2_xboole_0(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(B_151))
      | ~ r1_tarski(A_153,B_151) ) ),
    inference(resolution,[status(thm)],[c_20,c_893])).

tff(c_3079,plain,(
    ! [A_156] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_156) = k2_xboole_0('#skF_2',A_156)
      | ~ r1_tarski(A_156,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_2831])).

tff(c_3082,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_766,c_3079])).

tff(c_3105,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1108,c_793,c_3082])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_620,plain,(
    ! [A_94,B_95] :
      ( v4_pre_topc(k2_pre_topc(A_94,B_95),A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_625,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_620])).

tff(c_629,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_625])).

tff(c_3116,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3105,c_629])).

tff(c_3118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_3116])).

tff(c_3119,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3119,c_115])).

tff(c_3304,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_3309,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3304,c_36])).

tff(c_3726,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3606,c_3309])).

tff(c_4256,plain,(
    ! [A_247,B_248] :
      ( k4_subset_1(u1_struct_0(A_247),B_248,k2_tops_1(A_247,B_248)) = k2_pre_topc(A_247,B_248)
      | ~ m1_subset_1(B_248,k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ l1_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4261,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4256])).

tff(c_4265,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4261])).

tff(c_4023,plain,(
    ! [A_237,B_238] :
      ( r1_tarski(k2_tops_1(A_237,B_238),B_238)
      | ~ v4_pre_topc(B_238,A_237)
      | ~ m1_subset_1(B_238,k1_zfmisc_1(u1_struct_0(A_237)))
      | ~ l1_pre_topc(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4028,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4023])).

tff(c_4032,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3304,c_4028])).

tff(c_4039,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_4032,c_6])).

tff(c_4067,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_4039,c_2])).

tff(c_3310,plain,(
    ! [A_177,B_178] :
      ( r1_tarski(A_177,B_178)
      | ~ m1_subset_1(A_177,k1_zfmisc_1(B_178)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_3314,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_3310])).

tff(c_3318,plain,(
    k2_xboole_0('#skF_2',u1_struct_0('#skF_1')) = u1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3314,c_6])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(A_7,C_9)
      | ~ r1_tarski(B_8,C_9)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4118,plain,(
    ! [A_239] :
      ( r1_tarski(A_239,'#skF_2')
      | ~ r1_tarski(A_239,k2_tops_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_4032,c_8])).

tff(c_4138,plain,(
    ! [B_240] : r1_tarski(k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),B_240),'#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_4118])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_tarski(A_12,k2_xboole_0(B_13,C_14))
      | ~ r1_tarski(k4_xboole_0(A_12,B_13),C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4158,plain,(
    ! [B_244] : r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(B_244,'#skF_2')) ),
    inference(resolution,[status(thm)],[c_4138,c_12])).

tff(c_4209,plain,(
    ! [A_246] : r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0('#skF_2',A_246)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_4158])).

tff(c_4226,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3318,c_4209])).

tff(c_4151,plain,(
    ! [A_241,B_242,C_243] :
      ( k4_subset_1(A_241,B_242,C_243) = k2_xboole_0(B_242,C_243)
      | ~ m1_subset_1(C_243,k1_zfmisc_1(A_241))
      | ~ m1_subset_1(B_242,k1_zfmisc_1(A_241)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6687,plain,(
    ! [B_292,B_293,A_294] :
      ( k4_subset_1(B_292,B_293,A_294) = k2_xboole_0(B_293,A_294)
      | ~ m1_subset_1(B_293,k1_zfmisc_1(B_292))
      | ~ r1_tarski(A_294,B_292) ) ),
    inference(resolution,[status(thm)],[c_20,c_4151])).

tff(c_6761,plain,(
    ! [A_296] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_296) = k2_xboole_0('#skF_2',A_296)
      | ~ r1_tarski(A_296,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_6687])).

tff(c_6767,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4226,c_6761])).

tff(c_6792,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4265,c_4067,c_6767])).

tff(c_24,plain,(
    ! [A_25,B_27] :
      ( k7_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,B_27),k1_tops_1(A_25,B_27)) = k2_tops_1(A_25,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6811,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6792,c_24])).

tff(c_6817,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3606,c_6811])).

tff(c_6819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3726,c_6817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.54/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.22  
% 5.54/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.22  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.54/2.22  
% 5.54/2.22  %Foreground sorts:
% 5.54/2.22  
% 5.54/2.22  
% 5.54/2.22  %Background operators:
% 5.54/2.22  
% 5.54/2.22  
% 5.54/2.22  %Foreground operators:
% 5.54/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.54/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.54/2.22  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.54/2.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.54/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.54/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.54/2.22  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.54/2.22  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.54/2.22  tff('#skF_2', type, '#skF_2': $i).
% 5.54/2.22  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.54/2.22  tff('#skF_1', type, '#skF_1': $i).
% 5.54/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.54/2.22  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.54/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.54/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.54/2.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.54/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.54/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.54/2.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.54/2.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.54/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.54/2.22  
% 5.54/2.24  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.54/2.24  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.54/2.24  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.54/2.24  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.54/2.24  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.54/2.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.54/2.24  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.54/2.24  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.54/2.24  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.54/2.24  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.54/2.24  tff(f_67, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tops_1)).
% 5.54/2.24  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 5.54/2.24  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 5.54/2.24  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.54/2.24  tff(c_3600, plain, (![A_213, B_214, C_215]: (k7_subset_1(A_213, B_214, C_215)=k4_xboole_0(B_214, C_215) | ~m1_subset_1(B_214, k1_zfmisc_1(A_213)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.54/2.24  tff(c_3606, plain, (![C_215]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_215)=k4_xboole_0('#skF_2', C_215))), inference(resolution, [status(thm)], [c_30, c_3600])).
% 5.54/2.24  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.54/2.24  tff(c_160, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 5.54/2.24  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.54/2.24  tff(c_1099, plain, (![A_114, B_115]: (k4_subset_1(u1_struct_0(A_114), B_115, k2_tops_1(A_114, B_115))=k2_pre_topc(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_114))) | ~l1_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.54/2.24  tff(c_1104, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1099])).
% 5.54/2.24  tff(c_1108, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1104])).
% 5.54/2.24  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.54/2.24  tff(c_115, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 5.54/2.24  tff(c_387, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.54/2.24  tff(c_471, plain, (![C_88]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_88)=k4_xboole_0('#skF_2', C_88))), inference(resolution, [status(thm)], [c_30, c_387])).
% 5.54/2.24  tff(c_483, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_115, c_471])).
% 5.54/2.24  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.54/2.24  tff(c_77, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.54/2.24  tff(c_82, plain, (![A_41, B_42]: (k2_xboole_0(k4_xboole_0(A_41, B_42), A_41)=A_41)), inference(resolution, [status(thm)], [c_10, c_77])).
% 5.54/2.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.54/2.24  tff(c_88, plain, (![A_41, B_42]: (k2_xboole_0(A_41, k4_xboole_0(A_41, B_42))=A_41)), inference(superposition, [status(thm), theory('equality')], [c_82, c_2])).
% 5.54/2.24  tff(c_793, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_483, c_88])).
% 5.54/2.24  tff(c_118, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.54/2.24  tff(c_122, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_118])).
% 5.54/2.24  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.54/2.24  tff(c_126, plain, (k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))=u1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_122, c_6])).
% 5.54/2.24  tff(c_145, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(B_53, C_52) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.54/2.24  tff(c_161, plain, (![A_55, A_56, B_57]: (r1_tarski(A_55, A_56) | ~r1_tarski(A_55, k4_xboole_0(A_56, B_57)))), inference(resolution, [status(thm)], [c_10, c_145])).
% 5.54/2.24  tff(c_166, plain, (![A_56, B_57, B_11]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_56, B_57), B_11), A_56))), inference(resolution, [status(thm)], [c_10, c_161])).
% 5.54/2.24  tff(c_212, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, k2_xboole_0(B_68, C_69)) | ~r1_tarski(k4_xboole_0(A_67, B_68), C_69))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.54/2.24  tff(c_346, plain, (![A_76, B_77, B_78]: (r1_tarski(k4_xboole_0(A_76, B_77), k2_xboole_0(B_78, A_76)))), inference(resolution, [status(thm)], [c_166, c_212])).
% 5.54/2.24  tff(c_417, plain, (![A_84, B_85, B_86]: (r1_tarski(k4_xboole_0(A_84, B_85), k2_xboole_0(A_84, B_86)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_346])).
% 5.54/2.24  tff(c_437, plain, (![B_85]: (r1_tarski(k4_xboole_0('#skF_2', B_85), u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_126, c_417])).
% 5.54/2.24  tff(c_766, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_437])).
% 5.54/2.24  tff(c_20, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.54/2.24  tff(c_893, plain, (![A_102, B_103, C_104]: (k4_subset_1(A_102, B_103, C_104)=k2_xboole_0(B_103, C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(A_102)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.54/2.24  tff(c_2831, plain, (![B_151, B_152, A_153]: (k4_subset_1(B_151, B_152, A_153)=k2_xboole_0(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(B_151)) | ~r1_tarski(A_153, B_151))), inference(resolution, [status(thm)], [c_20, c_893])).
% 5.54/2.24  tff(c_3079, plain, (![A_156]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_156)=k2_xboole_0('#skF_2', A_156) | ~r1_tarski(A_156, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_2831])).
% 5.54/2.24  tff(c_3082, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_766, c_3079])).
% 5.54/2.24  tff(c_3105, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1108, c_793, c_3082])).
% 5.54/2.24  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.54/2.24  tff(c_620, plain, (![A_94, B_95]: (v4_pre_topc(k2_pre_topc(A_94, B_95), A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.54/2.24  tff(c_625, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_620])).
% 5.54/2.24  tff(c_629, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_625])).
% 5.54/2.24  tff(c_3116, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3105, c_629])).
% 5.54/2.24  tff(c_3118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_3116])).
% 5.54/2.24  tff(c_3119, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 5.54/2.24  tff(c_3303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3119, c_115])).
% 5.54/2.24  tff(c_3304, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 5.54/2.24  tff(c_3309, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3304, c_36])).
% 5.54/2.24  tff(c_3726, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3606, c_3309])).
% 5.54/2.24  tff(c_4256, plain, (![A_247, B_248]: (k4_subset_1(u1_struct_0(A_247), B_248, k2_tops_1(A_247, B_248))=k2_pre_topc(A_247, B_248) | ~m1_subset_1(B_248, k1_zfmisc_1(u1_struct_0(A_247))) | ~l1_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.54/2.24  tff(c_4261, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4256])).
% 5.54/2.24  tff(c_4265, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4261])).
% 5.54/2.24  tff(c_4023, plain, (![A_237, B_238]: (r1_tarski(k2_tops_1(A_237, B_238), B_238) | ~v4_pre_topc(B_238, A_237) | ~m1_subset_1(B_238, k1_zfmisc_1(u1_struct_0(A_237))) | ~l1_pre_topc(A_237))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.54/2.24  tff(c_4028, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4023])).
% 5.54/2.24  tff(c_4032, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3304, c_4028])).
% 5.54/2.24  tff(c_4039, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_4032, c_6])).
% 5.54/2.24  tff(c_4067, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_4039, c_2])).
% 5.54/2.24  tff(c_3310, plain, (![A_177, B_178]: (r1_tarski(A_177, B_178) | ~m1_subset_1(A_177, k1_zfmisc_1(B_178)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.54/2.24  tff(c_3314, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_3310])).
% 5.54/2.24  tff(c_3318, plain, (k2_xboole_0('#skF_2', u1_struct_0('#skF_1'))=u1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3314, c_6])).
% 5.54/2.24  tff(c_8, plain, (![A_7, C_9, B_8]: (r1_tarski(A_7, C_9) | ~r1_tarski(B_8, C_9) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.54/2.24  tff(c_4118, plain, (![A_239]: (r1_tarski(A_239, '#skF_2') | ~r1_tarski(A_239, k2_tops_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_4032, c_8])).
% 5.54/2.24  tff(c_4138, plain, (![B_240]: (r1_tarski(k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), B_240), '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_4118])).
% 5.54/2.24  tff(c_12, plain, (![A_12, B_13, C_14]: (r1_tarski(A_12, k2_xboole_0(B_13, C_14)) | ~r1_tarski(k4_xboole_0(A_12, B_13), C_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.54/2.24  tff(c_4158, plain, (![B_244]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(B_244, '#skF_2')))), inference(resolution, [status(thm)], [c_4138, c_12])).
% 5.54/2.24  tff(c_4209, plain, (![A_246]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0('#skF_2', A_246)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_4158])).
% 5.54/2.24  tff(c_4226, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3318, c_4209])).
% 5.54/2.24  tff(c_4151, plain, (![A_241, B_242, C_243]: (k4_subset_1(A_241, B_242, C_243)=k2_xboole_0(B_242, C_243) | ~m1_subset_1(C_243, k1_zfmisc_1(A_241)) | ~m1_subset_1(B_242, k1_zfmisc_1(A_241)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.54/2.24  tff(c_6687, plain, (![B_292, B_293, A_294]: (k4_subset_1(B_292, B_293, A_294)=k2_xboole_0(B_293, A_294) | ~m1_subset_1(B_293, k1_zfmisc_1(B_292)) | ~r1_tarski(A_294, B_292))), inference(resolution, [status(thm)], [c_20, c_4151])).
% 5.54/2.24  tff(c_6761, plain, (![A_296]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_296)=k2_xboole_0('#skF_2', A_296) | ~r1_tarski(A_296, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_6687])).
% 5.54/2.24  tff(c_6767, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4226, c_6761])).
% 5.54/2.24  tff(c_6792, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4265, c_4067, c_6767])).
% 5.54/2.24  tff(c_24, plain, (![A_25, B_27]: (k7_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, B_27), k1_tops_1(A_25, B_27))=k2_tops_1(A_25, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.54/2.24  tff(c_6811, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6792, c_24])).
% 5.54/2.24  tff(c_6817, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3606, c_6811])).
% 5.54/2.24  tff(c_6819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3726, c_6817])).
% 5.54/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.24  
% 5.54/2.24  Inference rules
% 5.54/2.24  ----------------------
% 5.54/2.24  #Ref     : 0
% 5.54/2.24  #Sup     : 1682
% 5.54/2.24  #Fact    : 0
% 5.54/2.24  #Define  : 0
% 5.54/2.24  #Split   : 2
% 5.54/2.24  #Chain   : 0
% 5.54/2.24  #Close   : 0
% 5.54/2.24  
% 5.54/2.24  Ordering : KBO
% 5.54/2.24  
% 5.54/2.24  Simplification rules
% 5.54/2.24  ----------------------
% 5.54/2.24  #Subsume      : 79
% 5.54/2.24  #Demod        : 1478
% 5.54/2.24  #Tautology    : 1134
% 5.54/2.24  #SimpNegUnit  : 3
% 5.54/2.24  #BackRed      : 5
% 5.54/2.24  
% 5.54/2.24  #Partial instantiations: 0
% 5.54/2.24  #Strategies tried      : 1
% 5.54/2.24  
% 5.54/2.24  Timing (in seconds)
% 5.54/2.24  ----------------------
% 5.89/2.24  Preprocessing        : 0.42
% 5.89/2.24  Parsing              : 0.22
% 5.89/2.24  CNF conversion       : 0.03
% 5.89/2.24  Main loop            : 1.05
% 5.89/2.24  Inferencing          : 0.31
% 5.89/2.24  Reduction            : 0.48
% 5.89/2.24  Demodulation         : 0.40
% 5.89/2.24  BG Simplification    : 0.04
% 5.89/2.24  Subsumption          : 0.16
% 5.89/2.24  Abstraction          : 0.05
% 5.89/2.24  MUC search           : 0.00
% 5.89/2.24  Cooper               : 0.00
% 5.89/2.24  Total                : 1.51
% 5.89/2.24  Index Insertion      : 0.00
% 5.89/2.24  Index Deletion       : 0.00
% 5.89/2.24  Index Matching       : 0.00
% 5.89/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
