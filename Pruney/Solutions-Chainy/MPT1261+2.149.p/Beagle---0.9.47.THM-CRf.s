%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:32 EST 2020

% Result     : Theorem 5.19s
% Output     : CNFRefutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 166 expanded)
%              Number of leaves         :   38 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  143 ( 295 expanded)
%              Number of equality atoms :   68 ( 110 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_72,axiom,(
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

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_85,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_6471,plain,(
    ! [A_232,B_233,C_234] :
      ( k7_subset_1(A_232,B_233,C_234) = k4_xboole_0(B_233,C_234)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(A_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6474,plain,(
    ! [C_234] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_234) = k4_xboole_0('#skF_2',C_234) ),
    inference(resolution,[status(thm)],[c_34,c_6471])).

tff(c_40,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_112,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1387,plain,(
    ! [B_115,A_116] :
      ( v4_pre_topc(B_115,A_116)
      | k2_pre_topc(A_116,B_115) != B_115
      | ~ v2_pre_topc(A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1393,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1387])).

tff(c_1397,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_1393])).

tff(c_1398,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1397])).

tff(c_492,plain,(
    ! [A_69,B_70,C_71] :
      ( k7_subset_1(A_69,B_70,C_71) = k4_xboole_0(B_70,C_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_690,plain,(
    ! [C_79] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_79) = k4_xboole_0('#skF_2',C_79) ),
    inference(resolution,[status(thm)],[c_34,c_492])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_256,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_46])).

tff(c_696,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_256])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [A_8,B_9] : k3_xboole_0(k4_xboole_0(A_8,B_9),A_8) = k4_xboole_0(A_8,B_9) ),
    inference(resolution,[status(thm)],[c_10,c_103])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_395,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(A_62,k2_xboole_0(B_63,C_64))
      | ~ r1_tarski(k4_xboole_0(A_62,B_63),C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_421,plain,(
    ! [A_65,B_66] : r1_tarski(A_65,k2_xboole_0(B_66,A_65)) ),
    inference(resolution,[status(thm)],[c_10,c_395])).

tff(c_437,plain,(
    ! [A_67] : r1_tarski(k1_xboole_0,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_421])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_444,plain,(
    ! [A_68] : k3_xboole_0(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_437,c_8])).

tff(c_466,plain,(
    ! [A_68] : k3_xboole_0(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_2])).

tff(c_14,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_122,plain,(
    ! [A_46,B_47] : k4_xboole_0(A_46,k4_xboole_0(A_46,B_47)) = k3_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_140,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_122])).

tff(c_65,plain,(
    ! [A_38,B_39] : r1_tarski(k4_xboole_0(A_38,B_39),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_65])).

tff(c_110,plain,(
    ! [A_12] : k3_xboole_0(A_12,A_12) = A_12 ),
    inference(resolution,[status(thm)],[c_68,c_103])).

tff(c_308,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_317,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k4_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_308])).

tff(c_326,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_317])).

tff(c_496,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_326])).

tff(c_143,plain,(
    ! [A_48,B_49] : r1_tarski(k3_xboole_0(A_48,B_49),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_10])).

tff(c_1224,plain,(
    ! [A_111,B_112] : k3_xboole_0(k3_xboole_0(A_111,B_112),A_111) = k3_xboole_0(A_111,B_112) ),
    inference(resolution,[status(thm)],[c_143,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1240,plain,(
    ! [A_111,B_112] : k5_xboole_0(k3_xboole_0(A_111,B_112),k3_xboole_0(A_111,B_112)) = k4_xboole_0(k3_xboole_0(A_111,B_112),A_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_4])).

tff(c_1311,plain,(
    ! [A_113,B_114] : k4_xboole_0(k3_xboole_0(A_113,B_114),A_113) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_1240])).

tff(c_1496,plain,(
    ! [A_119,B_120] : k4_xboole_0(k3_xboole_0(A_119,B_120),B_120) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1311])).

tff(c_1583,plain,(
    ! [A_121,B_122] : k4_xboole_0(k4_xboole_0(A_121,B_122),A_121) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_1496])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1600,plain,(
    ! [A_121,B_122] : k2_xboole_0(A_121,k4_xboole_0(A_121,B_122)) = k2_xboole_0(A_121,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1583,c_12])).

tff(c_1784,plain,(
    ! [A_127,B_128] : k2_xboole_0(A_127,k4_xboole_0(A_127,B_128)) = A_127 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1600])).

tff(c_1851,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_696,c_1784])).

tff(c_1775,plain,(
    ! [A_125,B_126] :
      ( k4_subset_1(u1_struct_0(A_125),B_126,k2_tops_1(A_125,B_126)) = k2_pre_topc(A_125,B_126)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1779,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1775])).

tff(c_1783,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1779])).

tff(c_28,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k2_tops_1(A_27,B_28),k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1089,plain,(
    ! [A_100,B_101,C_102] :
      ( k4_subset_1(A_100,B_101,C_102) = k2_xboole_0(B_101,C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(A_100))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5852,plain,(
    ! [A_199,B_200,B_201] :
      ( k4_subset_1(u1_struct_0(A_199),B_200,k2_tops_1(A_199,B_201)) = k2_xboole_0(B_200,k2_tops_1(A_199,B_201))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(resolution,[status(thm)],[c_28,c_1089])).

tff(c_5856,plain,(
    ! [B_201] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_201)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_201))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_5852])).

tff(c_5976,plain,(
    ! [B_204] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_204)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_204))
      | ~ m1_subset_1(B_204,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5856])).

tff(c_5983,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_5976])).

tff(c_5988,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1851,c_1783,c_5983])).

tff(c_5990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1398,c_5988])).

tff(c_5991,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6500,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6474,c_5991])).

tff(c_5992,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6951,plain,(
    ! [A_264,B_265] :
      ( k2_pre_topc(A_264,B_265) = B_265
      | ~ v4_pre_topc(B_265,A_264)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6957,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_6951])).

tff(c_6961,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5992,c_6957])).

tff(c_7862,plain,(
    ! [A_300,B_301] :
      ( k7_subset_1(u1_struct_0(A_300),k2_pre_topc(A_300,B_301),k1_tops_1(A_300,B_301)) = k2_tops_1(A_300,B_301)
      | ~ m1_subset_1(B_301,k1_zfmisc_1(u1_struct_0(A_300)))
      | ~ l1_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7871,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6961,c_7862])).

tff(c_7875,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_6474,c_7871])).

tff(c_7877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6500,c_7875])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:01:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.19/2.02  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.03  
% 5.19/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.19/2.03  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.19/2.03  
% 5.19/2.03  %Foreground sorts:
% 5.19/2.03  
% 5.19/2.03  
% 5.19/2.03  %Background operators:
% 5.19/2.03  
% 5.19/2.03  
% 5.19/2.03  %Foreground operators:
% 5.19/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.19/2.03  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.19/2.03  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.19/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.19/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.19/2.03  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.19/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.19/2.03  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.19/2.03  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.19/2.03  tff('#skF_2', type, '#skF_2': $i).
% 5.19/2.03  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.19/2.03  tff('#skF_1', type, '#skF_1': $i).
% 5.19/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.19/2.03  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.19/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.19/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.19/2.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.19/2.03  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.19/2.03  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.19/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.19/2.03  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.19/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.19/2.03  
% 5.54/2.05  tff(f_104, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.54/2.05  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.54/2.05  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.54/2.05  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.54/2.05  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.54/2.05  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.54/2.05  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.54/2.05  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.54/2.05  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.54/2.05  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.54/2.05  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.54/2.05  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.54/2.05  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.54/2.05  tff(f_78, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.54/2.05  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.54/2.05  tff(f_85, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.54/2.05  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.54/2.05  tff(c_6471, plain, (![A_232, B_233, C_234]: (k7_subset_1(A_232, B_233, C_234)=k4_xboole_0(B_233, C_234) | ~m1_subset_1(B_233, k1_zfmisc_1(A_232)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.54/2.05  tff(c_6474, plain, (![C_234]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_234)=k4_xboole_0('#skF_2', C_234))), inference(resolution, [status(thm)], [c_34, c_6471])).
% 5.54/2.05  tff(c_40, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.54/2.05  tff(c_112, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 5.54/2.05  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.54/2.05  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.54/2.05  tff(c_1387, plain, (![B_115, A_116]: (v4_pre_topc(B_115, A_116) | k2_pre_topc(A_116, B_115)!=B_115 | ~v2_pre_topc(A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.54/2.05  tff(c_1393, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1387])).
% 5.54/2.05  tff(c_1397, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_1393])).
% 5.54/2.05  tff(c_1398, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_112, c_1397])).
% 5.54/2.05  tff(c_492, plain, (![A_69, B_70, C_71]: (k7_subset_1(A_69, B_70, C_71)=k4_xboole_0(B_70, C_71) | ~m1_subset_1(B_70, k1_zfmisc_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.54/2.05  tff(c_690, plain, (![C_79]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_79)=k4_xboole_0('#skF_2', C_79))), inference(resolution, [status(thm)], [c_34, c_492])).
% 5.54/2.05  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.54/2.05  tff(c_256, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_112, c_46])).
% 5.54/2.05  tff(c_696, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_690, c_256])).
% 5.54/2.05  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.54/2.05  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.05  tff(c_103, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.54/2.05  tff(c_111, plain, (![A_8, B_9]: (k3_xboole_0(k4_xboole_0(A_8, B_9), A_8)=k4_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_10, c_103])).
% 5.54/2.05  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.54/2.05  tff(c_395, plain, (![A_62, B_63, C_64]: (r1_tarski(A_62, k2_xboole_0(B_63, C_64)) | ~r1_tarski(k4_xboole_0(A_62, B_63), C_64))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.54/2.05  tff(c_421, plain, (![A_65, B_66]: (r1_tarski(A_65, k2_xboole_0(B_66, A_65)))), inference(resolution, [status(thm)], [c_10, c_395])).
% 5.54/2.05  tff(c_437, plain, (![A_67]: (r1_tarski(k1_xboole_0, A_67))), inference(superposition, [status(thm), theory('equality')], [c_6, c_421])).
% 5.54/2.05  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.54/2.05  tff(c_444, plain, (![A_68]: (k3_xboole_0(k1_xboole_0, A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_437, c_8])).
% 5.54/2.05  tff(c_466, plain, (![A_68]: (k3_xboole_0(A_68, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_444, c_2])).
% 5.54/2.05  tff(c_14, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.54/2.05  tff(c_122, plain, (![A_46, B_47]: (k4_xboole_0(A_46, k4_xboole_0(A_46, B_47))=k3_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.54/2.05  tff(c_140, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_122])).
% 5.54/2.05  tff(c_65, plain, (![A_38, B_39]: (r1_tarski(k4_xboole_0(A_38, B_39), A_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.05  tff(c_68, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_65])).
% 5.54/2.05  tff(c_110, plain, (![A_12]: (k3_xboole_0(A_12, A_12)=A_12)), inference(resolution, [status(thm)], [c_68, c_103])).
% 5.54/2.05  tff(c_308, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.54/2.05  tff(c_317, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k4_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_110, c_308])).
% 5.54/2.05  tff(c_326, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_317])).
% 5.54/2.05  tff(c_496, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_466, c_326])).
% 5.54/2.05  tff(c_143, plain, (![A_48, B_49]: (r1_tarski(k3_xboole_0(A_48, B_49), A_48))), inference(superposition, [status(thm), theory('equality')], [c_122, c_10])).
% 5.54/2.05  tff(c_1224, plain, (![A_111, B_112]: (k3_xboole_0(k3_xboole_0(A_111, B_112), A_111)=k3_xboole_0(A_111, B_112))), inference(resolution, [status(thm)], [c_143, c_8])).
% 5.54/2.05  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.54/2.05  tff(c_1240, plain, (![A_111, B_112]: (k5_xboole_0(k3_xboole_0(A_111, B_112), k3_xboole_0(A_111, B_112))=k4_xboole_0(k3_xboole_0(A_111, B_112), A_111))), inference(superposition, [status(thm), theory('equality')], [c_1224, c_4])).
% 5.54/2.05  tff(c_1311, plain, (![A_113, B_114]: (k4_xboole_0(k3_xboole_0(A_113, B_114), A_113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_496, c_1240])).
% 5.54/2.05  tff(c_1496, plain, (![A_119, B_120]: (k4_xboole_0(k3_xboole_0(A_119, B_120), B_120)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1311])).
% 5.54/2.05  tff(c_1583, plain, (![A_121, B_122]: (k4_xboole_0(k4_xboole_0(A_121, B_122), A_121)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_111, c_1496])).
% 5.54/2.05  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.54/2.05  tff(c_1600, plain, (![A_121, B_122]: (k2_xboole_0(A_121, k4_xboole_0(A_121, B_122))=k2_xboole_0(A_121, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1583, c_12])).
% 5.54/2.05  tff(c_1784, plain, (![A_127, B_128]: (k2_xboole_0(A_127, k4_xboole_0(A_127, B_128))=A_127)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1600])).
% 5.54/2.05  tff(c_1851, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_696, c_1784])).
% 5.54/2.05  tff(c_1775, plain, (![A_125, B_126]: (k4_subset_1(u1_struct_0(A_125), B_126, k2_tops_1(A_125, B_126))=k2_pre_topc(A_125, B_126) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_125))) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.54/2.05  tff(c_1779, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1775])).
% 5.54/2.05  tff(c_1783, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1779])).
% 5.54/2.05  tff(c_28, plain, (![A_27, B_28]: (m1_subset_1(k2_tops_1(A_27, B_28), k1_zfmisc_1(u1_struct_0(A_27))) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.54/2.05  tff(c_1089, plain, (![A_100, B_101, C_102]: (k4_subset_1(A_100, B_101, C_102)=k2_xboole_0(B_101, C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(A_100)) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.54/2.05  tff(c_5852, plain, (![A_199, B_200, B_201]: (k4_subset_1(u1_struct_0(A_199), B_200, k2_tops_1(A_199, B_201))=k2_xboole_0(B_200, k2_tops_1(A_199, B_201)) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(resolution, [status(thm)], [c_28, c_1089])).
% 5.54/2.05  tff(c_5856, plain, (![B_201]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_201))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_201)) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_5852])).
% 5.54/2.05  tff(c_5976, plain, (![B_204]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_204))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_204)) | ~m1_subset_1(B_204, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5856])).
% 5.54/2.05  tff(c_5983, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_5976])).
% 5.54/2.05  tff(c_5988, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1851, c_1783, c_5983])).
% 5.54/2.05  tff(c_5990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1398, c_5988])).
% 5.54/2.05  tff(c_5991, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 5.54/2.05  tff(c_6500, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6474, c_5991])).
% 5.54/2.05  tff(c_5992, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 5.54/2.05  tff(c_6951, plain, (![A_264, B_265]: (k2_pre_topc(A_264, B_265)=B_265 | ~v4_pre_topc(B_265, A_264) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.54/2.05  tff(c_6957, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_6951])).
% 5.54/2.05  tff(c_6961, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5992, c_6957])).
% 5.54/2.05  tff(c_7862, plain, (![A_300, B_301]: (k7_subset_1(u1_struct_0(A_300), k2_pre_topc(A_300, B_301), k1_tops_1(A_300, B_301))=k2_tops_1(A_300, B_301) | ~m1_subset_1(B_301, k1_zfmisc_1(u1_struct_0(A_300))) | ~l1_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.54/2.05  tff(c_7871, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6961, c_7862])).
% 5.54/2.05  tff(c_7875, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_6474, c_7871])).
% 5.54/2.05  tff(c_7877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6500, c_7875])).
% 5.54/2.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.54/2.05  
% 5.54/2.05  Inference rules
% 5.54/2.05  ----------------------
% 5.54/2.05  #Ref     : 0
% 5.54/2.05  #Sup     : 1905
% 5.54/2.05  #Fact    : 0
% 5.54/2.05  #Define  : 0
% 5.54/2.05  #Split   : 2
% 5.54/2.05  #Chain   : 0
% 5.54/2.05  #Close   : 0
% 5.54/2.05  
% 5.54/2.05  Ordering : KBO
% 5.54/2.05  
% 5.54/2.05  Simplification rules
% 5.54/2.05  ----------------------
% 5.54/2.05  #Subsume      : 27
% 5.54/2.05  #Demod        : 1950
% 5.54/2.05  #Tautology    : 1514
% 5.54/2.05  #SimpNegUnit  : 4
% 5.54/2.05  #BackRed      : 11
% 5.54/2.05  
% 5.54/2.05  #Partial instantiations: 0
% 5.54/2.05  #Strategies tried      : 1
% 5.54/2.05  
% 5.54/2.05  Timing (in seconds)
% 5.54/2.05  ----------------------
% 5.54/2.05  Preprocessing        : 0.32
% 5.54/2.05  Parsing              : 0.18
% 5.54/2.05  CNF conversion       : 0.02
% 5.54/2.05  Main loop            : 0.96
% 5.54/2.05  Inferencing          : 0.29
% 5.54/2.05  Reduction            : 0.44
% 5.54/2.05  Demodulation         : 0.37
% 5.54/2.05  BG Simplification    : 0.03
% 5.54/2.05  Subsumption          : 0.14
% 5.54/2.05  Abstraction          : 0.05
% 5.54/2.05  MUC search           : 0.00
% 5.54/2.05  Cooper               : 0.00
% 5.54/2.05  Total                : 1.33
% 5.54/2.06  Index Insertion      : 0.00
% 5.54/2.06  Index Deletion       : 0.00
% 5.54/2.06  Index Matching       : 0.00
% 5.54/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
