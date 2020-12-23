%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:17 EST 2020

% Result     : Theorem 6.00s
% Output     : CNFRefutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 404 expanded)
%              Number of leaves         :   41 ( 149 expanded)
%              Depth                    :   12
%              Number of atoms          :  138 ( 783 expanded)
%              Number of equality atoms :   68 ( 298 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(f_114,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
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

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_4216,plain,(
    ! [A_198,B_199,C_200] :
      ( k7_subset_1(A_198,B_199,C_200) = k4_xboole_0(B_199,C_200)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_198)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4231,plain,(
    ! [C_200] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_200) = k4_xboole_0('#skF_2',C_200) ),
    inference(resolution,[status(thm)],[c_38,c_4216])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_135,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1589,plain,(
    ! [B_115,A_116] :
      ( v4_pre_topc(B_115,A_116)
      | k2_pre_topc(A_116,B_115) != B_115
      | ~ v2_pre_topc(A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1627,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1589])).

tff(c_1648,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_1627])).

tff(c_1649,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_1648])).

tff(c_606,plain,(
    ! [A_79,B_80,C_81] :
      ( k7_subset_1(A_79,B_80,C_81) = k4_xboole_0(B_80,C_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_622,plain,(
    ! [C_82] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_82) = k4_xboole_0('#skF_2',C_82) ),
    inference(resolution,[status(thm)],[c_38,c_606])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_264,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_50])).

tff(c_628,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_264])).

tff(c_18,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_12,B_13] : m1_subset_1(k6_subset_1(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [A_12,B_13] : m1_subset_1(k4_xboole_0(A_12,B_13),k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14])).

tff(c_10,plain,(
    ! [A_9] : k2_subset_1(A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k4_subset_1(A_22,B_23,k3_subset_1(A_22,B_23)) = k2_subset_1(A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_696,plain,(
    ! [A_83,B_84] :
      ( k4_subset_1(A_83,B_84,k3_subset_1(A_83,B_84)) = A_83
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_22])).

tff(c_1118,plain,(
    ! [A_96,B_97] : k4_subset_1(A_96,k4_xboole_0(A_96,B_97),k3_subset_1(A_96,k4_xboole_0(A_96,B_97))) = A_96 ),
    inference(resolution,[status(thm)],[c_51,c_696])).

tff(c_1133,plain,(
    k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')))) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_1118])).

tff(c_1159,plain,(
    k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_1133])).

tff(c_362,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_369,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_subset_1(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(resolution,[status(thm)],[c_51,c_362])).

tff(c_646,plain,(
    k3_subset_1('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_369])).

tff(c_652,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_646])).

tff(c_1366,plain,(
    ! [A_108,B_109,C_110] :
      ( k4_subset_1(A_108,B_109,C_110) = k2_xboole_0(B_109,C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(A_108))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1761,plain,(
    ! [A_119,B_120,B_121] :
      ( k4_subset_1(A_119,B_120,k4_xboole_0(A_119,B_121)) = k2_xboole_0(B_120,k4_xboole_0(A_119,B_121))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_51,c_1366])).

tff(c_2147,plain,(
    ! [A_131,B_132,B_133] : k4_subset_1(A_131,k4_xboole_0(A_131,B_132),k4_xboole_0(A_131,B_133)) = k2_xboole_0(k4_xboole_0(A_131,B_132),k4_xboole_0(A_131,B_133)) ),
    inference(resolution,[status(thm)],[c_51,c_1761])).

tff(c_2174,plain,(
    ! [B_133] : k2_xboole_0(k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')),k4_xboole_0('#skF_2',B_133)) = k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),k4_xboole_0('#skF_2',B_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_2147])).

tff(c_2387,plain,(
    ! [B_143] : k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),k4_xboole_0('#skF_2',B_143)) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k4_xboole_0('#skF_2',B_143)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_628,c_2174])).

tff(c_2403,plain,(
    k4_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_2387])).

tff(c_2415,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1159,c_652,c_2403])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_192,plain,(
    ! [B_55,A_56] : k3_tarski(k2_tarski(B_55,A_56)) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_120])).

tff(c_8,plain,(
    ! [A_7,B_8] : k3_tarski(k2_tarski(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_198,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2448,plain,(
    k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2415,c_4])).

tff(c_2460,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2415,c_198,c_2448])).

tff(c_1703,plain,(
    ! [A_117,B_118] :
      ( k4_subset_1(u1_struct_0(A_117),B_118,k2_tops_1(A_117,B_118)) = k2_pre_topc(A_117,B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_117)))
      | ~ l1_pre_topc(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1732,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1703])).

tff(c_1756,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1732])).

tff(c_30,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k2_tops_1(A_29,B_30),k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3585,plain,(
    ! [A_164,B_165,B_166] :
      ( k4_subset_1(u1_struct_0(A_164),B_165,k2_tops_1(A_164,B_166)) = k2_xboole_0(B_165,k2_tops_1(A_164,B_166))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0(A_164)))
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_30,c_1366])).

tff(c_3625,plain,(
    ! [B_166] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_166)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_166))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_3585])).

tff(c_3663,plain,(
    ! [B_167] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_167)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_167))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3625])).

tff(c_3721,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_3663])).

tff(c_3741,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_1756,c_3721])).

tff(c_3743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1649,c_3741])).

tff(c_3744,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4232,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4231,c_3744])).

tff(c_3745,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_4657,plain,(
    ! [A_215,B_216] :
      ( k2_pre_topc(A_215,B_216) = B_216
      | ~ v4_pre_topc(B_216,A_215)
      | ~ m1_subset_1(B_216,k1_zfmisc_1(u1_struct_0(A_215)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4684,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_4657])).

tff(c_4700,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3745,c_4684])).

tff(c_5372,plain,(
    ! [A_239,B_240] :
      ( k7_subset_1(u1_struct_0(A_239),k2_pre_topc(A_239,B_240),k1_tops_1(A_239,B_240)) = k2_tops_1(A_239,B_240)
      | ~ m1_subset_1(B_240,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ l1_pre_topc(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5381,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4700,c_5372])).

tff(c_5385,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_4231,c_5381])).

tff(c_5387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4232,c_5385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:13:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.00/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.20  
% 6.00/2.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.00/2.20  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 6.00/2.20  
% 6.00/2.20  %Foreground sorts:
% 6.00/2.20  
% 6.00/2.20  
% 6.00/2.20  %Background operators:
% 6.00/2.20  
% 6.00/2.20  
% 6.00/2.20  %Foreground operators:
% 6.00/2.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.00/2.20  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.00/2.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.00/2.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.00/2.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.00/2.20  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.00/2.20  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.00/2.20  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.00/2.20  tff('#skF_2', type, '#skF_2': $i).
% 6.00/2.20  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.00/2.20  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 6.00/2.20  tff('#skF_1', type, '#skF_1': $i).
% 6.00/2.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.00/2.20  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.00/2.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.00/2.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.00/2.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.00/2.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.00/2.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.00/2.20  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.00/2.20  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.00/2.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.00/2.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.00/2.20  
% 6.30/2.22  tff(f_114, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 6.30/2.22  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.30/2.22  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.30/2.22  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 6.30/2.22  tff(f_41, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 6.30/2.22  tff(f_35, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 6.30/2.22  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 6.30/2.22  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.30/2.22  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.30/2.22  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.30/2.22  tff(f_33, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.30/2.22  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 6.30/2.22  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 6.30/2.22  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.30/2.22  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 6.30/2.22  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.30/2.22  tff(c_4216, plain, (![A_198, B_199, C_200]: (k7_subset_1(A_198, B_199, C_200)=k4_xboole_0(B_199, C_200) | ~m1_subset_1(B_199, k1_zfmisc_1(A_198)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.30/2.22  tff(c_4231, plain, (![C_200]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_200)=k4_xboole_0('#skF_2', C_200))), inference(resolution, [status(thm)], [c_38, c_4216])).
% 6.30/2.22  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.30/2.22  tff(c_135, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 6.30/2.22  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.30/2.22  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.30/2.22  tff(c_1589, plain, (![B_115, A_116]: (v4_pre_topc(B_115, A_116) | k2_pre_topc(A_116, B_115)!=B_115 | ~v2_pre_topc(A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.30/2.22  tff(c_1627, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1589])).
% 6.30/2.22  tff(c_1648, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_1627])).
% 6.30/2.22  tff(c_1649, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_135, c_1648])).
% 6.30/2.22  tff(c_606, plain, (![A_79, B_80, C_81]: (k7_subset_1(A_79, B_80, C_81)=k4_xboole_0(B_80, C_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.30/2.22  tff(c_622, plain, (![C_82]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_82)=k4_xboole_0('#skF_2', C_82))), inference(resolution, [status(thm)], [c_38, c_606])).
% 6.30/2.22  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.30/2.22  tff(c_264, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_135, c_50])).
% 6.30/2.22  tff(c_628, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_622, c_264])).
% 6.30/2.22  tff(c_18, plain, (![A_17, B_18]: (k6_subset_1(A_17, B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.30/2.22  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(k6_subset_1(A_12, B_13), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.30/2.22  tff(c_51, plain, (![A_12, B_13]: (m1_subset_1(k4_xboole_0(A_12, B_13), k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14])).
% 6.30/2.22  tff(c_10, plain, (![A_9]: (k2_subset_1(A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.30/2.22  tff(c_22, plain, (![A_22, B_23]: (k4_subset_1(A_22, B_23, k3_subset_1(A_22, B_23))=k2_subset_1(A_22) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.30/2.22  tff(c_696, plain, (![A_83, B_84]: (k4_subset_1(A_83, B_84, k3_subset_1(A_83, B_84))=A_83 | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_22])).
% 6.30/2.22  tff(c_1118, plain, (![A_96, B_97]: (k4_subset_1(A_96, k4_xboole_0(A_96, B_97), k3_subset_1(A_96, k4_xboole_0(A_96, B_97)))=A_96)), inference(resolution, [status(thm)], [c_51, c_696])).
% 6.30/2.22  tff(c_1133, plain, (k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_628, c_1118])).
% 6.30/2.22  tff(c_1159, plain, (k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_628, c_1133])).
% 6.30/2.22  tff(c_362, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.30/2.22  tff(c_369, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_subset_1(A_12, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_51, c_362])).
% 6.30/2.22  tff(c_646, plain, (k3_subset_1('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_628, c_369])).
% 6.30/2.22  tff(c_652, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_646])).
% 6.30/2.22  tff(c_1366, plain, (![A_108, B_109, C_110]: (k4_subset_1(A_108, B_109, C_110)=k2_xboole_0(B_109, C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(A_108)) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.30/2.22  tff(c_1761, plain, (![A_119, B_120, B_121]: (k4_subset_1(A_119, B_120, k4_xboole_0(A_119, B_121))=k2_xboole_0(B_120, k4_xboole_0(A_119, B_121)) | ~m1_subset_1(B_120, k1_zfmisc_1(A_119)))), inference(resolution, [status(thm)], [c_51, c_1366])).
% 6.30/2.22  tff(c_2147, plain, (![A_131, B_132, B_133]: (k4_subset_1(A_131, k4_xboole_0(A_131, B_132), k4_xboole_0(A_131, B_133))=k2_xboole_0(k4_xboole_0(A_131, B_132), k4_xboole_0(A_131, B_133)))), inference(resolution, [status(thm)], [c_51, c_1761])).
% 6.30/2.22  tff(c_2174, plain, (![B_133]: (k2_xboole_0(k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')), k4_xboole_0('#skF_2', B_133))=k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', B_133)))), inference(superposition, [status(thm), theory('equality')], [c_628, c_2147])).
% 6.30/2.22  tff(c_2387, plain, (![B_143]: (k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', B_143))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', B_143)))), inference(demodulation, [status(thm), theory('equality')], [c_628, c_2174])).
% 6.30/2.22  tff(c_2403, plain, (k4_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_652, c_2387])).
% 6.30/2.22  tff(c_2415, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1159, c_652, c_2403])).
% 6.30/2.22  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.30/2.22  tff(c_120, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.30/2.22  tff(c_192, plain, (![B_55, A_56]: (k3_tarski(k2_tarski(B_55, A_56))=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_6, c_120])).
% 6.30/2.22  tff(c_8, plain, (![A_7, B_8]: (k3_tarski(k2_tarski(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.30/2.22  tff(c_198, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_192, c_8])).
% 6.30/2.22  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.30/2.22  tff(c_2448, plain, (k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2415, c_4])).
% 6.30/2.22  tff(c_2460, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2415, c_198, c_2448])).
% 6.30/2.22  tff(c_1703, plain, (![A_117, B_118]: (k4_subset_1(u1_struct_0(A_117), B_118, k2_tops_1(A_117, B_118))=k2_pre_topc(A_117, B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_117))) | ~l1_pre_topc(A_117))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.30/2.22  tff(c_1732, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1703])).
% 6.30/2.22  tff(c_1756, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1732])).
% 6.30/2.22  tff(c_30, plain, (![A_29, B_30]: (m1_subset_1(k2_tops_1(A_29, B_30), k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_subset_1(B_30, k1_zfmisc_1(u1_struct_0(A_29))) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.30/2.22  tff(c_3585, plain, (![A_164, B_165, B_166]: (k4_subset_1(u1_struct_0(A_164), B_165, k2_tops_1(A_164, B_166))=k2_xboole_0(B_165, k2_tops_1(A_164, B_166)) | ~m1_subset_1(B_165, k1_zfmisc_1(u1_struct_0(A_164))) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0(A_164))) | ~l1_pre_topc(A_164))), inference(resolution, [status(thm)], [c_30, c_1366])).
% 6.30/2.22  tff(c_3625, plain, (![B_166]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_166))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_166)) | ~m1_subset_1(B_166, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_3585])).
% 6.30/2.22  tff(c_3663, plain, (![B_167]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_167))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_167)) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3625])).
% 6.30/2.22  tff(c_3721, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_3663])).
% 6.30/2.22  tff(c_3741, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_1756, c_3721])).
% 6.30/2.22  tff(c_3743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1649, c_3741])).
% 6.30/2.22  tff(c_3744, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 6.30/2.22  tff(c_4232, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4231, c_3744])).
% 6.30/2.22  tff(c_3745, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 6.30/2.22  tff(c_4657, plain, (![A_215, B_216]: (k2_pre_topc(A_215, B_216)=B_216 | ~v4_pre_topc(B_216, A_215) | ~m1_subset_1(B_216, k1_zfmisc_1(u1_struct_0(A_215))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.30/2.22  tff(c_4684, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_4657])).
% 6.30/2.22  tff(c_4700, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3745, c_4684])).
% 6.30/2.22  tff(c_5372, plain, (![A_239, B_240]: (k7_subset_1(u1_struct_0(A_239), k2_pre_topc(A_239, B_240), k1_tops_1(A_239, B_240))=k2_tops_1(A_239, B_240) | ~m1_subset_1(B_240, k1_zfmisc_1(u1_struct_0(A_239))) | ~l1_pre_topc(A_239))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.30/2.22  tff(c_5381, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4700, c_5372])).
% 6.30/2.22  tff(c_5385, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_4231, c_5381])).
% 6.30/2.22  tff(c_5387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4232, c_5385])).
% 6.30/2.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.30/2.22  
% 6.30/2.22  Inference rules
% 6.30/2.22  ----------------------
% 6.30/2.22  #Ref     : 0
% 6.30/2.22  #Sup     : 1310
% 6.30/2.22  #Fact    : 0
% 6.30/2.22  #Define  : 0
% 6.30/2.22  #Split   : 3
% 6.30/2.22  #Chain   : 0
% 6.30/2.22  #Close   : 0
% 6.30/2.22  
% 6.30/2.22  Ordering : KBO
% 6.30/2.22  
% 6.30/2.22  Simplification rules
% 6.30/2.22  ----------------------
% 6.30/2.22  #Subsume      : 71
% 6.30/2.22  #Demod        : 1334
% 6.30/2.22  #Tautology    : 611
% 6.30/2.22  #SimpNegUnit  : 7
% 6.30/2.22  #BackRed      : 6
% 6.30/2.22  
% 6.30/2.22  #Partial instantiations: 0
% 6.30/2.22  #Strategies tried      : 1
% 6.30/2.22  
% 6.30/2.22  Timing (in seconds)
% 6.30/2.22  ----------------------
% 6.30/2.22  Preprocessing        : 0.33
% 6.30/2.22  Parsing              : 0.18
% 6.30/2.22  CNF conversion       : 0.02
% 6.30/2.22  Main loop            : 1.13
% 6.30/2.22  Inferencing          : 0.32
% 6.30/2.22  Reduction            : 0.53
% 6.30/2.22  Demodulation         : 0.43
% 6.30/2.22  BG Simplification    : 0.04
% 6.30/2.22  Subsumption          : 0.15
% 6.30/2.22  Abstraction          : 0.08
% 6.30/2.22  MUC search           : 0.00
% 6.30/2.22  Cooper               : 0.00
% 6.30/2.22  Total                : 1.50
% 6.30/2.22  Index Insertion      : 0.00
% 6.30/2.22  Index Deletion       : 0.00
% 6.30/2.22  Index Matching       : 0.00
% 6.30/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
