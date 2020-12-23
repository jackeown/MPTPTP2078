%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:35 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 4.36s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 292 expanded)
%              Number of leaves         :   39 ( 115 expanded)
%              Depth                    :   13
%              Number of atoms          :  167 ( 563 expanded)
%              Number of equality atoms :   68 ( 161 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(f_108,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1976,plain,(
    ! [A_169,B_170,C_171] :
      ( k7_subset_1(A_169,B_170,C_171) = k4_xboole_0(B_170,C_171)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(A_169)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1982,plain,(
    ! [C_171] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_171) = k4_xboole_0('#skF_2',C_171) ),
    inference(resolution,[status(thm)],[c_36,c_1976])).

tff(c_42,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_87,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_240,plain,(
    ! [A_67,B_68,C_69] :
      ( k7_subset_1(A_67,B_68,C_69) = k4_xboole_0(B_68,C_69)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_251,plain,(
    ! [C_70] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_70) = k4_xboole_0('#skF_2',C_70) ),
    inference(resolution,[status(thm)],[c_36,c_240])).

tff(c_48,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_169,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_48])).

tff(c_257,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_169])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(A_23,k1_zfmisc_1(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_160,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [B_63,A_64] :
      ( k4_xboole_0(B_63,A_64) = k3_subset_1(B_63,A_64)
      | ~ r1_tarski(A_64,B_63) ) ),
    inference(resolution,[status(thm)],[c_24,c_160])).

tff(c_196,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_6,c_184])).

tff(c_204,plain,(
    ! [A_65,B_66] : k3_subset_1(A_65,k4_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_196])).

tff(c_116,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(A_57,k3_subset_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_121,plain,(
    ! [B_24,A_23] :
      ( k3_subset_1(B_24,k3_subset_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_116])).

tff(c_210,plain,(
    ! [A_65,B_66] :
      ( k3_subset_1(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66)
      | ~ r1_tarski(k4_xboole_0(A_65,B_66),A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_121])).

tff(c_222,plain,(
    ! [A_65,B_66] : k3_subset_1(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_210])).

tff(c_88,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_6])).

tff(c_199,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k3_subset_1(A_51,k3_xboole_0(A_51,B_52)) ),
    inference(resolution,[status(thm)],[c_97,c_184])).

tff(c_377,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_199])).

tff(c_100,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_88])).

tff(c_405,plain,(
    ! [A_82,B_83] : k3_xboole_0(A_82,k4_xboole_0(A_82,B_83)) = k4_xboole_0(A_82,B_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_100])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_453,plain,(
    ! [A_84,B_85] : k2_xboole_0(A_84,k4_xboole_0(A_84,B_85)) = A_84 ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_4])).

tff(c_468,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_453])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_831,plain,(
    ! [A_99,B_100] :
      ( k4_subset_1(u1_struct_0(A_99),B_100,k2_tops_1(A_99,B_100)) = k2_pre_topc(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(u1_struct_0(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_838,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_831])).

tff(c_843,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_838])).

tff(c_344,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k2_tops_1(A_75,B_76),k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(A_23,B_24)
      | ~ m1_subset_1(A_23,k1_zfmisc_1(B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_358,plain,(
    ! [A_75,B_76] :
      ( r1_tarski(k2_tops_1(A_75,B_76),u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(resolution,[status(thm)],[c_344,c_22])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1584,plain,(
    ! [A_146,B_147] :
      ( k4_xboole_0(u1_struct_0(A_146),k2_tops_1(A_146,B_147)) = k3_subset_1(u1_struct_0(A_146),k2_tops_1(A_146,B_147))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(resolution,[status(thm)],[c_344,c_12])).

tff(c_1591,plain,
    ( k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1584])).

tff(c_1596,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1591])).

tff(c_203,plain,(
    ! [A_5,B_6] : k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_196])).

tff(c_1621,plain,(
    k3_subset_1(u1_struct_0('#skF_1'),k3_subset_1(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2'))) = k3_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1596,c_203])).

tff(c_1668,plain,
    ( k3_xboole_0(u1_struct_0('#skF_1'),k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1621,c_121])).

tff(c_1765,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1668])).

tff(c_1768,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_358,c_1765])).

tff(c_1772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_1768])).

tff(c_1774,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1668])).

tff(c_662,plain,(
    ! [A_92,B_93,C_94] :
      ( k4_subset_1(A_92,B_93,C_94) = k2_xboole_0(B_93,C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(A_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1205,plain,(
    ! [B_120,B_121,A_122] :
      ( k4_subset_1(B_120,B_121,A_122) = k2_xboole_0(B_121,A_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(B_120))
      | ~ r1_tarski(A_122,B_120) ) ),
    inference(resolution,[status(thm)],[c_24,c_662])).

tff(c_1214,plain,(
    ! [A_122] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_122) = k2_xboole_0('#skF_2',A_122)
      | ~ r1_tarski(A_122,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_36,c_1205])).

tff(c_1792,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1774,c_1214])).

tff(c_1803,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_843,c_1792])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_557,plain,(
    ! [A_90,B_91] :
      ( v4_pre_topc(k2_pre_topc(A_90,B_91),A_90)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90)
      | ~ v2_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_564,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_557])).

tff(c_569,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_564])).

tff(c_1810,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1803,c_569])).

tff(c_1812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_1810])).

tff(c_1813,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_1983,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1982,c_1813])).

tff(c_1814,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2431,plain,(
    ! [A_207,B_208] :
      ( r1_tarski(k2_tops_1(A_207,B_208),B_208)
      | ~ v4_pre_topc(B_208,A_207)
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2438,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2431])).

tff(c_2443,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1814,c_2438])).

tff(c_1844,plain,(
    ! [A_157,B_158] :
      ( k4_xboole_0(A_157,B_158) = k3_subset_1(A_157,B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_157)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1851,plain,(
    ! [B_24,A_23] :
      ( k4_xboole_0(B_24,A_23) = k3_subset_1(B_24,A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_1844])).

tff(c_2450,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2443,c_1851])).

tff(c_2668,plain,(
    ! [A_212,B_213] :
      ( k7_subset_1(u1_struct_0(A_212),B_213,k2_tops_1(A_212,B_213)) = k1_tops_1(A_212,B_213)
      | ~ m1_subset_1(B_213,k1_zfmisc_1(u1_struct_0(A_212)))
      | ~ l1_pre_topc(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2675,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_2668])).

tff(c_2680,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2450,c_1982,c_2675])).

tff(c_1863,plain,(
    ! [B_159,A_160] :
      ( k4_xboole_0(B_159,A_160) = k3_subset_1(B_159,A_160)
      | ~ r1_tarski(A_160,B_159) ) ),
    inference(resolution,[status(thm)],[c_24,c_1844])).

tff(c_1875,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_6,c_1863])).

tff(c_1881,plain,(
    ! [A_5,B_6] : k3_subset_1(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1875])).

tff(c_2466,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2450,c_1881])).

tff(c_1911,plain,(
    ! [A_163,B_164] :
      ( k3_subset_1(A_163,k3_subset_1(A_163,B_164)) = B_164
      | ~ m1_subset_1(B_164,k1_zfmisc_1(A_163)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1916,plain,(
    ! [B_24,A_23] :
      ( k3_subset_1(B_24,k3_subset_1(B_24,A_23)) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_24,c_1911])).

tff(c_2504,plain,
    ( k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2466,c_1916])).

tff(c_2513,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2443,c_2504])).

tff(c_2469,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2450,c_8])).

tff(c_2598,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2'))) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2513,c_2469])).

tff(c_2683,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2680,c_2598])).

tff(c_2690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1983,c_2683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n007.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:55:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.75  
% 4.28/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.75  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 4.28/1.75  
% 4.28/1.75  %Foreground sorts:
% 4.28/1.75  
% 4.28/1.75  
% 4.28/1.75  %Background operators:
% 4.28/1.75  
% 4.28/1.75  
% 4.28/1.75  %Foreground operators:
% 4.28/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.28/1.75  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.28/1.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.28/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.28/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/1.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.28/1.75  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.28/1.75  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.28/1.75  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.28/1.75  tff('#skF_2', type, '#skF_2': $i).
% 4.28/1.75  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.28/1.75  tff('#skF_1', type, '#skF_1': $i).
% 4.28/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.28/1.75  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.28/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/1.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.28/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/1.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.28/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.28/1.75  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.28/1.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.28/1.75  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.28/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.28/1.75  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.28/1.75  
% 4.36/1.77  tff(f_108, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.36/1.77  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.36/1.77  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.36/1.77  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.36/1.77  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.36/1.77  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.36/1.77  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.36/1.77  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.36/1.77  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.36/1.77  tff(f_65, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.36/1.77  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.36/1.77  tff(f_73, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 4.36/1.77  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 4.36/1.77  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 4.36/1.77  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.36/1.77  tff(c_1976, plain, (![A_169, B_170, C_171]: (k7_subset_1(A_169, B_170, C_171)=k4_xboole_0(B_170, C_171) | ~m1_subset_1(B_170, k1_zfmisc_1(A_169)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.36/1.77  tff(c_1982, plain, (![C_171]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_171)=k4_xboole_0('#skF_2', C_171))), inference(resolution, [status(thm)], [c_36, c_1976])).
% 4.36/1.77  tff(c_42, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.36/1.77  tff(c_87, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_42])).
% 4.36/1.77  tff(c_240, plain, (![A_67, B_68, C_69]: (k7_subset_1(A_67, B_68, C_69)=k4_xboole_0(B_68, C_69) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.36/1.77  tff(c_251, plain, (![C_70]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_70)=k4_xboole_0('#skF_2', C_70))), inference(resolution, [status(thm)], [c_36, c_240])).
% 4.36/1.77  tff(c_48, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.36/1.77  tff(c_169, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_87, c_48])).
% 4.36/1.77  tff(c_257, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_251, c_169])).
% 4.36/1.77  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.36/1.77  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.36/1.77  tff(c_24, plain, (![A_23, B_24]: (m1_subset_1(A_23, k1_zfmisc_1(B_24)) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.36/1.77  tff(c_160, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.36/1.77  tff(c_184, plain, (![B_63, A_64]: (k4_xboole_0(B_63, A_64)=k3_subset_1(B_63, A_64) | ~r1_tarski(A_64, B_63))), inference(resolution, [status(thm)], [c_24, c_160])).
% 4.36/1.77  tff(c_196, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_subset_1(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_6, c_184])).
% 4.36/1.77  tff(c_204, plain, (![A_65, B_66]: (k3_subset_1(A_65, k4_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_196])).
% 4.36/1.77  tff(c_116, plain, (![A_57, B_58]: (k3_subset_1(A_57, k3_subset_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.36/1.77  tff(c_121, plain, (![B_24, A_23]: (k3_subset_1(B_24, k3_subset_1(B_24, A_23))=A_23 | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_24, c_116])).
% 4.36/1.77  tff(c_210, plain, (![A_65, B_66]: (k3_subset_1(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66) | ~r1_tarski(k4_xboole_0(A_65, B_66), A_65))), inference(superposition, [status(thm), theory('equality')], [c_204, c_121])).
% 4.36/1.77  tff(c_222, plain, (![A_65, B_66]: (k3_subset_1(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_210])).
% 4.36/1.77  tff(c_88, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.36/1.77  tff(c_97, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), A_51))), inference(superposition, [status(thm), theory('equality')], [c_88, c_6])).
% 4.36/1.77  tff(c_199, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k3_subset_1(A_51, k3_xboole_0(A_51, B_52)))), inference(resolution, [status(thm)], [c_97, c_184])).
% 4.36/1.77  tff(c_377, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_199])).
% 4.36/1.77  tff(c_100, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_xboole_0(A_7, k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_88])).
% 4.36/1.77  tff(c_405, plain, (![A_82, B_83]: (k3_xboole_0(A_82, k4_xboole_0(A_82, B_83))=k4_xboole_0(A_82, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_377, c_100])).
% 4.36/1.77  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.36/1.77  tff(c_453, plain, (![A_84, B_85]: (k2_xboole_0(A_84, k4_xboole_0(A_84, B_85))=A_84)), inference(superposition, [status(thm), theory('equality')], [c_405, c_4])).
% 4.36/1.77  tff(c_468, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_257, c_453])).
% 4.36/1.77  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.36/1.77  tff(c_831, plain, (![A_99, B_100]: (k4_subset_1(u1_struct_0(A_99), B_100, k2_tops_1(A_99, B_100))=k2_pre_topc(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(u1_struct_0(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.36/1.77  tff(c_838, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_831])).
% 4.36/1.77  tff(c_843, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_838])).
% 4.36/1.77  tff(c_344, plain, (![A_75, B_76]: (m1_subset_1(k2_tops_1(A_75, B_76), k1_zfmisc_1(u1_struct_0(A_75))) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.36/1.77  tff(c_22, plain, (![A_23, B_24]: (r1_tarski(A_23, B_24) | ~m1_subset_1(A_23, k1_zfmisc_1(B_24)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.36/1.77  tff(c_358, plain, (![A_75, B_76]: (r1_tarski(k2_tops_1(A_75, B_76), u1_struct_0(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(resolution, [status(thm)], [c_344, c_22])).
% 4.36/1.77  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.36/1.77  tff(c_1584, plain, (![A_146, B_147]: (k4_xboole_0(u1_struct_0(A_146), k2_tops_1(A_146, B_147))=k3_subset_1(u1_struct_0(A_146), k2_tops_1(A_146, B_147)) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(resolution, [status(thm)], [c_344, c_12])).
% 4.36/1.77  tff(c_1591, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1584])).
% 4.36/1.77  tff(c_1596, plain, (k4_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1591])).
% 4.36/1.77  tff(c_203, plain, (![A_5, B_6]: (k3_subset_1(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_196])).
% 4.36/1.77  tff(c_1621, plain, (k3_subset_1(u1_struct_0('#skF_1'), k3_subset_1(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2')))=k3_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1596, c_203])).
% 4.36/1.77  tff(c_1668, plain, (k3_xboole_0(u1_struct_0('#skF_1'), k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1621, c_121])).
% 4.36/1.77  tff(c_1765, plain, (~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1668])).
% 4.36/1.77  tff(c_1768, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_358, c_1765])).
% 4.36/1.77  tff(c_1772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_1768])).
% 4.36/1.77  tff(c_1774, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1668])).
% 4.36/1.77  tff(c_662, plain, (![A_92, B_93, C_94]: (k4_subset_1(A_92, B_93, C_94)=k2_xboole_0(B_93, C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(A_92)) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.36/1.77  tff(c_1205, plain, (![B_120, B_121, A_122]: (k4_subset_1(B_120, B_121, A_122)=k2_xboole_0(B_121, A_122) | ~m1_subset_1(B_121, k1_zfmisc_1(B_120)) | ~r1_tarski(A_122, B_120))), inference(resolution, [status(thm)], [c_24, c_662])).
% 4.36/1.77  tff(c_1214, plain, (![A_122]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_122)=k2_xboole_0('#skF_2', A_122) | ~r1_tarski(A_122, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_1205])).
% 4.36/1.77  tff(c_1792, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1774, c_1214])).
% 4.36/1.77  tff(c_1803, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_468, c_843, c_1792])).
% 4.36/1.77  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.36/1.77  tff(c_557, plain, (![A_90, B_91]: (v4_pre_topc(k2_pre_topc(A_90, B_91), A_90) | ~m1_subset_1(B_91, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90) | ~v2_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.36/1.77  tff(c_564, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_557])).
% 4.36/1.77  tff(c_569, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_564])).
% 4.36/1.77  tff(c_1810, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1803, c_569])).
% 4.36/1.77  tff(c_1812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_1810])).
% 4.36/1.77  tff(c_1813, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 4.36/1.77  tff(c_1983, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1982, c_1813])).
% 4.36/1.77  tff(c_1814, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_42])).
% 4.36/1.77  tff(c_2431, plain, (![A_207, B_208]: (r1_tarski(k2_tops_1(A_207, B_208), B_208) | ~v4_pre_topc(B_208, A_207) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.36/1.77  tff(c_2438, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2431])).
% 4.36/1.77  tff(c_2443, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1814, c_2438])).
% 4.36/1.77  tff(c_1844, plain, (![A_157, B_158]: (k4_xboole_0(A_157, B_158)=k3_subset_1(A_157, B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(A_157)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.36/1.77  tff(c_1851, plain, (![B_24, A_23]: (k4_xboole_0(B_24, A_23)=k3_subset_1(B_24, A_23) | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_24, c_1844])).
% 4.36/1.77  tff(c_2450, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2443, c_1851])).
% 4.36/1.77  tff(c_2668, plain, (![A_212, B_213]: (k7_subset_1(u1_struct_0(A_212), B_213, k2_tops_1(A_212, B_213))=k1_tops_1(A_212, B_213) | ~m1_subset_1(B_213, k1_zfmisc_1(u1_struct_0(A_212))) | ~l1_pre_topc(A_212))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.36/1.77  tff(c_2675, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_2668])).
% 4.36/1.77  tff(c_2680, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2450, c_1982, c_2675])).
% 4.36/1.77  tff(c_1863, plain, (![B_159, A_160]: (k4_xboole_0(B_159, A_160)=k3_subset_1(B_159, A_160) | ~r1_tarski(A_160, B_159))), inference(resolution, [status(thm)], [c_24, c_1844])).
% 4.36/1.77  tff(c_1875, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_subset_1(A_5, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_6, c_1863])).
% 4.36/1.77  tff(c_1881, plain, (![A_5, B_6]: (k3_subset_1(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1875])).
% 4.36/1.77  tff(c_2466, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2450, c_1881])).
% 4.36/1.77  tff(c_1911, plain, (![A_163, B_164]: (k3_subset_1(A_163, k3_subset_1(A_163, B_164))=B_164 | ~m1_subset_1(B_164, k1_zfmisc_1(A_163)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.36/1.77  tff(c_1916, plain, (![B_24, A_23]: (k3_subset_1(B_24, k3_subset_1(B_24, A_23))=A_23 | ~r1_tarski(A_23, B_24))), inference(resolution, [status(thm)], [c_24, c_1911])).
% 4.36/1.77  tff(c_2504, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2466, c_1916])).
% 4.36/1.77  tff(c_2513, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2443, c_2504])).
% 4.36/1.77  tff(c_2469, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2450, c_8])).
% 4.36/1.77  tff(c_2598, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2')))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2513, c_2469])).
% 4.36/1.77  tff(c_2683, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2680, c_2598])).
% 4.36/1.77  tff(c_2690, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1983, c_2683])).
% 4.36/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.36/1.77  
% 4.36/1.77  Inference rules
% 4.36/1.77  ----------------------
% 4.36/1.77  #Ref     : 0
% 4.36/1.77  #Sup     : 668
% 4.36/1.77  #Fact    : 0
% 4.36/1.77  #Define  : 0
% 4.36/1.77  #Split   : 2
% 4.36/1.77  #Chain   : 0
% 4.36/1.77  #Close   : 0
% 4.36/1.77  
% 4.36/1.77  Ordering : KBO
% 4.36/1.77  
% 4.36/1.77  Simplification rules
% 4.36/1.77  ----------------------
% 4.36/1.77  #Subsume      : 13
% 4.36/1.77  #Demod        : 527
% 4.36/1.77  #Tautology    : 455
% 4.36/1.77  #SimpNegUnit  : 3
% 4.36/1.77  #BackRed      : 24
% 4.36/1.77  
% 4.36/1.77  #Partial instantiations: 0
% 4.36/1.77  #Strategies tried      : 1
% 4.36/1.77  
% 4.36/1.77  Timing (in seconds)
% 4.36/1.77  ----------------------
% 4.36/1.77  Preprocessing        : 0.32
% 4.36/1.77  Parsing              : 0.18
% 4.36/1.77  CNF conversion       : 0.02
% 4.36/1.77  Main loop            : 0.68
% 4.36/1.77  Inferencing          : 0.25
% 4.36/1.77  Reduction            : 0.25
% 4.36/1.77  Demodulation         : 0.19
% 4.36/1.77  BG Simplification    : 0.03
% 4.36/1.77  Subsumption          : 0.10
% 4.36/1.77  Abstraction          : 0.04
% 4.36/1.78  MUC search           : 0.00
% 4.36/1.78  Cooper               : 0.00
% 4.36/1.78  Total                : 1.05
% 4.36/1.78  Index Insertion      : 0.00
% 4.36/1.78  Index Deletion       : 0.00
% 4.36/1.78  Index Matching       : 0.00
% 4.36/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
