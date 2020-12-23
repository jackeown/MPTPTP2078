%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:11 EST 2020

% Result     : Theorem 6.85s
% Output     : CNFRefutation 6.85s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 145 expanded)
%              Number of leaves         :   41 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  138 ( 264 expanded)
%              Number of equality atoms :   52 (  79 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_110,negated_conjecture,(
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

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_53,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_7697,plain,(
    ! [A_258,B_259,C_260] :
      ( k7_subset_1(A_258,B_259,C_260) = k4_xboole_0(B_259,C_260)
      | ~ m1_subset_1(B_259,k1_zfmisc_1(A_258)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7715,plain,(
    ! [C_260] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_260) = k4_xboole_0('#skF_2',C_260) ),
    inference(resolution,[status(thm)],[c_38,c_7697])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_137,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1145,plain,(
    ! [A_109,B_110] :
      ( k4_subset_1(u1_struct_0(A_109),B_110,k2_tops_1(A_109,B_110)) = k2_pre_topc(A_109,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_pre_topc(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1161,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1145])).

tff(c_1169,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1161])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_194,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_50])).

tff(c_522,plain,(
    ! [A_83,B_84,C_85] :
      ( k7_subset_1(A_83,B_84,C_85) = k4_xboole_0(B_84,C_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_636,plain,(
    ! [C_90] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_90) = k4_xboole_0('#skF_2',C_90) ),
    inference(resolution,[status(thm)],[c_38,c_522])).

tff(c_648,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_636])).

tff(c_20,plain,(
    ! [A_20,B_21] : k6_subset_1(A_20,B_21) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_15,B_16] : m1_subset_1(k6_subset_1(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_15,B_16] : m1_subset_1(k4_xboole_0(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16])).

tff(c_128,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_135,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(resolution,[status(thm)],[c_51,c_128])).

tff(c_154,plain,(
    ! [A_55,B_56] :
      ( k2_xboole_0(A_55,B_56) = B_56
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_161,plain,(
    ! [A_15,B_16] : k2_xboole_0(k4_xboole_0(A_15,B_16),A_15) = A_15 ),
    inference(resolution,[status(thm)],[c_135,c_154])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_139,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_199,plain,(
    ! [B_63,A_64] : k3_tarski(k2_tarski(B_63,A_64)) = k2_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_139])).

tff(c_14,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_222,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_14])).

tff(c_260,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = A_15 ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_222])).

tff(c_683,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_260])).

tff(c_666,plain,(
    ! [A_91,B_92] :
      ( m1_subset_1(k2_tops_1(A_91,B_92),k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_673,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k2_tops_1(A_91,B_92),u1_struct_0(A_91))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91) ) ),
    inference(resolution,[status(thm)],[c_666,c_24])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(A_25,k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_799,plain,(
    ! [A_97,B_98,C_99] :
      ( k4_subset_1(A_97,B_98,C_99) = k2_xboole_0(B_98,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3414,plain,(
    ! [B_161,B_162,A_163] :
      ( k4_subset_1(B_161,B_162,A_163) = k2_xboole_0(B_162,A_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(B_161))
      | ~ r1_tarski(A_163,B_161) ) ),
    inference(resolution,[status(thm)],[c_26,c_799])).

tff(c_3870,plain,(
    ! [A_168] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_168) = k2_xboole_0('#skF_2',A_168)
      | ~ r1_tarski(A_168,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_38,c_3414])).

tff(c_3874,plain,(
    ! [B_92] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_92)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_673,c_3870])).

tff(c_7295,plain,(
    ! [B_225] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_225)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_225))
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_3874])).

tff(c_7318,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_7295])).

tff(c_7327,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_683,c_7318])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_733,plain,(
    ! [A_93,B_94] :
      ( v4_pre_topc(k2_pre_topc(A_93,B_94),A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_749,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_733])).

tff(c_757,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_749])).

tff(c_7329,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7327,c_757])).

tff(c_7331,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_7329])).

tff(c_7332,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_7741,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7715,c_7332])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_7333,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_7999,plain,(
    ! [A_272,B_273] :
      ( r1_tarski(k2_tops_1(A_272,B_273),B_273)
      | ~ v4_pre_topc(B_273,A_272)
      | ~ m1_subset_1(B_273,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_pre_topc(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8015,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_7999])).

tff(c_8023,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7333,c_8015])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8030,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_8023,c_8])).

tff(c_8089,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_8030])).

tff(c_8557,plain,(
    ! [A_291,B_292] :
      ( k7_subset_1(u1_struct_0(A_291),B_292,k2_tops_1(A_291,B_292)) = k1_tops_1(A_291,B_292)
      | ~ m1_subset_1(B_292,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ l1_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_8573,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_8557])).

tff(c_8581,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_7715,c_8573])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8594,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8581,c_10])).

tff(c_8612,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8089,c_8594])).

tff(c_8614,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7741,c_8612])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 21:09:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.85/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.47  
% 6.85/2.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.48  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 6.85/2.48  
% 6.85/2.48  %Foreground sorts:
% 6.85/2.48  
% 6.85/2.48  
% 6.85/2.48  %Background operators:
% 6.85/2.48  
% 6.85/2.48  
% 6.85/2.48  %Foreground operators:
% 6.85/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.85/2.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.85/2.48  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.85/2.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.85/2.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.85/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.85/2.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.85/2.48  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.85/2.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.85/2.48  tff('#skF_2', type, '#skF_2': $i).
% 6.85/2.48  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.85/2.48  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 6.85/2.48  tff('#skF_1', type, '#skF_1': $i).
% 6.85/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.85/2.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.85/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.85/2.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.85/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.85/2.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.85/2.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.85/2.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.85/2.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.85/2.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.85/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.85/2.48  
% 6.85/2.49  tff(f_110, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 6.85/2.49  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.85/2.49  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 6.85/2.49  tff(f_53, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 6.85/2.49  tff(f_45, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 6.85/2.49  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.85/2.49  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.85/2.49  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.85/2.49  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.85/2.49  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.85/2.49  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.85/2.49  tff(f_75, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 6.85/2.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.85/2.49  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 6.85/2.49  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.85/2.49  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 6.85/2.49  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.85/2.49  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.85/2.49  tff(c_7697, plain, (![A_258, B_259, C_260]: (k7_subset_1(A_258, B_259, C_260)=k4_xboole_0(B_259, C_260) | ~m1_subset_1(B_259, k1_zfmisc_1(A_258)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.85/2.49  tff(c_7715, plain, (![C_260]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_260)=k4_xboole_0('#skF_2', C_260))), inference(resolution, [status(thm)], [c_38, c_7697])).
% 6.85/2.49  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.85/2.49  tff(c_137, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 6.85/2.49  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.85/2.49  tff(c_1145, plain, (![A_109, B_110]: (k4_subset_1(u1_struct_0(A_109), B_110, k2_tops_1(A_109, B_110))=k2_pre_topc(A_109, B_110) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_pre_topc(A_109))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.85/2.49  tff(c_1161, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1145])).
% 6.85/2.49  tff(c_1169, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1161])).
% 6.85/2.49  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.85/2.49  tff(c_194, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_137, c_50])).
% 6.85/2.49  tff(c_522, plain, (![A_83, B_84, C_85]: (k7_subset_1(A_83, B_84, C_85)=k4_xboole_0(B_84, C_85) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.85/2.49  tff(c_636, plain, (![C_90]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_90)=k4_xboole_0('#skF_2', C_90))), inference(resolution, [status(thm)], [c_38, c_522])).
% 6.85/2.49  tff(c_648, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_194, c_636])).
% 6.85/2.49  tff(c_20, plain, (![A_20, B_21]: (k6_subset_1(A_20, B_21)=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.85/2.49  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(k6_subset_1(A_15, B_16), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.85/2.49  tff(c_51, plain, (![A_15, B_16]: (m1_subset_1(k4_xboole_0(A_15, B_16), k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16])).
% 6.85/2.49  tff(c_128, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.85/2.49  tff(c_135, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(resolution, [status(thm)], [c_51, c_128])).
% 6.85/2.49  tff(c_154, plain, (![A_55, B_56]: (k2_xboole_0(A_55, B_56)=B_56 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.85/2.49  tff(c_161, plain, (![A_15, B_16]: (k2_xboole_0(k4_xboole_0(A_15, B_16), A_15)=A_15)), inference(resolution, [status(thm)], [c_135, c_154])).
% 6.85/2.49  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.85/2.49  tff(c_139, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.85/2.49  tff(c_199, plain, (![B_63, A_64]: (k3_tarski(k2_tarski(B_63, A_64))=k2_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_12, c_139])).
% 6.85/2.49  tff(c_14, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.85/2.49  tff(c_222, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_199, c_14])).
% 6.85/2.49  tff(c_260, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(A_15, B_16))=A_15)), inference(superposition, [status(thm), theory('equality')], [c_161, c_222])).
% 6.85/2.49  tff(c_683, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_648, c_260])).
% 6.85/2.49  tff(c_666, plain, (![A_91, B_92]: (m1_subset_1(k2_tops_1(A_91, B_92), k1_zfmisc_1(u1_struct_0(A_91))) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.85/2.49  tff(c_24, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.85/2.49  tff(c_673, plain, (![A_91, B_92]: (r1_tarski(k2_tops_1(A_91, B_92), u1_struct_0(A_91)) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91))), inference(resolution, [status(thm)], [c_666, c_24])).
% 6.85/2.49  tff(c_26, plain, (![A_25, B_26]: (m1_subset_1(A_25, k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.85/2.49  tff(c_799, plain, (![A_97, B_98, C_99]: (k4_subset_1(A_97, B_98, C_99)=k2_xboole_0(B_98, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(A_97)) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.85/2.49  tff(c_3414, plain, (![B_161, B_162, A_163]: (k4_subset_1(B_161, B_162, A_163)=k2_xboole_0(B_162, A_163) | ~m1_subset_1(B_162, k1_zfmisc_1(B_161)) | ~r1_tarski(A_163, B_161))), inference(resolution, [status(thm)], [c_26, c_799])).
% 6.85/2.49  tff(c_3870, plain, (![A_168]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_168)=k2_xboole_0('#skF_2', A_168) | ~r1_tarski(A_168, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_38, c_3414])).
% 6.85/2.49  tff(c_3874, plain, (![B_92]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_92))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_673, c_3870])).
% 6.85/2.49  tff(c_7295, plain, (![B_225]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_225))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_225)) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_3874])).
% 6.85/2.49  tff(c_7318, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_7295])).
% 6.85/2.49  tff(c_7327, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1169, c_683, c_7318])).
% 6.85/2.49  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 6.85/2.49  tff(c_733, plain, (![A_93, B_94]: (v4_pre_topc(k2_pre_topc(A_93, B_94), A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.85/2.49  tff(c_749, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_733])).
% 6.85/2.49  tff(c_757, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_749])).
% 6.85/2.49  tff(c_7329, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7327, c_757])).
% 6.85/2.49  tff(c_7331, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_7329])).
% 6.85/2.49  tff(c_7332, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 6.85/2.49  tff(c_7741, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7715, c_7332])).
% 6.85/2.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.85/2.49  tff(c_7333, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 6.85/2.49  tff(c_7999, plain, (![A_272, B_273]: (r1_tarski(k2_tops_1(A_272, B_273), B_273) | ~v4_pre_topc(B_273, A_272) | ~m1_subset_1(B_273, k1_zfmisc_1(u1_struct_0(A_272))) | ~l1_pre_topc(A_272))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.85/2.49  tff(c_8015, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_7999])).
% 6.85/2.49  tff(c_8023, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7333, c_8015])).
% 6.85/2.49  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.85/2.49  tff(c_8030, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_8023, c_8])).
% 6.85/2.49  tff(c_8089, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2, c_8030])).
% 6.85/2.49  tff(c_8557, plain, (![A_291, B_292]: (k7_subset_1(u1_struct_0(A_291), B_292, k2_tops_1(A_291, B_292))=k1_tops_1(A_291, B_292) | ~m1_subset_1(B_292, k1_zfmisc_1(u1_struct_0(A_291))) | ~l1_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.85/2.49  tff(c_8573, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_8557])).
% 6.85/2.49  tff(c_8581, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_7715, c_8573])).
% 6.85/2.49  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.85/2.49  tff(c_8594, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8581, c_10])).
% 6.85/2.49  tff(c_8612, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8089, c_8594])).
% 6.85/2.49  tff(c_8614, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7741, c_8612])).
% 6.85/2.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.49  
% 6.85/2.49  Inference rules
% 6.85/2.49  ----------------------
% 6.85/2.49  #Ref     : 0
% 6.85/2.49  #Sup     : 2156
% 6.85/2.49  #Fact    : 0
% 6.85/2.49  #Define  : 0
% 6.85/2.49  #Split   : 1
% 6.85/2.49  #Chain   : 0
% 6.85/2.49  #Close   : 0
% 6.85/2.49  
% 6.85/2.49  Ordering : KBO
% 6.85/2.49  
% 6.85/2.49  Simplification rules
% 6.85/2.49  ----------------------
% 6.85/2.49  #Subsume      : 100
% 6.85/2.49  #Demod        : 2598
% 6.85/2.49  #Tautology    : 1497
% 6.85/2.49  #SimpNegUnit  : 3
% 6.85/2.49  #BackRed      : 16
% 6.85/2.49  
% 6.85/2.49  #Partial instantiations: 0
% 6.85/2.49  #Strategies tried      : 1
% 6.85/2.49  
% 6.85/2.49  Timing (in seconds)
% 6.85/2.49  ----------------------
% 6.85/2.49  Preprocessing        : 0.32
% 6.85/2.50  Parsing              : 0.17
% 6.85/2.50  CNF conversion       : 0.02
% 6.85/2.50  Main loop            : 1.31
% 6.85/2.50  Inferencing          : 0.36
% 6.85/2.50  Reduction            : 0.64
% 6.85/2.50  Demodulation         : 0.55
% 6.85/2.50  BG Simplification    : 0.04
% 6.85/2.50  Subsumption          : 0.18
% 6.85/2.50  Abstraction          : 0.06
% 6.85/2.50  MUC search           : 0.00
% 6.85/2.50  Cooper               : 0.00
% 6.85/2.50  Total                : 1.66
% 6.85/2.50  Index Insertion      : 0.00
% 6.85/2.50  Index Deletion       : 0.00
% 6.85/2.50  Index Matching       : 0.00
% 6.85/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
