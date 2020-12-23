%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1281+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:42 EST 2020

% Result     : Theorem 5.52s
% Output     : CNFRefutation 5.52s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 163 expanded)
%              Number of leaves         :   28 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 293 expanded)
%              Number of equality atoms :   28 (  60 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_tops_1 > r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v5_tops_1,type,(
    v5_tops_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v5_tops_1(B,A)
             => r1_tarski(k2_tops_1(A,B),k2_pre_topc(A,k1_tops_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tops_1)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v5_tops_1(B,A)
          <=> B = k2_pre_topc(A,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k1_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k2_pre_topc(A,k2_pre_topc(A,B)) = k2_pre_topc(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

tff(f_78,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    v5_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_807,plain,(
    ! [A_100,B_101] :
      ( k2_pre_topc(A_100,k1_tops_1(A_100,B_101)) = B_101
      | ~ v5_tops_1(B_101,A_100)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_824,plain,
    ( k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ v5_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_807])).

tff(c_837,plain,(
    k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_824])).

tff(c_30,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_838,plain,(
    ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_837,c_30])).

tff(c_151,plain,(
    ! [A_55,B_56,C_57] :
      ( k9_subset_1(A_55,B_56,C_57) = k3_xboole_0(B_56,C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_160,plain,(
    ! [B_56] : k9_subset_1(u1_struct_0('#skF_1'),B_56,'#skF_2') = k3_xboole_0(B_56,'#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_151])).

tff(c_241,plain,(
    ! [A_66,C_67,B_68] :
      ( k9_subset_1(A_66,C_67,B_68) = k9_subset_1(A_66,B_68,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_249,plain,(
    ! [B_68] : k9_subset_1(u1_struct_0('#skF_1'),B_68,'#skF_2') = k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_68) ),
    inference(resolution,[status(thm)],[c_34,c_241])).

tff(c_254,plain,(
    ! [B_68] : k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',B_68) = k3_xboole_0(B_68,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_249])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k1_tops_1(A_10,B_11),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_621,plain,(
    ! [A_89,B_90] :
      ( k2_pre_topc(A_89,k2_pre_topc(A_89,B_90)) = k2_pre_topc(A_89,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4123,plain,(
    ! [A_216,B_217] :
      ( k2_pre_topc(A_216,k2_pre_topc(A_216,k1_tops_1(A_216,B_217))) = k2_pre_topc(A_216,k1_tops_1(A_216,B_217))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_216)))
      | ~ l1_pre_topc(A_216) ) ),
    inference(resolution,[status(thm)],[c_10,c_621])).

tff(c_4163,plain,
    ( k2_pre_topc('#skF_1',k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))) = k2_pre_topc('#skF_1',k1_tops_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4123])).

tff(c_4207,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_837,c_837,c_4163])).

tff(c_4,plain,(
    ! [A_4,B_6] :
      ( k9_subset_1(u1_struct_0(A_4),k2_pre_topc(A_4,B_6),k2_pre_topc(A_4,k3_subset_1(u1_struct_0(A_4),B_6))) = k2_tops_1(A_4,B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_4)))
      | ~ l1_pre_topc(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4212,plain,
    ( k9_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'))) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4207,c_4])).

tff(c_4216,plain,(
    k3_xboole_0(k2_pre_topc('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_254,c_4212])).

tff(c_161,plain,(
    ! [B_58] : k9_subset_1(u1_struct_0('#skF_1'),B_58,'#skF_2') = k3_xboole_0(B_58,'#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_151])).

tff(c_24,plain,(
    ! [A_27,B_28] : r1_tarski(k3_xboole_0(A_27,B_28),A_27) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,k1_zfmisc_1(B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_48,plain,(
    ! [A_38,B_39,C_40] :
      ( k9_subset_1(A_38,B_39,B_39) = B_39
      | ~ m1_subset_1(C_40,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    ! [B_42,B_43,A_44] :
      ( k9_subset_1(B_42,B_43,B_43) = B_43
      | ~ r1_tarski(A_44,B_42) ) ),
    inference(resolution,[status(thm)],[c_28,c_48])).

tff(c_71,plain,(
    ! [A_27,B_43] : k9_subset_1(A_27,B_43,B_43) = B_43 ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_168,plain,(
    k3_xboole_0('#skF_2','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_71])).

tff(c_181,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_24])).

tff(c_186,plain,(
    ! [B_59,B_60,A_61] :
      ( k9_subset_1(B_59,B_60,A_61) = k3_xboole_0(B_60,A_61)
      | ~ r1_tarski(A_61,B_59) ) ),
    inference(resolution,[status(thm)],[c_28,c_151])).

tff(c_195,plain,(
    ! [B_60] : k9_subset_1('#skF_2',B_60,'#skF_2') = k3_xboole_0(B_60,'#skF_2') ),
    inference(resolution,[status(thm)],[c_181,c_186])).

tff(c_219,plain,(
    ! [A_63,B_64,C_65] :
      ( m1_subset_1(k9_subset_1(A_63,B_64,C_65),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_370,plain,(
    ! [A_78,B_79,C_80] :
      ( r1_tarski(k9_subset_1(A_78,B_79,C_80),A_78)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_219,c_26])).

tff(c_381,plain,(
    ! [B_60] :
      ( r1_tarski(k3_xboole_0(B_60,'#skF_2'),'#skF_2')
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_370])).

tff(c_394,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_397,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_394])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_397])).

tff(c_402,plain,(
    ! [B_60] : r1_tarski(k3_xboole_0(B_60,'#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_4311,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4216,c_402])).

tff(c_4349,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_838,c_4311])).

%------------------------------------------------------------------------------
