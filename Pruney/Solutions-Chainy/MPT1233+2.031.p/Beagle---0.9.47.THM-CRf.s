%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:20:34 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 457 expanded)
%              Number of leaves         :   46 ( 170 expanded)
%              Depth                    :   18
%              Number of atoms          :  150 ( 719 expanded)
%              Number of equality atoms :   44 ( 290 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k1_struct_0,type,(
    k1_struct_0: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => k1_tops_1(A,k2_struct_0(A)) = k2_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_50,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_60,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => v1_xboole_0(k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = k3_subset_1(u1_struct_0(A),k1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_52,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_129,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k3_subset_1(u1_struct_0(A),k2_pre_topc(A,k3_subset_1(u1_struct_0(A),B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

tff(c_58,plain,(
    k1_tops_1('#skF_2',k2_struct_0('#skF_2')) != k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_60,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_46,plain,(
    ! [A_43] :
      ( l1_struct_0(A_43)
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18,plain,(
    ! [A_11] : k1_subset_1(A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = k2_subset_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_64,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_28])).

tff(c_65,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_64])).

tff(c_48,plain,(
    ! [A_44] :
      ( v1_xboole_0(k1_struct_0(A_44))
      | ~ l1_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_129,plain,(
    ! [B_62,A_63] :
      ( ~ v1_xboole_0(B_62)
      | B_62 = A_63
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    ! [A_64] :
      ( k1_xboole_0 = A_64
      | ~ v1_xboole_0(A_64) ) ),
    inference(resolution,[status(thm)],[c_2,c_129])).

tff(c_147,plain,(
    ! [A_67] :
      ( k1_struct_0(A_67) = k1_xboole_0
      | ~ l1_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_48,c_136])).

tff(c_152,plain,(
    ! [A_68] :
      ( k1_struct_0(A_68) = k1_xboole_0
      | ~ l1_pre_topc(A_68) ) ),
    inference(resolution,[status(thm)],[c_46,c_147])).

tff(c_156,plain,(
    k1_struct_0('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_152])).

tff(c_520,plain,(
    ! [A_108] :
      ( k3_subset_1(u1_struct_0(A_108),k1_struct_0(A_108)) = k2_struct_0(A_108)
      | ~ l1_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_529,plain,
    ( k3_subset_1(u1_struct_0('#skF_2'),k1_xboole_0) = k2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_520])).

tff(c_532,plain,
    ( u1_struct_0('#skF_2') = k2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_529])).

tff(c_536,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_532])).

tff(c_539,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_536])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_539])).

tff(c_545,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_532])).

tff(c_544,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_532])).

tff(c_44,plain,(
    ! [A_42] :
      ( m1_subset_1(k2_struct_0(A_42),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_582,plain,
    ( m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_44])).

tff(c_588,plain,(
    m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_582])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_599,plain,(
    r1_tarski(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_588,c_30])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_603,plain,(
    k4_xboole_0(k2_struct_0('#skF_2'),k2_struct_0('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_599,c_6])).

tff(c_26,plain,(
    ! [A_17,B_18] : k6_subset_1(A_17,B_18) = k4_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_22,plain,(
    ! [A_13,B_14] : m1_subset_1(k6_subset_1(A_13,B_14),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_63,plain,(
    ! [A_13,B_14] : m1_subset_1(k4_xboole_0(A_13,B_14),k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_620,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_63])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_838,plain,(
    ! [B_141,A_142] :
      ( v4_pre_topc(B_141,A_142)
      | ~ v1_xboole_0(B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_841,plain,(
    ! [B_141] :
      ( v4_pre_topc(B_141,'#skF_2')
      | ~ v1_xboole_0(B_141)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_838])).

tff(c_954,plain,(
    ! [B_148] :
      ( v4_pre_topc(B_148,'#skF_2')
      | ~ v1_xboole_0(B_148)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_841])).

tff(c_957,plain,
    ( v4_pre_topc(k1_xboole_0,'#skF_2')
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_620,c_954])).

tff(c_975,plain,(
    v4_pre_topc(k1_xboole_0,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_957])).

tff(c_426,plain,(
    ! [A_97] :
      ( m1_subset_1(k2_struct_0(A_97),k1_zfmisc_1(u1_struct_0(A_97)))
      | ~ l1_struct_0(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_690,plain,(
    ! [A_122] :
      ( r1_tarski(k2_struct_0(A_122),u1_struct_0(A_122))
      | ~ l1_struct_0(A_122) ) ),
    inference(resolution,[status(thm)],[c_426,c_30])).

tff(c_918,plain,(
    ! [A_147] :
      ( k4_xboole_0(k2_struct_0(A_147),u1_struct_0(A_147)) = k1_xboole_0
      | ~ l1_struct_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_690,c_6])).

tff(c_940,plain,(
    ! [A_147] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(A_147)))
      | ~ l1_struct_0(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_63])).

tff(c_1024,plain,(
    ! [A_154,B_155] :
      ( k2_pre_topc(A_154,B_155) = B_155
      | ~ v4_pre_topc(B_155,A_154)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1027,plain,(
    ! [B_155] :
      ( k2_pre_topc('#skF_2',B_155) = B_155
      | ~ v4_pre_topc(B_155,'#skF_2')
      | ~ m1_subset_1(B_155,k1_zfmisc_1(k2_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_1024])).

tff(c_1085,plain,(
    ! [B_161] :
      ( k2_pre_topc('#skF_2',B_161) = B_161
      | ~ v4_pre_topc(B_161,'#skF_2')
      | ~ m1_subset_1(B_161,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1027])).

tff(c_1089,plain,
    ( k2_pre_topc('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ v4_pre_topc(k1_xboole_0,'#skF_2')
    | ~ l1_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_940,c_1085])).

tff(c_1110,plain,(
    k2_pre_topc('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_975,c_1089])).

tff(c_991,plain,(
    ! [A_150] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_struct_0(A_150)))
      | ~ l1_struct_0(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_918,c_63])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( k3_subset_1(A_15,k3_subset_1(A_15,B_16)) = B_16
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_997,plain,(
    ! [A_150] :
      ( k3_subset_1(k2_struct_0(A_150),k3_subset_1(k2_struct_0(A_150),k1_xboole_0)) = k1_xboole_0
      | ~ l1_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_991,c_24])).

tff(c_1007,plain,(
    ! [A_150] :
      ( k3_subset_1(k2_struct_0(A_150),k2_struct_0(A_150)) = k1_xboole_0
      | ~ l1_struct_0(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_997])).

tff(c_1445,plain,(
    ! [A_177,B_178] :
      ( k3_subset_1(u1_struct_0(A_177),k2_pre_topc(A_177,k3_subset_1(u1_struct_0(A_177),B_178))) = k1_tops_1(A_177,B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0(A_177)))
      | ~ l1_pre_topc(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1463,plain,(
    ! [B_178] :
      ( k3_subset_1(u1_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_178))) = k1_tops_1('#skF_2',B_178)
      | ~ m1_subset_1(B_178,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_544,c_1445])).

tff(c_1557,plain,(
    ! [B_182] :
      ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k3_subset_1(k2_struct_0('#skF_2'),B_182))) = k1_tops_1('#skF_2',B_182)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k2_struct_0('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_544,c_544,c_1463])).

tff(c_1580,plain,
    ( k3_subset_1(k2_struct_0('#skF_2'),k2_pre_topc('#skF_2',k1_xboole_0)) = k1_tops_1('#skF_2',k2_struct_0('#skF_2'))
    | ~ m1_subset_1(k2_struct_0('#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_2')))
    | ~ l1_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1007,c_1557])).

tff(c_1591,plain,(
    k1_tops_1('#skF_2',k2_struct_0('#skF_2')) = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_545,c_588,c_65,c_1110,c_1580])).

tff(c_1593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1591])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.58  
% 3.56/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.58  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k3_mcart_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > k1_subset_1 > k1_struct_0 > k1_xboole_0 > #skF_1 > #skF_2
% 3.56/1.58  
% 3.56/1.58  %Foreground sorts:
% 3.56/1.58  
% 3.56/1.58  
% 3.56/1.58  %Background operators:
% 3.56/1.58  
% 3.56/1.58  
% 3.56/1.58  %Foreground operators:
% 3.56/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.56/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.56/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.56/1.58  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.56/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.56/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.56/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.56/1.58  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.56/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.58  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.56/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.56/1.58  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.56/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.58  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.56/1.58  tff(k1_struct_0, type, k1_struct_0: $i > $i).
% 3.56/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.56/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.56/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.56/1.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.56/1.58  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.56/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.56/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.58  
% 3.56/1.60  tff(f_143, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (k1_tops_1(A, k2_struct_0(A)) = k2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tops_1)).
% 3.56/1.60  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.56/1.60  tff(f_48, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.56/1.60  tff(f_50, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.56/1.60  tff(f_60, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.56/1.60  tff(f_110, axiom, (![A]: (l1_struct_0(A) => v1_xboole_0(k1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_struct_0)).
% 3.56/1.60  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.56/1.60  tff(f_44, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.56/1.60  tff(f_114, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = k3_subset_1(u1_struct_0(A), k1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_pre_topc)).
% 3.56/1.60  tff(f_102, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.56/1.60  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.56/1.60  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.56/1.60  tff(f_58, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.56/1.60  tff(f_52, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.56/1.60  tff(f_98, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 3.56/1.60  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.56/1.60  tff(f_56, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.56/1.60  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k3_subset_1(u1_struct_0(A), k2_pre_topc(A, k3_subset_1(u1_struct_0(A), B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tops_1)).
% 3.56/1.60  tff(c_58, plain, (k1_tops_1('#skF_2', k2_struct_0('#skF_2'))!=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.60  tff(c_60, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.60  tff(c_46, plain, (![A_43]: (l1_struct_0(A_43) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.60  tff(c_18, plain, (![A_11]: (k1_subset_1(A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.56/1.60  tff(c_20, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.56/1.60  tff(c_28, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=k2_subset_1(A_19))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.56/1.60  tff(c_64, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_28])).
% 3.56/1.60  tff(c_65, plain, (![A_19]: (k3_subset_1(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_64])).
% 3.56/1.60  tff(c_48, plain, (![A_44]: (v1_xboole_0(k1_struct_0(A_44)) | ~l1_struct_0(A_44))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.56/1.60  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.56/1.60  tff(c_129, plain, (![B_62, A_63]: (~v1_xboole_0(B_62) | B_62=A_63 | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.56/1.60  tff(c_136, plain, (![A_64]: (k1_xboole_0=A_64 | ~v1_xboole_0(A_64))), inference(resolution, [status(thm)], [c_2, c_129])).
% 3.56/1.60  tff(c_147, plain, (![A_67]: (k1_struct_0(A_67)=k1_xboole_0 | ~l1_struct_0(A_67))), inference(resolution, [status(thm)], [c_48, c_136])).
% 3.56/1.60  tff(c_152, plain, (![A_68]: (k1_struct_0(A_68)=k1_xboole_0 | ~l1_pre_topc(A_68))), inference(resolution, [status(thm)], [c_46, c_147])).
% 3.56/1.60  tff(c_156, plain, (k1_struct_0('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_152])).
% 3.56/1.60  tff(c_520, plain, (![A_108]: (k3_subset_1(u1_struct_0(A_108), k1_struct_0(A_108))=k2_struct_0(A_108) | ~l1_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.56/1.60  tff(c_529, plain, (k3_subset_1(u1_struct_0('#skF_2'), k1_xboole_0)=k2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_156, c_520])).
% 3.56/1.60  tff(c_532, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2') | ~l1_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_529])).
% 3.56/1.60  tff(c_536, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_532])).
% 3.56/1.60  tff(c_539, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_46, c_536])).
% 3.56/1.60  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_539])).
% 3.56/1.60  tff(c_545, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_532])).
% 3.56/1.60  tff(c_544, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_532])).
% 3.56/1.60  tff(c_44, plain, (![A_42]: (m1_subset_1(k2_struct_0(A_42), k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.56/1.60  tff(c_582, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_544, c_44])).
% 3.56/1.60  tff(c_588, plain, (m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_545, c_582])).
% 3.56/1.60  tff(c_30, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.56/1.60  tff(c_599, plain, (r1_tarski(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_588, c_30])).
% 3.56/1.60  tff(c_6, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.56/1.60  tff(c_603, plain, (k4_xboole_0(k2_struct_0('#skF_2'), k2_struct_0('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_599, c_6])).
% 3.56/1.60  tff(c_26, plain, (![A_17, B_18]: (k6_subset_1(A_17, B_18)=k4_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.56/1.60  tff(c_22, plain, (![A_13, B_14]: (m1_subset_1(k6_subset_1(A_13, B_14), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.56/1.60  tff(c_63, plain, (![A_13, B_14]: (m1_subset_1(k4_xboole_0(A_13, B_14), k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22])).
% 3.56/1.60  tff(c_620, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_struct_0('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_603, c_63])).
% 3.56/1.60  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.56/1.60  tff(c_838, plain, (![B_141, A_142]: (v4_pre_topc(B_141, A_142) | ~v1_xboole_0(B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.56/1.60  tff(c_841, plain, (![B_141]: (v4_pre_topc(B_141, '#skF_2') | ~v1_xboole_0(B_141) | ~m1_subset_1(B_141, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_544, c_838])).
% 3.56/1.60  tff(c_954, plain, (![B_148]: (v4_pre_topc(B_148, '#skF_2') | ~v1_xboole_0(B_148) | ~m1_subset_1(B_148, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_841])).
% 3.56/1.60  tff(c_957, plain, (v4_pre_topc(k1_xboole_0, '#skF_2') | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_620, c_954])).
% 3.56/1.60  tff(c_975, plain, (v4_pre_topc(k1_xboole_0, '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_957])).
% 3.56/1.60  tff(c_426, plain, (![A_97]: (m1_subset_1(k2_struct_0(A_97), k1_zfmisc_1(u1_struct_0(A_97))) | ~l1_struct_0(A_97))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.56/1.60  tff(c_690, plain, (![A_122]: (r1_tarski(k2_struct_0(A_122), u1_struct_0(A_122)) | ~l1_struct_0(A_122))), inference(resolution, [status(thm)], [c_426, c_30])).
% 3.56/1.60  tff(c_918, plain, (![A_147]: (k4_xboole_0(k2_struct_0(A_147), u1_struct_0(A_147))=k1_xboole_0 | ~l1_struct_0(A_147))), inference(resolution, [status(thm)], [c_690, c_6])).
% 3.56/1.60  tff(c_940, plain, (![A_147]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_struct_0(A_147))) | ~l1_struct_0(A_147))), inference(superposition, [status(thm), theory('equality')], [c_918, c_63])).
% 3.56/1.60  tff(c_1024, plain, (![A_154, B_155]: (k2_pre_topc(A_154, B_155)=B_155 | ~v4_pre_topc(B_155, A_154) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.56/1.60  tff(c_1027, plain, (![B_155]: (k2_pre_topc('#skF_2', B_155)=B_155 | ~v4_pre_topc(B_155, '#skF_2') | ~m1_subset_1(B_155, k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_544, c_1024])).
% 3.56/1.60  tff(c_1085, plain, (![B_161]: (k2_pre_topc('#skF_2', B_161)=B_161 | ~v4_pre_topc(B_161, '#skF_2') | ~m1_subset_1(B_161, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1027])).
% 3.56/1.60  tff(c_1089, plain, (k2_pre_topc('#skF_2', k1_xboole_0)=k1_xboole_0 | ~v4_pre_topc(k1_xboole_0, '#skF_2') | ~l1_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_940, c_1085])).
% 3.56/1.60  tff(c_1110, plain, (k2_pre_topc('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_545, c_975, c_1089])).
% 3.56/1.60  tff(c_991, plain, (![A_150]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_struct_0(A_150))) | ~l1_struct_0(A_150))), inference(superposition, [status(thm), theory('equality')], [c_918, c_63])).
% 3.56/1.60  tff(c_24, plain, (![A_15, B_16]: (k3_subset_1(A_15, k3_subset_1(A_15, B_16))=B_16 | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.56/1.60  tff(c_997, plain, (![A_150]: (k3_subset_1(k2_struct_0(A_150), k3_subset_1(k2_struct_0(A_150), k1_xboole_0))=k1_xboole_0 | ~l1_struct_0(A_150))), inference(resolution, [status(thm)], [c_991, c_24])).
% 3.56/1.60  tff(c_1007, plain, (![A_150]: (k3_subset_1(k2_struct_0(A_150), k2_struct_0(A_150))=k1_xboole_0 | ~l1_struct_0(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_997])).
% 3.56/1.60  tff(c_1445, plain, (![A_177, B_178]: (k3_subset_1(u1_struct_0(A_177), k2_pre_topc(A_177, k3_subset_1(u1_struct_0(A_177), B_178)))=k1_tops_1(A_177, B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0(A_177))) | ~l1_pre_topc(A_177))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.56/1.60  tff(c_1463, plain, (![B_178]: (k3_subset_1(u1_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_178)))=k1_tops_1('#skF_2', B_178) | ~m1_subset_1(B_178, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_544, c_1445])).
% 3.56/1.60  tff(c_1557, plain, (![B_182]: (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k3_subset_1(k2_struct_0('#skF_2'), B_182)))=k1_tops_1('#skF_2', B_182) | ~m1_subset_1(B_182, k1_zfmisc_1(k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_544, c_544, c_1463])).
% 3.56/1.60  tff(c_1580, plain, (k3_subset_1(k2_struct_0('#skF_2'), k2_pre_topc('#skF_2', k1_xboole_0))=k1_tops_1('#skF_2', k2_struct_0('#skF_2')) | ~m1_subset_1(k2_struct_0('#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_2'))) | ~l1_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1007, c_1557])).
% 3.56/1.60  tff(c_1591, plain, (k1_tops_1('#skF_2', k2_struct_0('#skF_2'))=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_545, c_588, c_65, c_1110, c_1580])).
% 3.56/1.60  tff(c_1593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1591])).
% 3.56/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.60  
% 3.56/1.60  Inference rules
% 3.56/1.60  ----------------------
% 3.56/1.60  #Ref     : 0
% 3.56/1.60  #Sup     : 377
% 3.56/1.60  #Fact    : 0
% 3.56/1.60  #Define  : 0
% 3.56/1.60  #Split   : 2
% 3.56/1.60  #Chain   : 0
% 3.56/1.60  #Close   : 0
% 3.56/1.60  
% 3.56/1.60  Ordering : KBO
% 3.56/1.60  
% 3.56/1.60  Simplification rules
% 3.56/1.60  ----------------------
% 3.56/1.60  #Subsume      : 58
% 3.56/1.60  #Demod        : 207
% 3.56/1.60  #Tautology    : 190
% 3.56/1.60  #SimpNegUnit  : 1
% 3.56/1.60  #BackRed      : 0
% 3.56/1.60  
% 3.56/1.60  #Partial instantiations: 0
% 3.56/1.60  #Strategies tried      : 1
% 3.56/1.60  
% 3.56/1.60  Timing (in seconds)
% 3.56/1.60  ----------------------
% 3.86/1.60  Preprocessing        : 0.35
% 3.86/1.60  Parsing              : 0.19
% 3.86/1.60  CNF conversion       : 0.02
% 3.86/1.60  Main loop            : 0.48
% 3.86/1.60  Inferencing          : 0.18
% 3.86/1.61  Reduction            : 0.16
% 3.86/1.61  Demodulation         : 0.11
% 3.86/1.61  BG Simplification    : 0.02
% 3.86/1.61  Subsumption          : 0.07
% 3.86/1.61  Abstraction          : 0.03
% 3.86/1.61  MUC search           : 0.00
% 3.86/1.61  Cooper               : 0.00
% 3.86/1.61  Total                : 0.87
% 3.86/1.61  Index Insertion      : 0.00
% 3.86/1.61  Index Deletion       : 0.00
% 3.86/1.61  Index Matching       : 0.00
% 3.86/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
