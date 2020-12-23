%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:20 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 275 expanded)
%              Number of leaves         :   44 ( 108 expanded)
%              Depth                    :   13
%              Number of atoms          :  188 ( 774 expanded)
%              Number of equality atoms :   18 ( 100 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_32,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v3_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_30,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_36,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_44,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    ! [A_4] : r1_tarski('#skF_3',A_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_69,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2])).

tff(c_18,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_63,plain,(
    ! [A_10] : m1_subset_1('#skF_3',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_262,plain,(
    ! [B_82,A_83] :
      ( v3_pre_topc(B_82,A_83)
      | ~ v1_xboole_0(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_266,plain,(
    ! [A_83] :
      ( v3_pre_topc('#skF_3',A_83)
      | ~ v1_xboole_0('#skF_3')
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(resolution,[status(thm)],[c_63,c_262])).

tff(c_273,plain,(
    ! [A_83] :
      ( v3_pre_topc('#skF_3',A_83)
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_266])).

tff(c_141,plain,(
    ! [D_63] :
      ( v3_pre_topc(D_63,'#skF_1')
      | ~ r2_hidden(D_63,'#skF_3')
      | ~ m1_subset_1(D_63,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_150,plain,
    ( v3_pre_topc('#skF_3','#skF_1')
    | ~ r2_hidden('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_141])).

tff(c_152,plain,(
    ~ r2_hidden('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_278,plain,(
    ! [D_87] :
      ( r2_hidden(D_87,'#skF_3')
      | ~ r2_hidden('#skF_2',D_87)
      | ~ v4_pre_topc(D_87,'#skF_1')
      | ~ v3_pre_topc(D_87,'#skF_1')
      | ~ m1_subset_1(D_87,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_282,plain,
    ( r2_hidden('#skF_3','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_63,c_278])).

tff(c_289,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_282])).

tff(c_293,plain,(
    ~ v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_289])).

tff(c_296,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_273,c_293])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_296])).

tff(c_302,plain,(
    v3_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_289])).

tff(c_10,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_66,plain,(
    ! [A_5] : k5_xboole_0(A_5,'#skF_3') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_68,plain,(
    ! [A_3] : k3_xboole_0(A_3,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_6])).

tff(c_114,plain,(
    ! [A_58,B_59] : k5_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_123,plain,(
    ! [A_3] : k5_xboole_0(A_3,'#skF_3') = k4_xboole_0(A_3,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_114])).

tff(c_126,plain,(
    ! [A_3] : k4_xboole_0(A_3,'#skF_3') = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_123])).

tff(c_188,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,B_74) = k3_subset_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_191,plain,(
    ! [A_10] : k4_xboole_0(A_10,'#skF_3') = k3_subset_1(A_10,'#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_188])).

tff(c_196,plain,(
    ! [A_10] : k3_subset_1(A_10,'#skF_3') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_191])).

tff(c_309,plain,(
    ! [A_88,B_89] :
      ( v4_pre_topc(k3_subset_1(u1_struct_0(A_88),B_89),A_88)
      | ~ v3_pre_topc(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_313,plain,(
    ! [A_88] :
      ( v4_pre_topc(u1_struct_0(A_88),A_88)
      | ~ v3_pre_topc('#skF_3',A_88)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_309])).

tff(c_315,plain,(
    ! [A_88] :
      ( v4_pre_topc(u1_struct_0(A_88),A_88)
      | ~ v3_pre_topc('#skF_3',A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_313])).

tff(c_30,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_248,plain,(
    ! [B_79,A_80] :
      ( v4_pre_topc(B_79,A_80)
      | ~ v1_xboole_0(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0(A_80)))
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_252,plain,(
    ! [A_80] :
      ( v4_pre_topc('#skF_3',A_80)
      | ~ v1_xboole_0('#skF_3')
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(resolution,[status(thm)],[c_63,c_248])).

tff(c_259,plain,(
    ! [A_80] :
      ( v4_pre_topc('#skF_3',A_80)
      | ~ l1_pre_topc(A_80)
      | ~ v2_pre_topc(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_252])).

tff(c_336,plain,(
    ! [A_94,B_95] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(A_94),B_95),A_94)
      | ~ v4_pre_topc(B_95,A_94)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_343,plain,(
    ! [A_94] :
      ( v3_pre_topc(u1_struct_0(A_94),A_94)
      | ~ v4_pre_topc('#skF_3',A_94)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_336])).

tff(c_347,plain,(
    ! [A_96] :
      ( v3_pre_topc(u1_struct_0(A_96),A_96)
      | ~ v4_pre_topc('#skF_3',A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_343])).

tff(c_12,plain,(
    ! [A_6] : k2_subset_1(A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_65,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_151,plain,
    ( v3_pre_topc(u1_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_65,c_141])).

tff(c_164,plain,(
    ~ r2_hidden(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_286,plain,
    ( r2_hidden(u1_struct_0('#skF_1'),'#skF_3')
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1'))
    | ~ v4_pre_topc(u1_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_65,c_278])).

tff(c_292,plain,
    ( ~ r2_hidden('#skF_2',u1_struct_0('#skF_1'))
    | ~ v4_pre_topc(u1_struct_0('#skF_1'),'#skF_1')
    | ~ v3_pre_topc(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_286])).

tff(c_317,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_353,plain,
    ( ~ v4_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_347,c_317])).

tff(c_357,plain,(
    ~ v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_353])).

tff(c_360,plain,
    ( ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_259,c_357])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_360])).

tff(c_365,plain,
    ( ~ v4_pre_topc(u1_struct_0('#skF_1'),'#skF_1')
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_374,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_377,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_374])).

tff(c_380,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_377])).

tff(c_32,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_383,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_380,c_32])).

tff(c_386,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_383])).

tff(c_389,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_386])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_389])).

tff(c_394,plain,(
    ~ v4_pre_topc(u1_struct_0('#skF_1'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_407,plain,
    ( ~ v3_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_315,c_394])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_302,c_407])).

tff(c_416,plain,(
    r2_hidden(u1_struct_0('#skF_1'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_419,plain,(
    ~ r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_416,c_26])).

tff(c_423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:55:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.31  
% 2.39/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.39/1.31  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.39/1.31  
% 2.39/1.31  %Foreground sorts:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Background operators:
% 2.39/1.31  
% 2.39/1.31  
% 2.39/1.31  %Foreground operators:
% 2.39/1.31  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.39/1.31  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.39/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.31  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.39/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.39/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.39/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.39/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.39/1.31  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.39/1.31  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.31  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.39/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.39/1.31  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.39/1.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.39/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.39/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.39/1.31  
% 2.68/1.33  tff(f_143, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_connsp_2)).
% 2.68/1.33  tff(f_32, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.68/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.68/1.33  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.68/1.33  tff(f_97, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v3_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_tops_1)).
% 2.68/1.33  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.68/1.33  tff(f_30, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.68/1.33  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.68/1.33  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.68/1.33  tff(f_115, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> v4_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tops_1)).
% 2.68/1.33  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.68/1.33  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.68/1.33  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.68/1.33  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 2.68/1.33  tff(f_36, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.68/1.33  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.68/1.33  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.68/1.33  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.68/1.33  tff(c_44, plain, (k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.68/1.33  tff(c_8, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.68/1.33  tff(c_67, plain, (![A_4]: (r1_tarski('#skF_3', A_4))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8])).
% 2.68/1.33  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.68/1.33  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.68/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.68/1.33  tff(c_69, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2])).
% 2.68/1.33  tff(c_18, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.33  tff(c_63, plain, (![A_10]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 2.68/1.33  tff(c_262, plain, (![B_82, A_83]: (v3_pre_topc(B_82, A_83) | ~v1_xboole_0(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.68/1.33  tff(c_266, plain, (![A_83]: (v3_pre_topc('#skF_3', A_83) | ~v1_xboole_0('#skF_3') | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(resolution, [status(thm)], [c_63, c_262])).
% 2.68/1.33  tff(c_273, plain, (![A_83]: (v3_pre_topc('#skF_3', A_83) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_266])).
% 2.68/1.33  tff(c_141, plain, (![D_63]: (v3_pre_topc(D_63, '#skF_1') | ~r2_hidden(D_63, '#skF_3') | ~m1_subset_1(D_63, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.68/1.33  tff(c_150, plain, (v3_pre_topc('#skF_3', '#skF_1') | ~r2_hidden('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_63, c_141])).
% 2.68/1.33  tff(c_152, plain, (~r2_hidden('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_150])).
% 2.68/1.33  tff(c_278, plain, (![D_87]: (r2_hidden(D_87, '#skF_3') | ~r2_hidden('#skF_2', D_87) | ~v4_pre_topc(D_87, '#skF_1') | ~v3_pre_topc(D_87, '#skF_1') | ~m1_subset_1(D_87, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.68/1.33  tff(c_282, plain, (r2_hidden('#skF_3', '#skF_3') | ~r2_hidden('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_63, c_278])).
% 2.68/1.33  tff(c_289, plain, (~r2_hidden('#skF_2', '#skF_3') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v3_pre_topc('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_152, c_282])).
% 2.68/1.33  tff(c_293, plain, (~v3_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_289])).
% 2.68/1.33  tff(c_296, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_273, c_293])).
% 2.68/1.33  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_296])).
% 2.68/1.33  tff(c_302, plain, (v3_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_289])).
% 2.68/1.33  tff(c_10, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.33  tff(c_66, plain, (![A_5]: (k5_xboole_0(A_5, '#skF_3')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10])).
% 2.68/1.33  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.68/1.33  tff(c_68, plain, (![A_3]: (k3_xboole_0(A_3, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_6])).
% 2.68/1.33  tff(c_114, plain, (![A_58, B_59]: (k5_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.68/1.33  tff(c_123, plain, (![A_3]: (k5_xboole_0(A_3, '#skF_3')=k4_xboole_0(A_3, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_114])).
% 2.68/1.33  tff(c_126, plain, (![A_3]: (k4_xboole_0(A_3, '#skF_3')=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_123])).
% 2.68/1.33  tff(c_188, plain, (![A_73, B_74]: (k4_xboole_0(A_73, B_74)=k3_subset_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.68/1.33  tff(c_191, plain, (![A_10]: (k4_xboole_0(A_10, '#skF_3')=k3_subset_1(A_10, '#skF_3'))), inference(resolution, [status(thm)], [c_63, c_188])).
% 2.68/1.33  tff(c_196, plain, (![A_10]: (k3_subset_1(A_10, '#skF_3')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_126, c_191])).
% 2.68/1.33  tff(c_309, plain, (![A_88, B_89]: (v4_pre_topc(k3_subset_1(u1_struct_0(A_88), B_89), A_88) | ~v3_pre_topc(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.68/1.33  tff(c_313, plain, (![A_88]: (v4_pre_topc(u1_struct_0(A_88), A_88) | ~v3_pre_topc('#skF_3', A_88) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(superposition, [status(thm), theory('equality')], [c_196, c_309])).
% 2.68/1.33  tff(c_315, plain, (![A_88]: (v4_pre_topc(u1_struct_0(A_88), A_88) | ~v3_pre_topc('#skF_3', A_88) | ~l1_pre_topc(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_313])).
% 2.68/1.33  tff(c_30, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.68/1.33  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.68/1.33  tff(c_48, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 2.68/1.33  tff(c_22, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.68/1.33  tff(c_248, plain, (![B_79, A_80]: (v4_pre_topc(B_79, A_80) | ~v1_xboole_0(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0(A_80))) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.68/1.33  tff(c_252, plain, (![A_80]: (v4_pre_topc('#skF_3', A_80) | ~v1_xboole_0('#skF_3') | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(resolution, [status(thm)], [c_63, c_248])).
% 2.68/1.33  tff(c_259, plain, (![A_80]: (v4_pre_topc('#skF_3', A_80) | ~l1_pre_topc(A_80) | ~v2_pre_topc(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_252])).
% 2.68/1.33  tff(c_336, plain, (![A_94, B_95]: (v3_pre_topc(k3_subset_1(u1_struct_0(A_94), B_95), A_94) | ~v4_pre_topc(B_95, A_94) | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.68/1.33  tff(c_343, plain, (![A_94]: (v3_pre_topc(u1_struct_0(A_94), A_94) | ~v4_pre_topc('#skF_3', A_94) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_pre_topc(A_94))), inference(superposition, [status(thm), theory('equality')], [c_196, c_336])).
% 2.68/1.33  tff(c_347, plain, (![A_96]: (v3_pre_topc(u1_struct_0(A_96), A_96) | ~v4_pre_topc('#skF_3', A_96) | ~l1_pre_topc(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_343])).
% 2.68/1.33  tff(c_12, plain, (![A_6]: (k2_subset_1(A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.68/1.33  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.33  tff(c_65, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 2.68/1.33  tff(c_151, plain, (v3_pre_topc(u1_struct_0('#skF_1'), '#skF_1') | ~r2_hidden(u1_struct_0('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_65, c_141])).
% 2.68/1.33  tff(c_164, plain, (~r2_hidden(u1_struct_0('#skF_1'), '#skF_3')), inference(splitLeft, [status(thm)], [c_151])).
% 2.68/1.33  tff(c_286, plain, (r2_hidden(u1_struct_0('#skF_1'), '#skF_3') | ~r2_hidden('#skF_2', u1_struct_0('#skF_1')) | ~v4_pre_topc(u1_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(u1_struct_0('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_65, c_278])).
% 2.68/1.33  tff(c_292, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1')) | ~v4_pre_topc(u1_struct_0('#skF_1'), '#skF_1') | ~v3_pre_topc(u1_struct_0('#skF_1'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_164, c_286])).
% 2.68/1.33  tff(c_317, plain, (~v3_pre_topc(u1_struct_0('#skF_1'), '#skF_1')), inference(splitLeft, [status(thm)], [c_292])).
% 2.68/1.33  tff(c_353, plain, (~v4_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_347, c_317])).
% 2.68/1.33  tff(c_357, plain, (~v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_353])).
% 2.68/1.33  tff(c_360, plain, (~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_259, c_357])).
% 2.68/1.33  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_360])).
% 2.68/1.33  tff(c_365, plain, (~v4_pre_topc(u1_struct_0('#skF_1'), '#skF_1') | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_292])).
% 2.68/1.33  tff(c_374, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_365])).
% 2.68/1.33  tff(c_377, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_374])).
% 2.68/1.33  tff(c_380, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_377])).
% 2.68/1.33  tff(c_32, plain, (![A_24]: (~v1_xboole_0(u1_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.68/1.33  tff(c_383, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_380, c_32])).
% 2.68/1.33  tff(c_386, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_54, c_383])).
% 2.68/1.33  tff(c_389, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_386])).
% 2.68/1.33  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_389])).
% 2.68/1.33  tff(c_394, plain, (~v4_pre_topc(u1_struct_0('#skF_1'), '#skF_1')), inference(splitRight, [status(thm)], [c_365])).
% 2.68/1.33  tff(c_407, plain, (~v3_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_315, c_394])).
% 2.68/1.33  tff(c_414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_302, c_407])).
% 2.68/1.33  tff(c_416, plain, (r2_hidden(u1_struct_0('#skF_1'), '#skF_3')), inference(splitRight, [status(thm)], [c_151])).
% 2.68/1.33  tff(c_26, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.68/1.33  tff(c_419, plain, (~r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_416, c_26])).
% 2.68/1.33  tff(c_423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_419])).
% 2.68/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.33  
% 2.68/1.33  Inference rules
% 2.68/1.33  ----------------------
% 2.68/1.33  #Ref     : 0
% 2.68/1.33  #Sup     : 63
% 2.68/1.33  #Fact    : 0
% 2.68/1.33  #Define  : 0
% 2.68/1.33  #Split   : 6
% 2.68/1.33  #Chain   : 0
% 2.68/1.33  #Close   : 0
% 2.68/1.33  
% 2.68/1.33  Ordering : KBO
% 2.68/1.33  
% 2.68/1.33  Simplification rules
% 2.68/1.33  ----------------------
% 2.68/1.33  #Subsume      : 5
% 2.68/1.33  #Demod        : 36
% 2.68/1.33  #Tautology    : 30
% 2.68/1.33  #SimpNegUnit  : 3
% 2.68/1.33  #BackRed      : 0
% 2.68/1.33  
% 2.68/1.33  #Partial instantiations: 0
% 2.68/1.33  #Strategies tried      : 1
% 2.68/1.33  
% 2.68/1.33  Timing (in seconds)
% 2.68/1.33  ----------------------
% 2.68/1.33  Preprocessing        : 0.33
% 2.68/1.34  Parsing              : 0.18
% 2.68/1.34  CNF conversion       : 0.02
% 2.68/1.34  Main loop            : 0.24
% 2.68/1.34  Inferencing          : 0.09
% 2.68/1.34  Reduction            : 0.08
% 2.68/1.34  Demodulation         : 0.05
% 2.68/1.34  BG Simplification    : 0.02
% 2.68/1.34  Subsumption          : 0.04
% 2.68/1.34  Abstraction          : 0.01
% 2.68/1.34  MUC search           : 0.00
% 2.68/1.34  Cooper               : 0.00
% 2.68/1.34  Total                : 0.61
% 2.68/1.34  Index Insertion      : 0.00
% 2.68/1.34  Index Deletion       : 0.00
% 2.68/1.34  Index Matching       : 0.00
% 2.68/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
