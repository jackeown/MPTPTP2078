%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:04 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 5.04s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 216 expanded)
%              Number of leaves         :   25 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 431 expanded)
%              Number of equality atoms :   21 (  66 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => r1_tarski(k2_pre_topc(A,k9_subset_1(u1_struct_0(A),B,C)),k9_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k2_pre_topc(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r1_tarski(B,C)
               => r1_tarski(k2_pre_topc(A,B),k2_pre_topc(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(A_16,k1_zfmisc_1(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_46,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_57,plain,(
    r1_tarski('#skF_3',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_46])).

tff(c_217,plain,(
    ! [A_58,B_59,C_60] :
      ( k9_subset_1(A_58,B_59,C_60) = k3_xboole_0(B_59,C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_613,plain,(
    ! [B_77,B_78,A_79] :
      ( k9_subset_1(B_77,B_78,A_79) = k3_xboole_0(B_78,A_79)
      | ~ r1_tarski(A_79,B_77) ) ),
    inference(resolution,[status(thm)],[c_20,c_217])).

tff(c_657,plain,(
    ! [B_83,B_84] : k9_subset_1(B_83,B_84,B_83) = k3_xboole_0(B_84,B_83) ),
    inference(resolution,[status(thm)],[c_6,c_613])).

tff(c_204,plain,(
    ! [A_52,B_53,C_54] :
      ( m1_subset_1(k9_subset_1(A_52,B_53,C_54),k1_zfmisc_1(A_52))
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(A_16,B_17)
      | ~ m1_subset_1(A_16,k1_zfmisc_1(B_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_208,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(k9_subset_1(A_52,B_53,C_54),A_52)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52)) ) ),
    inference(resolution,[status(thm)],[c_204,c_18])).

tff(c_663,plain,(
    ! [B_84,B_83] :
      ( r1_tarski(k3_xboole_0(B_84,B_83),B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(B_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_208])).

tff(c_77,plain,(
    ! [A_42,B_43,C_44] :
      ( r1_tarski(A_42,k3_xboole_0(B_43,C_44))
      | ~ r1_tarski(A_42,C_44)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1089,plain,(
    ! [B_110,C_111,A_112] :
      ( k3_xboole_0(B_110,C_111) = A_112
      | ~ r1_tarski(k3_xboole_0(B_110,C_111),A_112)
      | ~ r1_tarski(A_112,C_111)
      | ~ r1_tarski(A_112,B_110) ) ),
    inference(resolution,[status(thm)],[c_77,c_2])).

tff(c_1104,plain,(
    ! [B_84,B_83] :
      ( k3_xboole_0(B_84,B_83) = B_83
      | ~ r1_tarski(B_83,B_83)
      | ~ r1_tarski(B_83,B_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(B_83)) ) ),
    inference(resolution,[status(thm)],[c_663,c_1089])).

tff(c_1711,plain,(
    ! [B_143,B_144] :
      ( k3_xboole_0(B_143,B_144) = B_144
      | ~ r1_tarski(B_144,B_143)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(B_144)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1104])).

tff(c_1772,plain,
    ( k3_xboole_0(u1_struct_0('#skF_1'),'#skF_3') = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_57,c_1711])).

tff(c_1889,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1772])).

tff(c_1892,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_1889])).

tff(c_1896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1892])).

tff(c_1898,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1772])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(A_5,k3_xboole_0(B_6,C_7))
      | ~ r1_tarski(A_5,C_7)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(B_40,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,k3_xboole_0(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_85,plain,(
    ! [B_6,C_7] :
      ( k3_xboole_0(B_6,C_7) = B_6
      | ~ r1_tarski(B_6,C_7)
      | ~ r1_tarski(B_6,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_81])).

tff(c_89,plain,(
    ! [B_47,C_48] :
      ( k3_xboole_0(B_47,C_48) = B_47
      | ~ r1_tarski(B_47,C_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_85])).

tff(c_108,plain,(
    ! [A_3,B_4] : k3_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k3_xboole_0(A_3,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_89])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_283,plain,(
    ! [B_64] : k9_subset_1(u1_struct_0('#skF_1'),B_64,'#skF_2') = k3_xboole_0(B_64,'#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_217])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k9_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_292,plain,(
    ! [B_64] :
      ( m1_subset_1(k3_xboole_0(B_64,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_12])).

tff(c_335,plain,(
    ! [B_67] : m1_subset_1(k3_xboole_0(B_67,'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_292])).

tff(c_344,plain,(
    ! [B_4] : m1_subset_1(k3_xboole_0('#skF_2',B_4),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_335])).

tff(c_24,plain,(
    ! [A_20,B_24,C_26] :
      ( r1_tarski(k2_pre_topc(A_20,B_24),k2_pre_topc(A_20,C_26))
      | ~ r1_tarski(B_24,C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_388,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k2_pre_topc(A_70,B_71),k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [A_11,B_12,C_13] :
      ( k9_subset_1(A_11,B_12,C_13) = k3_xboole_0(B_12,C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1776,plain,(
    ! [A_145,B_146,B_147] :
      ( k9_subset_1(u1_struct_0(A_145),B_146,k2_pre_topc(A_145,B_147)) = k3_xboole_0(B_146,k2_pre_topc(A_145,B_147))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(resolution,[status(thm)],[c_388,c_14])).

tff(c_1816,plain,(
    ! [B_146] :
      ( k9_subset_1(u1_struct_0('#skF_1'),B_146,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_146,k2_pre_topc('#skF_1','#skF_3'))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_1776])).

tff(c_1862,plain,(
    ! [B_146] : k9_subset_1(u1_struct_0('#skF_1'),B_146,k2_pre_topc('#skF_1','#skF_3')) = k3_xboole_0(B_146,k2_pre_topc('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1816])).

tff(c_228,plain,(
    ! [B_59] : k9_subset_1(u1_struct_0('#skF_1'),B_59,'#skF_3') = k3_xboole_0(B_59,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_217])).

tff(c_26,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_230,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k9_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_26])).

tff(c_2160,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1862,c_230])).

tff(c_2179,plain,
    ( ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3'))
    | ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_2160])).

tff(c_4342,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2179])).

tff(c_4345,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_4342])).

tff(c_4349,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_344,c_30,c_8,c_4345])).

tff(c_4350,plain,(
    ~ r1_tarski(k2_pre_topc('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k2_pre_topc('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2179])).

tff(c_4354,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_xboole_0('#skF_2','#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_4350])).

tff(c_4357,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_344,c_28,c_4354])).

tff(c_4360,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_663,c_4357])).

tff(c_4364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1898,c_4360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.90  
% 4.67/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.67/1.90  %$ r1_tarski > m1_subset_1 > l1_pre_topc > k9_subset_1 > k3_xboole_0 > k2_tarski > k2_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.67/1.90  
% 4.67/1.90  %Foreground sorts:
% 4.67/1.90  
% 4.67/1.90  
% 4.67/1.90  %Background operators:
% 4.67/1.90  
% 4.67/1.90  
% 4.67/1.90  %Foreground operators:
% 4.67/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.67/1.90  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.67/1.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.67/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.67/1.90  tff('#skF_2', type, '#skF_2': $i).
% 4.67/1.90  tff('#skF_3', type, '#skF_3': $i).
% 4.67/1.90  tff('#skF_1', type, '#skF_1': $i).
% 4.67/1.90  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.67/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.67/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.67/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.67/1.90  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.67/1.90  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.67/1.90  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.67/1.90  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.67/1.90  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.67/1.90  
% 5.04/1.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.04/1.92  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.04/1.92  tff(f_82, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k2_pre_topc(A, k9_subset_1(u1_struct_0(A), B, C)), k9_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_pre_topc)).
% 5.04/1.92  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 5.04/1.92  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 5.04/1.92  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.04/1.92  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.04/1.92  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r1_tarski(B, C) => r1_tarski(k2_pre_topc(A, B), k2_pre_topc(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_pre_topc)).
% 5.04/1.92  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 5.04/1.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.04/1.92  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(A_16, k1_zfmisc_1(B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.04/1.92  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.04/1.92  tff(c_46, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.04/1.92  tff(c_57, plain, (r1_tarski('#skF_3', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_46])).
% 5.04/1.92  tff(c_217, plain, (![A_58, B_59, C_60]: (k9_subset_1(A_58, B_59, C_60)=k3_xboole_0(B_59, C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.04/1.92  tff(c_613, plain, (![B_77, B_78, A_79]: (k9_subset_1(B_77, B_78, A_79)=k3_xboole_0(B_78, A_79) | ~r1_tarski(A_79, B_77))), inference(resolution, [status(thm)], [c_20, c_217])).
% 5.04/1.92  tff(c_657, plain, (![B_83, B_84]: (k9_subset_1(B_83, B_84, B_83)=k3_xboole_0(B_84, B_83))), inference(resolution, [status(thm)], [c_6, c_613])).
% 5.04/1.92  tff(c_204, plain, (![A_52, B_53, C_54]: (m1_subset_1(k9_subset_1(A_52, B_53, C_54), k1_zfmisc_1(A_52)) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.04/1.92  tff(c_18, plain, (![A_16, B_17]: (r1_tarski(A_16, B_17) | ~m1_subset_1(A_16, k1_zfmisc_1(B_17)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.04/1.92  tff(c_208, plain, (![A_52, B_53, C_54]: (r1_tarski(k9_subset_1(A_52, B_53, C_54), A_52) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)))), inference(resolution, [status(thm)], [c_204, c_18])).
% 5.04/1.92  tff(c_663, plain, (![B_84, B_83]: (r1_tarski(k3_xboole_0(B_84, B_83), B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(B_83)))), inference(superposition, [status(thm), theory('equality')], [c_657, c_208])).
% 5.04/1.92  tff(c_77, plain, (![A_42, B_43, C_44]: (r1_tarski(A_42, k3_xboole_0(B_43, C_44)) | ~r1_tarski(A_42, C_44) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.04/1.92  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.04/1.92  tff(c_1089, plain, (![B_110, C_111, A_112]: (k3_xboole_0(B_110, C_111)=A_112 | ~r1_tarski(k3_xboole_0(B_110, C_111), A_112) | ~r1_tarski(A_112, C_111) | ~r1_tarski(A_112, B_110))), inference(resolution, [status(thm)], [c_77, c_2])).
% 5.04/1.92  tff(c_1104, plain, (![B_84, B_83]: (k3_xboole_0(B_84, B_83)=B_83 | ~r1_tarski(B_83, B_83) | ~r1_tarski(B_83, B_84) | ~m1_subset_1(B_83, k1_zfmisc_1(B_83)))), inference(resolution, [status(thm)], [c_663, c_1089])).
% 5.04/1.92  tff(c_1711, plain, (![B_143, B_144]: (k3_xboole_0(B_143, B_144)=B_144 | ~r1_tarski(B_144, B_143) | ~m1_subset_1(B_144, k1_zfmisc_1(B_144)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1104])).
% 5.04/1.92  tff(c_1772, plain, (k3_xboole_0(u1_struct_0('#skF_1'), '#skF_3')='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_57, c_1711])).
% 5.04/1.92  tff(c_1889, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1772])).
% 5.04/1.92  tff(c_1892, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_1889])).
% 5.04/1.92  tff(c_1896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1892])).
% 5.04/1.92  tff(c_1898, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1772])).
% 5.04/1.92  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.04/1.92  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.04/1.92  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_tarski(A_5, k3_xboole_0(B_6, C_7)) | ~r1_tarski(A_5, C_7) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.04/1.92  tff(c_59, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(B_40, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.04/1.92  tff(c_81, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, k3_xboole_0(A_45, B_46)))), inference(resolution, [status(thm)], [c_8, c_59])).
% 5.04/1.92  tff(c_85, plain, (![B_6, C_7]: (k3_xboole_0(B_6, C_7)=B_6 | ~r1_tarski(B_6, C_7) | ~r1_tarski(B_6, B_6))), inference(resolution, [status(thm)], [c_10, c_81])).
% 5.04/1.92  tff(c_89, plain, (![B_47, C_48]: (k3_xboole_0(B_47, C_48)=B_47 | ~r1_tarski(B_47, C_48))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_85])).
% 5.04/1.92  tff(c_108, plain, (![A_3, B_4]: (k3_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k3_xboole_0(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_89])).
% 5.04/1.92  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.04/1.92  tff(c_283, plain, (![B_64]: (k9_subset_1(u1_struct_0('#skF_1'), B_64, '#skF_2')=k3_xboole_0(B_64, '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_217])).
% 5.04/1.92  tff(c_12, plain, (![A_8, B_9, C_10]: (m1_subset_1(k9_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.04/1.92  tff(c_292, plain, (![B_64]: (m1_subset_1(k3_xboole_0(B_64, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_283, c_12])).
% 5.04/1.92  tff(c_335, plain, (![B_67]: (m1_subset_1(k3_xboole_0(B_67, '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_292])).
% 5.04/1.92  tff(c_344, plain, (![B_4]: (m1_subset_1(k3_xboole_0('#skF_2', B_4), k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_108, c_335])).
% 5.04/1.92  tff(c_24, plain, (![A_20, B_24, C_26]: (r1_tarski(k2_pre_topc(A_20, B_24), k2_pre_topc(A_20, C_26)) | ~r1_tarski(B_24, C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_20))) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.04/1.92  tff(c_388, plain, (![A_70, B_71]: (m1_subset_1(k2_pre_topc(A_70, B_71), k1_zfmisc_1(u1_struct_0(A_70))) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.04/1.92  tff(c_14, plain, (![A_11, B_12, C_13]: (k9_subset_1(A_11, B_12, C_13)=k3_xboole_0(B_12, C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.04/1.92  tff(c_1776, plain, (![A_145, B_146, B_147]: (k9_subset_1(u1_struct_0(A_145), B_146, k2_pre_topc(A_145, B_147))=k3_xboole_0(B_146, k2_pre_topc(A_145, B_147)) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(resolution, [status(thm)], [c_388, c_14])).
% 5.04/1.92  tff(c_1816, plain, (![B_146]: (k9_subset_1(u1_struct_0('#skF_1'), B_146, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_146, k2_pre_topc('#skF_1', '#skF_3')) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_1776])).
% 5.04/1.92  tff(c_1862, plain, (![B_146]: (k9_subset_1(u1_struct_0('#skF_1'), B_146, k2_pre_topc('#skF_1', '#skF_3'))=k3_xboole_0(B_146, k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1816])).
% 5.04/1.92  tff(c_228, plain, (![B_59]: (k9_subset_1(u1_struct_0('#skF_1'), B_59, '#skF_3')=k3_xboole_0(B_59, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_217])).
% 5.04/1.92  tff(c_26, plain, (~r1_tarski(k2_pre_topc('#skF_1', k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.04/1.92  tff(c_230, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k9_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_26])).
% 5.04/1.92  tff(c_2160, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1862, c_230])).
% 5.04/1.92  tff(c_2179, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3')) | ~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_2160])).
% 5.04/1.92  tff(c_4342, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2179])).
% 5.04/1.92  tff(c_4345, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_4342])).
% 5.04/1.92  tff(c_4349, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_344, c_30, c_8, c_4345])).
% 5.04/1.92  tff(c_4350, plain, (~r1_tarski(k2_pre_topc('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k2_pre_topc('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_2179])).
% 5.04/1.92  tff(c_4354, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_xboole_0('#skF_2', '#skF_3'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_4350])).
% 5.04/1.92  tff(c_4357, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_344, c_28, c_4354])).
% 5.04/1.92  tff(c_4360, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_663, c_4357])).
% 5.04/1.92  tff(c_4364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1898, c_4360])).
% 5.04/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.04/1.92  
% 5.04/1.92  Inference rules
% 5.04/1.92  ----------------------
% 5.04/1.92  #Ref     : 0
% 5.04/1.92  #Sup     : 1029
% 5.04/1.92  #Fact    : 0
% 5.04/1.92  #Define  : 0
% 5.04/1.92  #Split   : 9
% 5.04/1.92  #Chain   : 0
% 5.04/1.92  #Close   : 0
% 5.04/1.92  
% 5.04/1.92  Ordering : KBO
% 5.04/1.92  
% 5.04/1.92  Simplification rules
% 5.04/1.92  ----------------------
% 5.04/1.92  #Subsume      : 119
% 5.04/1.92  #Demod        : 686
% 5.04/1.92  #Tautology    : 576
% 5.04/1.92  #SimpNegUnit  : 0
% 5.04/1.92  #BackRed      : 2
% 5.04/1.92  
% 5.04/1.92  #Partial instantiations: 0
% 5.04/1.92  #Strategies tried      : 1
% 5.04/1.92  
% 5.04/1.92  Timing (in seconds)
% 5.04/1.92  ----------------------
% 5.04/1.92  Preprocessing        : 0.30
% 5.04/1.92  Parsing              : 0.16
% 5.04/1.92  CNF conversion       : 0.02
% 5.04/1.92  Main loop            : 0.86
% 5.04/1.92  Inferencing          : 0.27
% 5.04/1.92  Reduction            : 0.35
% 5.04/1.92  Demodulation         : 0.28
% 5.04/1.92  BG Simplification    : 0.03
% 5.04/1.92  Subsumption          : 0.15
% 5.04/1.92  Abstraction          : 0.05
% 5.04/1.92  MUC search           : 0.00
% 5.04/1.92  Cooper               : 0.00
% 5.04/1.92  Total                : 1.19
% 5.04/1.92  Index Insertion      : 0.00
% 5.04/1.92  Index Deletion       : 0.00
% 5.04/1.92  Index Matching       : 0.00
% 5.04/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
