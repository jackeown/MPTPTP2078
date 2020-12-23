%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:58 EST 2020

% Result     : Theorem 19.48s
% Output     : CNFRefutation 19.57s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 125 expanded)
%              Number of leaves         :   35 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  158 ( 384 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v8_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v2_compts_1,type,(
    v2_compts_1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_130,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( ( v8_pre_topc(A)
                    & v2_compts_1(B,A)
                    & v2_compts_1(C,A) )
                 => v2_compts_1(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_compts_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v4_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v4_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tops_1)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_111,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v2_compts_1(B,A)
                  & r1_tarski(C,B)
                  & v4_pre_topc(C,A) )
               => v2_compts_1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_114,plain,(
    ! [A_59,B_60,C_61] :
      ( k9_subset_1(A_59,B_60,C_61) = k3_xboole_0(B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [B_60] : k9_subset_1(u1_struct_0('#skF_1'),B_60,'#skF_3') = k3_xboole_0(B_60,'#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_30,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_133,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_30])).

tff(c_78,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k4_xboole_0(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_53,B_54] : r1_tarski(k3_xboole_0(A_53,B_54),A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_614,plain,(
    ! [B_107,A_108] :
      ( v4_pre_topc(B_107,A_108)
      | ~ v2_compts_1(B_107,A_108)
      | ~ v8_pre_topc(A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_636,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_614])).

tff(c_645,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_34,c_636])).

tff(c_32,plain,(
    v2_compts_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_639,plain,
    ( v4_pre_topc('#skF_3','#skF_1')
    | ~ v2_compts_1('#skF_3','#skF_1')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_614])).

tff(c_648,plain,(
    v4_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_36,c_32,c_639])).

tff(c_716,plain,(
    ! [B_110,C_111,A_112] :
      ( v4_pre_topc(k3_xboole_0(B_110,C_111),A_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v4_pre_topc(C_111,A_112)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ v4_pre_topc(B_110,A_112)
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_735,plain,(
    ! [B_110] :
      ( v4_pre_topc(k3_xboole_0(B_110,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_110,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_716])).

tff(c_801,plain,(
    ! [B_118] :
      ( v4_pre_topc(k3_xboole_0(B_118,'#skF_3'),'#skF_1')
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ v4_pre_topc(B_118,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_648,c_735])).

tff(c_816,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_801])).

tff(c_829,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_816])).

tff(c_244,plain,(
    ! [A_81,B_82] :
      ( u1_struct_0(k1_pre_topc(A_81,B_82)) = B_82
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_251,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_244])).

tff(c_258,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_251])).

tff(c_176,plain,(
    ! [A_69,B_70] :
      ( m1_pre_topc(k1_pre_topc(A_69,B_70),A_69)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_181,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_176])).

tff(c_187,plain,(
    m1_pre_topc(k1_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_181])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_434,plain,(
    ! [C_95,A_96,B_97] :
      ( m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(A_96)))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(u1_struct_0(B_97)))
      | ~ m1_pre_topc(B_97,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_870,plain,(
    ! [A_122,A_123,B_124] :
      ( m1_subset_1(A_122,k1_zfmisc_1(u1_struct_0(A_123)))
      | ~ m1_pre_topc(B_124,A_123)
      | ~ l1_pre_topc(A_123)
      | ~ r1_tarski(A_122,u1_struct_0(B_124)) ) ),
    inference(resolution,[status(thm)],[c_14,c_434])).

tff(c_882,plain,(
    ! [A_122] :
      ( m1_subset_1(A_122,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_122,u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_187,c_870])).

tff(c_892,plain,(
    ! [A_122] :
      ( m1_subset_1(A_122,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_122,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_42,c_882])).

tff(c_782,plain,(
    ! [C_115,A_116,B_117] :
      ( v2_compts_1(C_115,A_116)
      | ~ v4_pre_topc(C_115,A_116)
      | ~ r1_tarski(C_115,B_117)
      | ~ v2_compts_1(B_117,A_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8532,plain,(
    ! [A_434,B_435,A_436] :
      ( v2_compts_1(k3_xboole_0(A_434,B_435),A_436)
      | ~ v4_pre_topc(k3_xboole_0(A_434,B_435),A_436)
      | ~ v2_compts_1(A_434,A_436)
      | ~ m1_subset_1(k3_xboole_0(A_434,B_435),k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ m1_subset_1(A_434,k1_zfmisc_1(u1_struct_0(A_436)))
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436) ) ),
    inference(resolution,[status(thm)],[c_87,c_782])).

tff(c_8603,plain,(
    ! [A_434,B_435] :
      ( v2_compts_1(k3_xboole_0(A_434,B_435),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_434,B_435),'#skF_1')
      | ~ v2_compts_1(A_434,'#skF_1')
      | ~ m1_subset_1(A_434,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_434,B_435),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_892,c_8532])).

tff(c_52685,plain,(
    ! [A_1479,B_1480] :
      ( v2_compts_1(k3_xboole_0(A_1479,B_1480),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_1479,B_1480),'#skF_1')
      | ~ v2_compts_1(A_1479,'#skF_1')
      | ~ m1_subset_1(A_1479,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_1479,B_1480),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_8603])).

tff(c_52787,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_829,c_52685])).

tff(c_52875,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_40,c_34,c_52787])).

tff(c_52877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_52875])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.48/10.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.57/10.91  
% 19.57/10.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.57/10.91  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v8_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 19.57/10.91  
% 19.57/10.91  %Foreground sorts:
% 19.57/10.91  
% 19.57/10.91  
% 19.57/10.91  %Background operators:
% 19.57/10.91  
% 19.57/10.91  
% 19.57/10.91  %Foreground operators:
% 19.57/10.91  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 19.57/10.91  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 19.57/10.91  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 19.57/10.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.57/10.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.57/10.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.57/10.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.57/10.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.57/10.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.57/10.91  tff('#skF_2', type, '#skF_2': $i).
% 19.57/10.91  tff('#skF_3', type, '#skF_3': $i).
% 19.57/10.91  tff('#skF_1', type, '#skF_1': $i).
% 19.57/10.91  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 19.57/10.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.57/10.91  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 19.57/10.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.57/10.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.57/10.91  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 19.57/10.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.57/10.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.57/10.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.57/10.91  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 19.57/10.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.57/10.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.57/10.91  
% 19.57/10.92  tff(f_130, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 19.57/10.92  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 19.57/10.92  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 19.57/10.92  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 19.57/10.92  tff(f_93, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 19.57/10.92  tff(f_80, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v4_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v4_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_tops_1)).
% 19.57/10.92  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 19.57/10.92  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 19.57/10.92  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 19.57/10.92  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 19.57/10.92  tff(f_111, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 19.57/10.92  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.57/10.92  tff(c_114, plain, (![A_59, B_60, C_61]: (k9_subset_1(A_59, B_60, C_61)=k3_xboole_0(B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.57/10.92  tff(c_123, plain, (![B_60]: (k9_subset_1(u1_struct_0('#skF_1'), B_60, '#skF_3')=k3_xboole_0(B_60, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_114])).
% 19.57/10.92  tff(c_30, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.57/10.92  tff(c_133, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_30])).
% 19.57/10.92  tff(c_78, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k4_xboole_0(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.57/10.92  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.57/10.92  tff(c_87, plain, (![A_53, B_54]: (r1_tarski(k3_xboole_0(A_53, B_54), A_53))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2])).
% 19.57/10.92  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.57/10.92  tff(c_34, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.57/10.92  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.57/10.92  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.57/10.92  tff(c_36, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.57/10.92  tff(c_614, plain, (![B_107, A_108]: (v4_pre_topc(B_107, A_108) | ~v2_compts_1(B_107, A_108) | ~v8_pre_topc(A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_93])).
% 19.57/10.92  tff(c_636, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_614])).
% 19.57/10.92  tff(c_645, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_34, c_636])).
% 19.57/10.92  tff(c_32, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_130])).
% 19.57/10.92  tff(c_639, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_614])).
% 19.57/10.92  tff(c_648, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_32, c_639])).
% 19.57/10.92  tff(c_716, plain, (![B_110, C_111, A_112]: (v4_pre_topc(k3_xboole_0(B_110, C_111), A_112) | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~v4_pre_topc(C_111, A_112) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_112))) | ~v4_pre_topc(B_110, A_112) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_80])).
% 19.57/10.92  tff(c_735, plain, (![B_110]: (v4_pre_topc(k3_xboole_0(B_110, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_110, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_716])).
% 19.57/10.92  tff(c_801, plain, (![B_118]: (v4_pre_topc(k3_xboole_0(B_118, '#skF_3'), '#skF_1') | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~v4_pre_topc(B_118, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_648, c_735])).
% 19.57/10.92  tff(c_816, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_801])).
% 19.57/10.92  tff(c_829, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_816])).
% 19.57/10.92  tff(c_244, plain, (![A_81, B_82]: (u1_struct_0(k1_pre_topc(A_81, B_82))=B_82 | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 19.57/10.92  tff(c_251, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_244])).
% 19.57/10.92  tff(c_258, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_251])).
% 19.57/10.92  tff(c_176, plain, (![A_69, B_70]: (m1_pre_topc(k1_pre_topc(A_69, B_70), A_69) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_49])).
% 19.57/10.92  tff(c_181, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_176])).
% 19.57/10.92  tff(c_187, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_181])).
% 19.57/10.92  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.57/10.92  tff(c_434, plain, (![C_95, A_96, B_97]: (m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(A_96))) | ~m1_subset_1(C_95, k1_zfmisc_1(u1_struct_0(B_97))) | ~m1_pre_topc(B_97, A_96) | ~l1_pre_topc(A_96))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.57/10.92  tff(c_870, plain, (![A_122, A_123, B_124]: (m1_subset_1(A_122, k1_zfmisc_1(u1_struct_0(A_123))) | ~m1_pre_topc(B_124, A_123) | ~l1_pre_topc(A_123) | ~r1_tarski(A_122, u1_struct_0(B_124)))), inference(resolution, [status(thm)], [c_14, c_434])).
% 19.57/10.92  tff(c_882, plain, (![A_122]: (m1_subset_1(A_122, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_122, u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_187, c_870])).
% 19.57/10.92  tff(c_892, plain, (![A_122]: (m1_subset_1(A_122, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_122, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_42, c_882])).
% 19.57/10.92  tff(c_782, plain, (![C_115, A_116, B_117]: (v2_compts_1(C_115, A_116) | ~v4_pre_topc(C_115, A_116) | ~r1_tarski(C_115, B_117) | ~v2_compts_1(B_117, A_116) | ~m1_subset_1(C_115, k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_111])).
% 19.57/10.92  tff(c_8532, plain, (![A_434, B_435, A_436]: (v2_compts_1(k3_xboole_0(A_434, B_435), A_436) | ~v4_pre_topc(k3_xboole_0(A_434, B_435), A_436) | ~v2_compts_1(A_434, A_436) | ~m1_subset_1(k3_xboole_0(A_434, B_435), k1_zfmisc_1(u1_struct_0(A_436))) | ~m1_subset_1(A_434, k1_zfmisc_1(u1_struct_0(A_436))) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436))), inference(resolution, [status(thm)], [c_87, c_782])).
% 19.57/10.92  tff(c_8603, plain, (![A_434, B_435]: (v2_compts_1(k3_xboole_0(A_434, B_435), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_434, B_435), '#skF_1') | ~v2_compts_1(A_434, '#skF_1') | ~m1_subset_1(A_434, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_434, B_435), '#skF_2'))), inference(resolution, [status(thm)], [c_892, c_8532])).
% 19.57/10.92  tff(c_52685, plain, (![A_1479, B_1480]: (v2_compts_1(k3_xboole_0(A_1479, B_1480), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_1479, B_1480), '#skF_1') | ~v2_compts_1(A_1479, '#skF_1') | ~m1_subset_1(A_1479, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_1479, B_1480), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_8603])).
% 19.57/10.92  tff(c_52787, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_829, c_52685])).
% 19.57/10.92  tff(c_52875, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_40, c_34, c_52787])).
% 19.57/10.92  tff(c_52877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_52875])).
% 19.57/10.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.57/10.92  
% 19.57/10.92  Inference rules
% 19.57/10.92  ----------------------
% 19.57/10.92  #Ref     : 0
% 19.57/10.92  #Sup     : 14216
% 19.57/10.92  #Fact    : 0
% 19.57/10.92  #Define  : 0
% 19.57/10.92  #Split   : 16
% 19.57/10.92  #Chain   : 0
% 19.57/10.92  #Close   : 0
% 19.57/10.92  
% 19.57/10.92  Ordering : KBO
% 19.57/10.92  
% 19.57/10.92  Simplification rules
% 19.57/10.92  ----------------------
% 19.57/10.92  #Subsume      : 4123
% 19.57/10.92  #Demod        : 4667
% 19.57/10.92  #Tautology    : 615
% 19.57/10.92  #SimpNegUnit  : 8
% 19.57/10.92  #BackRed      : 1
% 19.57/10.92  
% 19.57/10.92  #Partial instantiations: 0
% 19.57/10.92  #Strategies tried      : 1
% 19.57/10.92  
% 19.57/10.92  Timing (in seconds)
% 19.57/10.92  ----------------------
% 19.57/10.92  Preprocessing        : 0.32
% 19.57/10.92  Parsing              : 0.17
% 19.57/10.92  CNF conversion       : 0.02
% 19.57/10.92  Main loop            : 9.78
% 19.57/10.92  Inferencing          : 2.09
% 19.57/10.92  Reduction            : 2.87
% 19.57/10.92  Demodulation         : 2.04
% 19.57/10.93  BG Simplification    : 0.21
% 19.57/10.93  Subsumption          : 4.00
% 19.57/10.93  Abstraction          : 0.26
% 19.57/10.93  MUC search           : 0.00
% 19.57/10.93  Cooper               : 0.00
% 19.57/10.93  Total                : 10.13
% 19.57/10.93  Index Insertion      : 0.00
% 19.57/10.93  Index Deletion       : 0.00
% 19.57/10.93  Index Matching       : 0.00
% 19.57/10.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
