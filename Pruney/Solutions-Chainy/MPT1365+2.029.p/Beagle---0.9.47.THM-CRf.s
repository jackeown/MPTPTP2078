%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:58 EST 2020

% Result     : Theorem 19.43s
% Output     : CNFRefutation 19.59s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 135 expanded)
%              Number of leaves         :   35 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  174 ( 416 expanded)
%              Number of equality atoms :   10 (  18 expanded)
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

tff(f_132,negated_conjecture,(
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

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v8_pre_topc(A)
              & v2_compts_1(B,A) )
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_compts_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( v4_pre_topc(B,A)
                  & v4_pre_topc(C,A) )
               => v4_pre_topc(k9_subset_1(u1_struct_0(A),B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_1)).

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

tff(f_113,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_114,plain,(
    ! [A_63,B_64,C_65] :
      ( k9_subset_1(A_63,B_64,C_65) = k3_xboole_0(B_64,C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_123,plain,(
    ! [B_64] : k9_subset_1(u1_struct_0('#skF_1'),B_64,'#skF_3') = k3_xboole_0(B_64,'#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_114])).

tff(c_30,plain,(
    ~ v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_133,plain,(
    ~ v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_30])).

tff(c_78,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_57,B_58] : r1_tarski(k3_xboole_0(A_57,B_58),A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_34,plain,(
    v2_compts_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_614,plain,(
    ! [B_111,A_112] :
      ( v4_pre_topc(B_111,A_112)
      | ~ v2_compts_1(B_111,A_112)
      | ~ v8_pre_topc(A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0(A_112)))
      | ~ l1_pre_topc(A_112)
      | ~ v2_pre_topc(A_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

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
    inference(cnfTransformation,[status(thm)],[f_132])).

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

tff(c_824,plain,(
    ! [A_119,B_120,C_121] :
      ( v4_pre_topc(k9_subset_1(u1_struct_0(A_119),B_120,C_121),A_119)
      | ~ v4_pre_topc(C_121,A_119)
      | ~ v4_pre_topc(B_120,A_119)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_subset_1(B_120,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_850,plain,(
    ! [B_64] :
      ( v4_pre_topc(k3_xboole_0(B_64,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc('#skF_3','#skF_1')
      | ~ v4_pre_topc(B_64,'#skF_1')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_824])).

tff(c_1030,plain,(
    ! [B_129] :
      ( v4_pre_topc(k3_xboole_0(B_129,'#skF_3'),'#skF_1')
      | ~ v4_pre_topc(B_129,'#skF_1')
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_648,c_850])).

tff(c_1045,plain,
    ( v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1030])).

tff(c_1058,plain,(
    v4_pre_topc(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_1045])).

tff(c_244,plain,(
    ! [A_85,B_86] :
      ( u1_struct_0(k1_pre_topc(A_85,B_86)) = B_86
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_251,plain,
    ( u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2'
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_244])).

tff(c_258,plain,(
    u1_struct_0(k1_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_251])).

tff(c_176,plain,(
    ! [A_73,B_74] :
      ( m1_pre_topc(k1_pre_topc(A_73,B_74),A_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
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
    ! [C_99,A_100,B_101] :
      ( m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(u1_struct_0(B_101)))
      | ~ m1_pre_topc(B_101,A_100)
      | ~ l1_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1064,plain,(
    ! [A_130,A_131,B_132] :
      ( m1_subset_1(A_130,k1_zfmisc_1(u1_struct_0(A_131)))
      | ~ m1_pre_topc(B_132,A_131)
      | ~ l1_pre_topc(A_131)
      | ~ r1_tarski(A_130,u1_struct_0(B_132)) ) ),
    inference(resolution,[status(thm)],[c_14,c_434])).

tff(c_1076,plain,(
    ! [A_130] :
      ( m1_subset_1(A_130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ r1_tarski(A_130,u1_struct_0(k1_pre_topc('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_187,c_1064])).

tff(c_1086,plain,(
    ! [A_130] :
      ( m1_subset_1(A_130,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(A_130,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_258,c_42,c_1076])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_716,plain,(
    ! [C_114,A_115,B_116] :
      ( v2_compts_1(C_114,A_115)
      | ~ v4_pre_topc(C_114,A_115)
      | ~ r1_tarski(C_114,B_116)
      | ~ v2_compts_1(B_116,A_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115)
      | ~ v2_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1618,plain,(
    ! [A_150,B_151,A_152] :
      ( v2_compts_1(k4_xboole_0(A_150,B_151),A_152)
      | ~ v4_pre_topc(k4_xboole_0(A_150,B_151),A_152)
      | ~ v2_compts_1(A_150,A_152)
      | ~ m1_subset_1(k4_xboole_0(A_150,B_151),k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ m1_subset_1(A_150,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_2,c_716])).

tff(c_1659,plain,(
    ! [A_3,B_4,A_152] :
      ( v2_compts_1(k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)),A_152)
      | ~ v4_pre_topc(k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)),A_152)
      | ~ v2_compts_1(A_3,A_152)
      | ~ m1_subset_1(k3_xboole_0(A_3,B_4),k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ m1_subset_1(A_3,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1618])).

tff(c_6899,plain,(
    ! [A_363,B_364,A_365] :
      ( v2_compts_1(k3_xboole_0(A_363,B_364),A_365)
      | ~ v4_pre_topc(k3_xboole_0(A_363,B_364),A_365)
      | ~ v2_compts_1(A_363,A_365)
      | ~ m1_subset_1(k3_xboole_0(A_363,B_364),k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ m1_subset_1(A_363,k1_zfmisc_1(u1_struct_0(A_365)))
      | ~ l1_pre_topc(A_365)
      | ~ v2_pre_topc(A_365) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_1659])).

tff(c_6958,plain,(
    ! [A_363,B_364] :
      ( v2_compts_1(k3_xboole_0(A_363,B_364),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_363,B_364),'#skF_1')
      | ~ v2_compts_1(A_363,'#skF_1')
      | ~ m1_subset_1(A_363,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ r1_tarski(k3_xboole_0(A_363,B_364),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1086,c_6899])).

tff(c_48541,plain,(
    ! [A_1402,B_1403] :
      ( v2_compts_1(k3_xboole_0(A_1402,B_1403),'#skF_1')
      | ~ v4_pre_topc(k3_xboole_0(A_1402,B_1403),'#skF_1')
      | ~ v2_compts_1(A_1402,'#skF_1')
      | ~ m1_subset_1(A_1402,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ r1_tarski(k3_xboole_0(A_1402,B_1403),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6958])).

tff(c_48598,plain,
    ( v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1')
    | ~ v2_compts_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1058,c_48541])).

tff(c_48635,plain,(
    v2_compts_1(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_40,c_34,c_48598])).

tff(c_48637,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_133,c_48635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:17:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.43/10.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.43/10.60  
% 19.43/10.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.43/10.60  %$ v4_pre_topc > v2_compts_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v8_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > k9_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k1_pre_topc > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 19.43/10.60  
% 19.43/10.60  %Foreground sorts:
% 19.43/10.60  
% 19.43/10.60  
% 19.43/10.60  %Background operators:
% 19.43/10.60  
% 19.43/10.60  
% 19.43/10.60  %Foreground operators:
% 19.43/10.60  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 19.43/10.60  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 19.43/10.60  tff(v2_compts_1, type, v2_compts_1: ($i * $i) > $o).
% 19.43/10.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.43/10.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.43/10.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.43/10.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.43/10.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.43/10.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.43/10.60  tff('#skF_2', type, '#skF_2': $i).
% 19.43/10.60  tff('#skF_3', type, '#skF_3': $i).
% 19.43/10.60  tff('#skF_1', type, '#skF_1': $i).
% 19.43/10.60  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 19.43/10.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.43/10.60  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 19.43/10.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.43/10.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.43/10.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 19.43/10.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 19.43/10.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.43/10.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.43/10.60  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 19.43/10.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.43/10.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.43/10.60  
% 19.59/10.61  tff(f_132, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v8_pre_topc(A) & v2_compts_1(B, A)) & v2_compts_1(C, A)) => v2_compts_1(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_compts_1)).
% 19.59/10.61  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 19.59/10.61  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 19.59/10.61  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 19.59/10.61  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v8_pre_topc(A) & v2_compts_1(B, A)) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_compts_1)).
% 19.59/10.61  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) & v4_pre_topc(C, A)) => v4_pre_topc(k9_subset_1(u1_struct_0(A), B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_tops_1)).
% 19.59/10.61  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 19.59/10.61  tff(f_49, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 19.59/10.61  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 19.59/10.61  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 19.59/10.61  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (((v2_compts_1(B, A) & r1_tarski(C, B)) & v4_pre_topc(C, A)) => v2_compts_1(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 19.59/10.61  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 19.59/10.61  tff(c_114, plain, (![A_63, B_64, C_65]: (k9_subset_1(A_63, B_64, C_65)=k3_xboole_0(B_64, C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.59/10.61  tff(c_123, plain, (![B_64]: (k9_subset_1(u1_struct_0('#skF_1'), B_64, '#skF_3')=k3_xboole_0(B_64, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_114])).
% 19.59/10.61  tff(c_30, plain, (~v2_compts_1(k9_subset_1(u1_struct_0('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 19.59/10.61  tff(c_133, plain, (~v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_30])).
% 19.59/10.61  tff(c_78, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k4_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.59/10.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.59/10.61  tff(c_87, plain, (![A_57, B_58]: (r1_tarski(k3_xboole_0(A_57, B_58), A_57))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2])).
% 19.59/10.61  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 19.59/10.61  tff(c_34, plain, (v2_compts_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 19.59/10.61  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 19.59/10.61  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 19.59/10.61  tff(c_36, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 19.59/10.61  tff(c_614, plain, (![B_111, A_112]: (v4_pre_topc(B_111, A_112) | ~v2_compts_1(B_111, A_112) | ~v8_pre_topc(A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0(A_112))) | ~l1_pre_topc(A_112) | ~v2_pre_topc(A_112))), inference(cnfTransformation, [status(thm)], [f_95])).
% 19.59/10.61  tff(c_636, plain, (v4_pre_topc('#skF_2', '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_614])).
% 19.59/10.61  tff(c_645, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_34, c_636])).
% 19.59/10.61  tff(c_32, plain, (v2_compts_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_132])).
% 19.59/10.61  tff(c_639, plain, (v4_pre_topc('#skF_3', '#skF_1') | ~v2_compts_1('#skF_3', '#skF_1') | ~v8_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_614])).
% 19.59/10.61  tff(c_648, plain, (v4_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_36, c_32, c_639])).
% 19.59/10.61  tff(c_824, plain, (![A_119, B_120, C_121]: (v4_pre_topc(k9_subset_1(u1_struct_0(A_119), B_120, C_121), A_119) | ~v4_pre_topc(C_121, A_119) | ~v4_pre_topc(B_120, A_119) | ~m1_subset_1(C_121, k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_subset_1(B_120, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_82])).
% 19.59/10.61  tff(c_850, plain, (![B_64]: (v4_pre_topc(k3_xboole_0(B_64, '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_3', '#skF_1') | ~v4_pre_topc(B_64, '#skF_1') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_824])).
% 19.59/10.61  tff(c_1030, plain, (![B_129]: (v4_pre_topc(k3_xboole_0(B_129, '#skF_3'), '#skF_1') | ~v4_pre_topc(B_129, '#skF_1') | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_648, c_850])).
% 19.59/10.61  tff(c_1045, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_1030])).
% 19.59/10.61  tff(c_1058, plain, (v4_pre_topc(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_1045])).
% 19.59/10.61  tff(c_244, plain, (![A_85, B_86]: (u1_struct_0(k1_pre_topc(A_85, B_86))=B_86 | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_56])).
% 19.59/10.61  tff(c_251, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2' | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_244])).
% 19.59/10.61  tff(c_258, plain, (u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_251])).
% 19.59/10.61  tff(c_176, plain, (![A_73, B_74]: (m1_pre_topc(k1_pre_topc(A_73, B_74), A_73) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 19.59/10.61  tff(c_181, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_176])).
% 19.59/10.61  tff(c_187, plain, (m1_pre_topc(k1_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_181])).
% 19.59/10.61  tff(c_14, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.59/10.61  tff(c_434, plain, (![C_99, A_100, B_101]: (m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(A_100))) | ~m1_subset_1(C_99, k1_zfmisc_1(u1_struct_0(B_101))) | ~m1_pre_topc(B_101, A_100) | ~l1_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_66])).
% 19.59/10.61  tff(c_1064, plain, (![A_130, A_131, B_132]: (m1_subset_1(A_130, k1_zfmisc_1(u1_struct_0(A_131))) | ~m1_pre_topc(B_132, A_131) | ~l1_pre_topc(A_131) | ~r1_tarski(A_130, u1_struct_0(B_132)))), inference(resolution, [status(thm)], [c_14, c_434])).
% 19.59/10.61  tff(c_1076, plain, (![A_130]: (m1_subset_1(A_130, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~r1_tarski(A_130, u1_struct_0(k1_pre_topc('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_187, c_1064])).
% 19.59/10.61  tff(c_1086, plain, (![A_130]: (m1_subset_1(A_130, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(A_130, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_258, c_42, c_1076])).
% 19.59/10.61  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.59/10.61  tff(c_716, plain, (![C_114, A_115, B_116]: (v2_compts_1(C_114, A_115) | ~v4_pre_topc(C_114, A_115) | ~r1_tarski(C_114, B_116) | ~v2_compts_1(B_116, A_115) | ~m1_subset_1(C_114, k1_zfmisc_1(u1_struct_0(A_115))) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115) | ~v2_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_113])).
% 19.59/10.61  tff(c_1618, plain, (![A_150, B_151, A_152]: (v2_compts_1(k4_xboole_0(A_150, B_151), A_152) | ~v4_pre_topc(k4_xboole_0(A_150, B_151), A_152) | ~v2_compts_1(A_150, A_152) | ~m1_subset_1(k4_xboole_0(A_150, B_151), k1_zfmisc_1(u1_struct_0(A_152))) | ~m1_subset_1(A_150, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152))), inference(resolution, [status(thm)], [c_2, c_716])).
% 19.59/10.61  tff(c_1659, plain, (![A_3, B_4, A_152]: (v2_compts_1(k4_xboole_0(A_3, k4_xboole_0(A_3, B_4)), A_152) | ~v4_pre_topc(k4_xboole_0(A_3, k4_xboole_0(A_3, B_4)), A_152) | ~v2_compts_1(A_3, A_152) | ~m1_subset_1(k3_xboole_0(A_3, B_4), k1_zfmisc_1(u1_struct_0(A_152))) | ~m1_subset_1(A_3, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1618])).
% 19.59/10.61  tff(c_6899, plain, (![A_363, B_364, A_365]: (v2_compts_1(k3_xboole_0(A_363, B_364), A_365) | ~v4_pre_topc(k3_xboole_0(A_363, B_364), A_365) | ~v2_compts_1(A_363, A_365) | ~m1_subset_1(k3_xboole_0(A_363, B_364), k1_zfmisc_1(u1_struct_0(A_365))) | ~m1_subset_1(A_363, k1_zfmisc_1(u1_struct_0(A_365))) | ~l1_pre_topc(A_365) | ~v2_pre_topc(A_365))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_1659])).
% 19.59/10.61  tff(c_6958, plain, (![A_363, B_364]: (v2_compts_1(k3_xboole_0(A_363, B_364), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_363, B_364), '#skF_1') | ~v2_compts_1(A_363, '#skF_1') | ~m1_subset_1(A_363, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~r1_tarski(k3_xboole_0(A_363, B_364), '#skF_2'))), inference(resolution, [status(thm)], [c_1086, c_6899])).
% 19.59/10.61  tff(c_48541, plain, (![A_1402, B_1403]: (v2_compts_1(k3_xboole_0(A_1402, B_1403), '#skF_1') | ~v4_pre_topc(k3_xboole_0(A_1402, B_1403), '#skF_1') | ~v2_compts_1(A_1402, '#skF_1') | ~m1_subset_1(A_1402, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0(A_1402, B_1403), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6958])).
% 19.59/10.61  tff(c_48598, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1') | ~v2_compts_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_1058, c_48541])).
% 19.59/10.61  tff(c_48635, plain, (v2_compts_1(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_40, c_34, c_48598])).
% 19.59/10.61  tff(c_48637, plain, $false, inference(negUnitSimplification, [status(thm)], [c_133, c_48635])).
% 19.59/10.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.59/10.61  
% 19.59/10.61  Inference rules
% 19.59/10.61  ----------------------
% 19.59/10.61  #Ref     : 0
% 19.59/10.61  #Sup     : 13199
% 19.59/10.61  #Fact    : 0
% 19.59/10.61  #Define  : 0
% 19.59/10.61  #Split   : 16
% 19.59/10.61  #Chain   : 0
% 19.59/10.61  #Close   : 0
% 19.59/10.61  
% 19.59/10.61  Ordering : KBO
% 19.59/10.62  
% 19.59/10.62  Simplification rules
% 19.59/10.62  ----------------------
% 19.59/10.62  #Subsume      : 4040
% 19.59/10.62  #Demod        : 3601
% 19.59/10.62  #Tautology    : 621
% 19.59/10.62  #SimpNegUnit  : 6
% 19.59/10.62  #BackRed      : 1
% 19.59/10.62  
% 19.59/10.62  #Partial instantiations: 0
% 19.59/10.62  #Strategies tried      : 1
% 19.59/10.62  
% 19.59/10.62  Timing (in seconds)
% 19.59/10.62  ----------------------
% 19.59/10.62  Preprocessing        : 0.35
% 19.59/10.62  Parsing              : 0.19
% 19.59/10.62  CNF conversion       : 0.03
% 19.59/10.62  Main loop            : 9.45
% 19.59/10.62  Inferencing          : 2.10
% 19.59/10.62  Reduction            : 2.74
% 19.59/10.62  Demodulation         : 1.94
% 19.59/10.62  BG Simplification    : 0.21
% 19.59/10.62  Subsumption          : 3.82
% 19.59/10.62  Abstraction          : 0.30
% 19.59/10.62  MUC search           : 0.00
% 19.59/10.62  Cooper               : 0.00
% 19.59/10.62  Total                : 9.84
% 19.59/10.62  Index Insertion      : 0.00
% 19.59/10.62  Index Deletion       : 0.00
% 19.59/10.62  Index Matching       : 0.00
% 19.59/10.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
