%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:21 EST 2020

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 142 expanded)
%              Number of leaves         :   38 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  123 ( 253 expanded)
%              Number of equality atoms :   51 (  85 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

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

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_4337,plain,(
    ! [A_172,B_173,C_174] :
      ( k7_subset_1(A_172,B_173,C_174) = k4_xboole_0(B_173,C_174)
      | ~ m1_subset_1(B_173,k1_zfmisc_1(A_172)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4340,plain,(
    ! [C_174] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_174) = k4_xboole_0('#skF_2',C_174) ),
    inference(resolution,[status(thm)],[c_32,c_4337])).

tff(c_38,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_123,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_34,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1566,plain,(
    ! [A_113,B_114] :
      ( k4_subset_1(u1_struct_0(A_113),B_114,k2_tops_1(A_113,B_114)) = k2_pre_topc(A_113,B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1570,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_1566])).

tff(c_1574,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1570])).

tff(c_44,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_285,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_44])).

tff(c_321,plain,(
    ! [A_65,B_66,C_67] :
      ( k7_subset_1(A_65,B_66,C_67) = k4_xboole_0(B_66,C_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_339,plain,(
    ! [C_70] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_70) = k4_xboole_0('#skF_2',C_70) ),
    inference(resolution,[status(thm)],[c_32,c_321])).

tff(c_351,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_339])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_368,plain,(
    ! [A_71,B_72] : k3_xboole_0(k4_xboole_0(A_71,B_72),A_71) = k4_xboole_0(A_71,B_72) ),
    inference(resolution,[status(thm)],[c_8,c_118])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(B_50,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_103])).

tff(c_20,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_147,plain,(
    ! [B_51,A_52] : k3_xboole_0(B_51,A_52) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_20])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    ! [A_52,B_51] : k2_xboole_0(A_52,k3_xboole_0(B_51,A_52)) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_4])).

tff(c_415,plain,(
    ! [A_73,B_74] : k2_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_162])).

tff(c_424,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_415])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1(k2_tops_1(A_23,B_24),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1244,plain,(
    ! [A_103,B_104,C_105] :
      ( k4_subset_1(A_103,B_104,C_105) = k2_xboole_0(B_104,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_103))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4099,plain,(
    ! [A_150,B_151,B_152] :
      ( k4_subset_1(u1_struct_0(A_150),B_151,k2_tops_1(A_150,B_152)) = k2_xboole_0(B_151,k2_tops_1(A_150,B_152))
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(resolution,[status(thm)],[c_22,c_1244])).

tff(c_4103,plain,(
    ! [B_152] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_152)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_152))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_4099])).

tff(c_4111,plain,(
    ! [B_153] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_153)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_153))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4103])).

tff(c_4118,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_4111])).

tff(c_4123,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1574,c_424,c_4118])).

tff(c_36,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_456,plain,(
    ! [A_77,B_78] :
      ( v4_pre_topc(k2_pre_topc(A_77,B_78),A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77)
      | ~ v2_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_458,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_456])).

tff(c_461,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_458])).

tff(c_4125,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4123,c_461])).

tff(c_4127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_4125])).

tff(c_4128,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4470,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4340,c_4128])).

tff(c_4130,plain,(
    ! [A_154,B_155] : k1_setfam_1(k2_tarski(A_154,B_155)) = k3_xboole_0(B_155,A_154) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_103])).

tff(c_4136,plain,(
    ! [B_155,A_154] : k3_xboole_0(B_155,A_154) = k3_xboole_0(A_154,B_155) ),
    inference(superposition,[status(thm),theory(equality)],[c_4130,c_20])).

tff(c_4129,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_4737,plain,(
    ! [A_198,B_199] :
      ( r1_tarski(k2_tops_1(A_198,B_199),B_199)
      | ~ v4_pre_topc(B_199,A_198)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(u1_struct_0(A_198)))
      | ~ l1_pre_topc(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4741,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_4737])).

tff(c_4745,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4129,c_4741])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4749,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4745,c_6])).

tff(c_4799,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4136,c_4749])).

tff(c_5187,plain,(
    ! [A_210,B_211] :
      ( k7_subset_1(u1_struct_0(A_210),B_211,k2_tops_1(A_210,B_211)) = k1_tops_1(A_210,B_211)
      | ~ m1_subset_1(B_211,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5191,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_5187])).

tff(c_5195,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_4340,c_5191])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5214,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5195,c_10])).

tff(c_5224,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4799,c_5214])).

tff(c_5226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4470,c_5224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:46:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.20/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.20/2.08  
% 5.20/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.20/2.08  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 5.20/2.08  
% 5.20/2.08  %Foreground sorts:
% 5.20/2.08  
% 5.20/2.08  
% 5.20/2.08  %Background operators:
% 5.20/2.08  
% 5.20/2.08  
% 5.20/2.08  %Foreground operators:
% 5.20/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.20/2.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.20/2.08  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.20/2.08  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.20/2.08  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.20/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.20/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.20/2.08  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.20/2.08  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.20/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.20/2.08  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.20/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.20/2.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.20/2.08  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.20/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.20/2.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.20/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.20/2.08  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.20/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.20/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.20/2.08  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.20/2.08  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.20/2.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.20/2.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.20/2.08  
% 5.20/2.10  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.20/2.10  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.20/2.10  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.20/2.10  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.20/2.10  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.20/2.10  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.20/2.10  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.20/2.10  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.20/2.10  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.20/2.10  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.20/2.10  tff(f_67, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 5.20/2.10  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.20/2.10  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 5.20/2.10  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.20/2.10  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.20/2.10  tff(c_4337, plain, (![A_172, B_173, C_174]: (k7_subset_1(A_172, B_173, C_174)=k4_xboole_0(B_173, C_174) | ~m1_subset_1(B_173, k1_zfmisc_1(A_172)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.20/2.10  tff(c_4340, plain, (![C_174]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_174)=k4_xboole_0('#skF_2', C_174))), inference(resolution, [status(thm)], [c_32, c_4337])).
% 5.20/2.10  tff(c_38, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.20/2.10  tff(c_123, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_38])).
% 5.20/2.10  tff(c_34, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.20/2.10  tff(c_1566, plain, (![A_113, B_114]: (k4_subset_1(u1_struct_0(A_113), B_114, k2_tops_1(A_113, B_114))=k2_pre_topc(A_113, B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.20/2.10  tff(c_1570, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_1566])).
% 5.20/2.10  tff(c_1574, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1570])).
% 5.20/2.10  tff(c_44, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.20/2.10  tff(c_285, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_123, c_44])).
% 5.20/2.10  tff(c_321, plain, (![A_65, B_66, C_67]: (k7_subset_1(A_65, B_66, C_67)=k4_xboole_0(B_66, C_67) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.20/2.10  tff(c_339, plain, (![C_70]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_70)=k4_xboole_0('#skF_2', C_70))), inference(resolution, [status(thm)], [c_32, c_321])).
% 5.20/2.10  tff(c_351, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_285, c_339])).
% 5.20/2.10  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.20/2.10  tff(c_118, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.20/2.10  tff(c_368, plain, (![A_71, B_72]: (k3_xboole_0(k4_xboole_0(A_71, B_72), A_71)=k4_xboole_0(A_71, B_72))), inference(resolution, [status(thm)], [c_8, c_118])).
% 5.20/2.10  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.20/2.10  tff(c_103, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.20/2.10  tff(c_124, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(B_50, A_49))), inference(superposition, [status(thm), theory('equality')], [c_12, c_103])).
% 5.20/2.10  tff(c_20, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.20/2.10  tff(c_147, plain, (![B_51, A_52]: (k3_xboole_0(B_51, A_52)=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_124, c_20])).
% 5.20/2.10  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.20/2.10  tff(c_162, plain, (![A_52, B_51]: (k2_xboole_0(A_52, k3_xboole_0(B_51, A_52))=A_52)), inference(superposition, [status(thm), theory('equality')], [c_147, c_4])).
% 5.20/2.10  tff(c_415, plain, (![A_73, B_74]: (k2_xboole_0(A_73, k4_xboole_0(A_73, B_74))=A_73)), inference(superposition, [status(thm), theory('equality')], [c_368, c_162])).
% 5.20/2.10  tff(c_424, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_351, c_415])).
% 5.20/2.10  tff(c_22, plain, (![A_23, B_24]: (m1_subset_1(k2_tops_1(A_23, B_24), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.20/2.10  tff(c_1244, plain, (![A_103, B_104, C_105]: (k4_subset_1(A_103, B_104, C_105)=k2_xboole_0(B_104, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(A_103)) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.20/2.10  tff(c_4099, plain, (![A_150, B_151, B_152]: (k4_subset_1(u1_struct_0(A_150), B_151, k2_tops_1(A_150, B_152))=k2_xboole_0(B_151, k2_tops_1(A_150, B_152)) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(resolution, [status(thm)], [c_22, c_1244])).
% 5.20/2.10  tff(c_4103, plain, (![B_152]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_152))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_152)) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_4099])).
% 5.20/2.10  tff(c_4111, plain, (![B_153]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_153))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_153)) | ~m1_subset_1(B_153, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4103])).
% 5.20/2.10  tff(c_4118, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_4111])).
% 5.20/2.10  tff(c_4123, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1574, c_424, c_4118])).
% 5.20/2.10  tff(c_36, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.20/2.10  tff(c_456, plain, (![A_77, B_78]: (v4_pre_topc(k2_pre_topc(A_77, B_78), A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77) | ~v2_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.20/2.10  tff(c_458, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_456])).
% 5.20/2.10  tff(c_461, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_458])).
% 5.20/2.10  tff(c_4125, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4123, c_461])).
% 5.20/2.10  tff(c_4127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_4125])).
% 5.20/2.10  tff(c_4128, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_38])).
% 5.20/2.10  tff(c_4470, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4340, c_4128])).
% 5.20/2.10  tff(c_4130, plain, (![A_154, B_155]: (k1_setfam_1(k2_tarski(A_154, B_155))=k3_xboole_0(B_155, A_154))), inference(superposition, [status(thm), theory('equality')], [c_12, c_103])).
% 5.20/2.10  tff(c_4136, plain, (![B_155, A_154]: (k3_xboole_0(B_155, A_154)=k3_xboole_0(A_154, B_155))), inference(superposition, [status(thm), theory('equality')], [c_4130, c_20])).
% 5.20/2.10  tff(c_4129, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_38])).
% 5.20/2.10  tff(c_4737, plain, (![A_198, B_199]: (r1_tarski(k2_tops_1(A_198, B_199), B_199) | ~v4_pre_topc(B_199, A_198) | ~m1_subset_1(B_199, k1_zfmisc_1(u1_struct_0(A_198))) | ~l1_pre_topc(A_198))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.20/2.10  tff(c_4741, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_4737])).
% 5.20/2.10  tff(c_4745, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4129, c_4741])).
% 5.20/2.10  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.20/2.10  tff(c_4749, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4745, c_6])).
% 5.20/2.10  tff(c_4799, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4136, c_4749])).
% 5.20/2.10  tff(c_5187, plain, (![A_210, B_211]: (k7_subset_1(u1_struct_0(A_210), B_211, k2_tops_1(A_210, B_211))=k1_tops_1(A_210, B_211) | ~m1_subset_1(B_211, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.20/2.10  tff(c_5191, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_5187])).
% 5.20/2.10  tff(c_5195, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_4340, c_5191])).
% 5.20/2.10  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.20/2.10  tff(c_5214, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5195, c_10])).
% 5.20/2.10  tff(c_5224, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4799, c_5214])).
% 5.20/2.10  tff(c_5226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4470, c_5224])).
% 5.20/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.20/2.10  
% 5.20/2.10  Inference rules
% 5.20/2.10  ----------------------
% 5.20/2.10  #Ref     : 0
% 5.20/2.10  #Sup     : 1319
% 5.20/2.10  #Fact    : 0
% 5.20/2.10  #Define  : 0
% 5.20/2.10  #Split   : 1
% 5.20/2.10  #Chain   : 0
% 5.20/2.10  #Close   : 0
% 5.20/2.10  
% 5.20/2.10  Ordering : KBO
% 5.20/2.10  
% 5.20/2.10  Simplification rules
% 5.20/2.10  ----------------------
% 5.20/2.10  #Subsume      : 89
% 5.20/2.10  #Demod        : 1763
% 5.20/2.10  #Tautology    : 900
% 5.20/2.10  #SimpNegUnit  : 3
% 5.20/2.10  #BackRed      : 4
% 5.20/2.10  
% 5.20/2.10  #Partial instantiations: 0
% 5.20/2.10  #Strategies tried      : 1
% 5.20/2.10  
% 5.20/2.10  Timing (in seconds)
% 5.20/2.10  ----------------------
% 5.20/2.10  Preprocessing        : 0.32
% 5.20/2.11  Parsing              : 0.17
% 5.20/2.11  CNF conversion       : 0.02
% 5.20/2.11  Main loop            : 1.02
% 5.20/2.11  Inferencing          : 0.29
% 5.20/2.11  Reduction            : 0.51
% 5.20/2.11  Demodulation         : 0.44
% 5.20/2.11  BG Simplification    : 0.03
% 5.20/2.11  Subsumption          : 0.12
% 5.20/2.11  Abstraction          : 0.07
% 5.20/2.11  MUC search           : 0.00
% 5.20/2.11  Cooper               : 0.00
% 5.20/2.11  Total                : 1.38
% 5.20/2.11  Index Insertion      : 0.00
% 5.20/2.11  Index Deletion       : 0.00
% 5.20/2.11  Index Matching       : 0.00
% 5.20/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
