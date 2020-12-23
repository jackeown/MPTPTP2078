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
% DateTime   : Thu Dec  3 10:21:25 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 138 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 272 expanded)
%              Number of equality atoms :   49 (  84 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_55,axiom,(
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

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4326,plain,(
    ! [A_184,B_185,C_186] :
      ( k7_subset_1(A_184,B_185,C_186) = k4_xboole_0(B_185,C_186)
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_184)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4332,plain,(
    ! [C_186] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_186) = k4_xboole_0('#skF_2',C_186) ),
    inference(resolution,[status(thm)],[c_34,c_4326])).

tff(c_40,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_128,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_764,plain,(
    ! [B_92,A_93] :
      ( v4_pre_topc(B_92,A_93)
      | k2_pre_topc(A_93,B_92) != B_92
      | ~ v2_pre_topc(A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_771,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_764])).

tff(c_775,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_771])).

tff(c_776,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_775])).

tff(c_114,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(A_43,B_44)
      | ~ m1_subset_1(A_43,k1_zfmisc_1(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_118,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_114])).

tff(c_1025,plain,(
    ! [A_106,B_107] :
      ( k4_subset_1(u1_struct_0(A_106),B_107,k2_tops_1(A_106,B_107)) = k2_pre_topc(A_106,B_107)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1030,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_1025])).

tff(c_1034,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1030])).

tff(c_291,plain,(
    ! [A_64,B_65,C_66] :
      ( k7_subset_1(A_64,B_65,C_66) = k4_xboole_0(B_65,C_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_424,plain,(
    ! [C_75] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_75) = k4_xboole_0('#skF_2',C_75) ),
    inference(resolution,[status(thm)],[c_34,c_291])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_181,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_46])).

tff(c_430,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_181])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    ! [A_47,B_48] : k2_xboole_0(k4_xboole_0(A_47,B_48),A_47) = A_47 ),
    inference(resolution,[status(thm)],[c_12,c_119])).

tff(c_145,plain,(
    ! [B_2,B_48] : k2_xboole_0(B_2,k4_xboole_0(B_2,B_48)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_129])).

tff(c_710,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_145])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k4_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_704,plain,(
    ! [B_6] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),B_6)
      | ~ r1_tarski('#skF_2',B_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_6])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_477,plain,(
    ! [A_78,B_79,C_80] :
      ( k4_subset_1(A_78,B_79,C_80) = k2_xboole_0(B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4114,plain,(
    ! [B_163,B_164,A_165] :
      ( k4_subset_1(B_163,B_164,A_165) = k2_xboole_0(B_164,A_165)
      | ~ m1_subset_1(B_164,k1_zfmisc_1(B_163))
      | ~ r1_tarski(A_165,B_163) ) ),
    inference(resolution,[status(thm)],[c_22,c_477])).

tff(c_4121,plain,(
    ! [A_166] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_166) = k2_xboole_0('#skF_2',A_166)
      | ~ r1_tarski(A_166,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_4114])).

tff(c_4129,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_704,c_4121])).

tff(c_4164,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_1034,c_710,c_4129])).

tff(c_4166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_776,c_4164])).

tff(c_4167,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4462,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4332,c_4167])).

tff(c_4168,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4557,plain,(
    ! [A_202,B_203] :
      ( r1_tarski(k2_tops_1(A_202,B_203),B_203)
      | ~ v4_pre_topc(B_203,A_202)
      | ~ m1_subset_1(B_203,k1_zfmisc_1(u1_struct_0(A_202)))
      | ~ l1_pre_topc(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4562,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_4557])).

tff(c_4566,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4168,c_4562])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4573,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_4566,c_10])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4832,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4573,c_4])).

tff(c_5258,plain,(
    ! [A_230,B_231] :
      ( k7_subset_1(u1_struct_0(A_230),B_231,k2_tops_1(A_230,B_231)) = k1_tops_1(A_230,B_231)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5263,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_5258])).

tff(c_5267,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4332,c_5263])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5283,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5267,c_14])).

tff(c_5302,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4832,c_5283])).

tff(c_5304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4462,c_5302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/2.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/2.04  
% 4.83/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/2.04  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 4.83/2.04  
% 4.83/2.04  %Foreground sorts:
% 4.83/2.04  
% 4.83/2.04  
% 4.83/2.04  %Background operators:
% 4.83/2.04  
% 4.83/2.04  
% 4.83/2.04  %Foreground operators:
% 4.83/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/2.04  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.83/2.04  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.83/2.04  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.83/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.83/2.04  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.83/2.04  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.83/2.04  tff('#skF_2', type, '#skF_2': $i).
% 4.83/2.04  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.83/2.04  tff('#skF_1', type, '#skF_1': $i).
% 4.83/2.04  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/2.04  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 4.83/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/2.04  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.83/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.83/2.04  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.83/2.04  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.83/2.04  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.83/2.04  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/2.04  
% 4.96/2.06  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 4.96/2.06  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.96/2.06  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.96/2.06  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.96/2.06  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 4.96/2.06  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.96/2.06  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.96/2.06  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.96/2.06  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 4.96/2.06  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.96/2.06  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 4.96/2.06  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.96/2.06  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.96/2.06  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 4.96/2.06  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.96/2.06  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/2.06  tff(c_4326, plain, (![A_184, B_185, C_186]: (k7_subset_1(A_184, B_185, C_186)=k4_xboole_0(B_185, C_186) | ~m1_subset_1(B_185, k1_zfmisc_1(A_184)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.96/2.06  tff(c_4332, plain, (![C_186]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_186)=k4_xboole_0('#skF_2', C_186))), inference(resolution, [status(thm)], [c_34, c_4326])).
% 4.96/2.06  tff(c_40, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/2.06  tff(c_128, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 4.96/2.06  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/2.06  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/2.06  tff(c_764, plain, (![B_92, A_93]: (v4_pre_topc(B_92, A_93) | k2_pre_topc(A_93, B_92)!=B_92 | ~v2_pre_topc(A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.96/2.06  tff(c_771, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_764])).
% 4.96/2.06  tff(c_775, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_771])).
% 4.96/2.06  tff(c_776, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_128, c_775])).
% 4.96/2.06  tff(c_114, plain, (![A_43, B_44]: (r1_tarski(A_43, B_44) | ~m1_subset_1(A_43, k1_zfmisc_1(B_44)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.96/2.06  tff(c_118, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_114])).
% 4.96/2.06  tff(c_1025, plain, (![A_106, B_107]: (k4_subset_1(u1_struct_0(A_106), B_107, k2_tops_1(A_106, B_107))=k2_pre_topc(A_106, B_107) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_106))) | ~l1_pre_topc(A_106))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.96/2.06  tff(c_1030, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_1025])).
% 4.96/2.06  tff(c_1034, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1030])).
% 4.96/2.06  tff(c_291, plain, (![A_64, B_65, C_66]: (k7_subset_1(A_64, B_65, C_66)=k4_xboole_0(B_65, C_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.96/2.06  tff(c_424, plain, (![C_75]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_75)=k4_xboole_0('#skF_2', C_75))), inference(resolution, [status(thm)], [c_34, c_291])).
% 4.96/2.06  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.96/2.06  tff(c_181, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_128, c_46])).
% 4.96/2.06  tff(c_430, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_424, c_181])).
% 4.96/2.06  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.96/2.06  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.96/2.06  tff(c_119, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.96/2.06  tff(c_129, plain, (![A_47, B_48]: (k2_xboole_0(k4_xboole_0(A_47, B_48), A_47)=A_47)), inference(resolution, [status(thm)], [c_12, c_119])).
% 4.96/2.06  tff(c_145, plain, (![B_2, B_48]: (k2_xboole_0(B_2, k4_xboole_0(B_2, B_48))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_129])).
% 4.96/2.06  tff(c_710, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_430, c_145])).
% 4.96/2.06  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_tarski(k4_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.96/2.06  tff(c_704, plain, (![B_6]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), B_6) | ~r1_tarski('#skF_2', B_6))), inference(superposition, [status(thm), theory('equality')], [c_430, c_6])).
% 4.96/2.06  tff(c_22, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.96/2.06  tff(c_477, plain, (![A_78, B_79, C_80]: (k4_subset_1(A_78, B_79, C_80)=k2_xboole_0(B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.96/2.06  tff(c_4114, plain, (![B_163, B_164, A_165]: (k4_subset_1(B_163, B_164, A_165)=k2_xboole_0(B_164, A_165) | ~m1_subset_1(B_164, k1_zfmisc_1(B_163)) | ~r1_tarski(A_165, B_163))), inference(resolution, [status(thm)], [c_22, c_477])).
% 4.96/2.06  tff(c_4121, plain, (![A_166]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_166)=k2_xboole_0('#skF_2', A_166) | ~r1_tarski(A_166, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_4114])).
% 4.96/2.06  tff(c_4129, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_704, c_4121])).
% 4.96/2.06  tff(c_4164, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_1034, c_710, c_4129])).
% 4.96/2.06  tff(c_4166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_776, c_4164])).
% 4.96/2.06  tff(c_4167, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.96/2.06  tff(c_4462, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4332, c_4167])).
% 4.96/2.06  tff(c_4168, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 4.96/2.06  tff(c_4557, plain, (![A_202, B_203]: (r1_tarski(k2_tops_1(A_202, B_203), B_203) | ~v4_pre_topc(B_203, A_202) | ~m1_subset_1(B_203, k1_zfmisc_1(u1_struct_0(A_202))) | ~l1_pre_topc(A_202))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.96/2.06  tff(c_4562, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_4557])).
% 4.96/2.06  tff(c_4566, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4168, c_4562])).
% 4.96/2.06  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.96/2.06  tff(c_4573, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_4566, c_10])).
% 4.96/2.06  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.96/2.06  tff(c_4832, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4573, c_4])).
% 4.96/2.06  tff(c_5258, plain, (![A_230, B_231]: (k7_subset_1(u1_struct_0(A_230), B_231, k2_tops_1(A_230, B_231))=k1_tops_1(A_230, B_231) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.96/2.06  tff(c_5263, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_5258])).
% 4.96/2.06  tff(c_5267, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4332, c_5263])).
% 4.96/2.06  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.96/2.06  tff(c_5283, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5267, c_14])).
% 4.96/2.06  tff(c_5302, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4832, c_5283])).
% 4.96/2.06  tff(c_5304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4462, c_5302])).
% 4.96/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.96/2.06  
% 4.96/2.06  Inference rules
% 4.96/2.06  ----------------------
% 4.96/2.06  #Ref     : 0
% 4.96/2.06  #Sup     : 1364
% 4.96/2.06  #Fact    : 0
% 4.96/2.06  #Define  : 0
% 4.96/2.06  #Split   : 1
% 4.96/2.06  #Chain   : 0
% 4.96/2.06  #Close   : 0
% 4.96/2.06  
% 4.96/2.06  Ordering : KBO
% 4.96/2.06  
% 4.96/2.06  Simplification rules
% 4.96/2.06  ----------------------
% 4.96/2.06  #Subsume      : 135
% 4.96/2.06  #Demod        : 873
% 4.96/2.06  #Tautology    : 719
% 4.96/2.06  #SimpNegUnit  : 5
% 4.96/2.06  #BackRed      : 1
% 4.96/2.06  
% 4.96/2.06  #Partial instantiations: 0
% 4.96/2.06  #Strategies tried      : 1
% 4.96/2.06  
% 4.96/2.06  Timing (in seconds)
% 4.96/2.06  ----------------------
% 4.96/2.06  Preprocessing        : 0.32
% 4.96/2.06  Parsing              : 0.17
% 4.96/2.06  CNF conversion       : 0.02
% 4.96/2.06  Main loop            : 0.87
% 4.96/2.06  Inferencing          : 0.27
% 4.96/2.06  Reduction            : 0.36
% 4.96/2.06  Demodulation         : 0.29
% 4.96/2.06  BG Simplification    : 0.03
% 4.96/2.06  Subsumption          : 0.15
% 4.96/2.06  Abstraction          : 0.04
% 4.96/2.06  MUC search           : 0.00
% 4.96/2.06  Cooper               : 0.00
% 4.96/2.06  Total                : 1.23
% 4.96/2.06  Index Insertion      : 0.00
% 4.96/2.06  Index Deletion       : 0.00
% 4.96/2.06  Index Matching       : 0.00
% 4.96/2.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
