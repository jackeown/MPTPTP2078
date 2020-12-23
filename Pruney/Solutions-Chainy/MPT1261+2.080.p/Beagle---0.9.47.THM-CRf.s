%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:23 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 4.14s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 126 expanded)
%              Number of leaves         :   36 (  59 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 245 expanded)
%              Number of equality atoms :   51 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
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

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_66,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_981,plain,(
    ! [A_128,B_129,C_130] :
      ( k7_subset_1(A_128,B_129,C_130) = k4_xboole_0(B_129,C_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_984,plain,(
    ! [C_130] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_130) = k4_xboole_0('#skF_2',C_130) ),
    inference(resolution,[status(thm)],[c_30,c_981])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_121,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_590,plain,(
    ! [B_83,A_84] :
      ( v4_pre_topc(B_83,A_84)
      | k2_pre_topc(A_84,B_83) != B_83
      | ~ v2_pre_topc(A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_596,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_590])).

tff(c_600,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_596])).

tff(c_601,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_600])).

tff(c_602,plain,(
    ! [A_85,B_86] :
      ( k4_subset_1(u1_struct_0(A_85),B_86,k2_tops_1(A_85,B_86)) = k2_pre_topc(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_606,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_602])).

tff(c_610,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_606])).

tff(c_331,plain,(
    ! [A_61,B_62,C_63] :
      ( k7_subset_1(A_61,B_62,C_63) = k4_xboole_0(B_62,C_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_335,plain,(
    ! [C_64] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_64) = k4_xboole_0('#skF_2',C_64) ),
    inference(resolution,[status(thm)],[c_30,c_331])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_282,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_42])).

tff(c_341,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_282])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_116,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_290,plain,(
    ! [A_57,B_58] : k3_xboole_0(k4_xboole_0(A_57,B_58),A_57) = k4_xboole_0(A_57,B_58) ),
    inference(resolution,[status(thm)],[c_8,c_116])).

tff(c_10,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_178,plain,(
    ! [B_49,A_50] : k1_setfam_1(k2_tarski(B_49,A_50)) = k3_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_18,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_210,plain,(
    ! [B_53,A_54] : k3_xboole_0(B_53,A_54) = k3_xboole_0(A_54,B_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_18])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_234,plain,(
    ! [B_53,A_54] : k2_xboole_0(B_53,k3_xboole_0(A_54,B_53)) = B_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_4])).

tff(c_296,plain,(
    ! [A_57,B_58] : k2_xboole_0(A_57,k4_xboole_0(A_57,B_58)) = A_57 ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_234])).

tff(c_353,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_296])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(k2_tops_1(A_24,B_25),k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_565,plain,(
    ! [A_79,B_80,C_81] :
      ( k4_subset_1(A_79,B_80,C_81) = k2_xboole_0(B_80,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_697,plain,(
    ! [A_104,B_105,B_106] :
      ( k4_subset_1(u1_struct_0(A_104),B_105,k2_tops_1(A_104,B_106)) = k2_xboole_0(B_105,k2_tops_1(A_104,B_106))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(resolution,[status(thm)],[c_24,c_565])).

tff(c_701,plain,(
    ! [B_106] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_106)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_106))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_697])).

tff(c_706,plain,(
    ! [B_107] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_107)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_107))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_701])).

tff(c_713,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_706])).

tff(c_718,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_353,c_713])).

tff(c_720,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_601,c_718])).

tff(c_721,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_985,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_984,c_721])).

tff(c_722,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1021,plain,(
    ! [A_138,B_139] :
      ( k2_pre_topc(A_138,B_139) = B_139
      | ~ v4_pre_topc(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1027,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1021])).

tff(c_1031,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_722,c_1027])).

tff(c_1108,plain,(
    ! [A_151,B_152] :
      ( k7_subset_1(u1_struct_0(A_151),k2_pre_topc(A_151,B_152),k1_tops_1(A_151,B_152)) = k2_tops_1(A_151,B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1117,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1031,c_1108])).

tff(c_1121,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_984,c_1117])).

tff(c_1123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_985,c_1121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/2.06  
% 3.79/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/2.06  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.79/2.06  
% 3.79/2.06  %Foreground sorts:
% 3.79/2.06  
% 3.79/2.06  
% 3.79/2.06  %Background operators:
% 3.79/2.06  
% 3.79/2.06  
% 3.79/2.06  %Foreground operators:
% 3.79/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/2.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.79/2.06  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.79/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.79/2.06  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.79/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/2.06  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.79/2.06  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.79/2.06  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.79/2.06  tff('#skF_2', type, '#skF_2': $i).
% 3.79/2.06  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.79/2.06  tff('#skF_1', type, '#skF_1': $i).
% 3.79/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.79/2.06  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.79/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/2.06  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.79/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.79/2.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.79/2.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.79/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.79/2.06  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.79/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/2.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.79/2.06  
% 4.14/2.08  tff(f_98, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 4.14/2.08  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.14/2.08  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 4.14/2.08  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 4.14/2.08  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.14/2.08  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.14/2.08  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.14/2.08  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.14/2.08  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.14/2.08  tff(f_72, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 4.14/2.08  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.14/2.08  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.14/2.08  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.14/2.08  tff(c_981, plain, (![A_128, B_129, C_130]: (k7_subset_1(A_128, B_129, C_130)=k4_xboole_0(B_129, C_130) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/2.08  tff(c_984, plain, (![C_130]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_130)=k4_xboole_0('#skF_2', C_130))), inference(resolution, [status(thm)], [c_30, c_981])).
% 4.14/2.08  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.14/2.08  tff(c_121, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 4.14/2.08  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.14/2.08  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.14/2.08  tff(c_590, plain, (![B_83, A_84]: (v4_pre_topc(B_83, A_84) | k2_pre_topc(A_84, B_83)!=B_83 | ~v2_pre_topc(A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.14/2.08  tff(c_596, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_590])).
% 4.14/2.08  tff(c_600, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_596])).
% 4.14/2.08  tff(c_601, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_121, c_600])).
% 4.14/2.08  tff(c_602, plain, (![A_85, B_86]: (k4_subset_1(u1_struct_0(A_85), B_86, k2_tops_1(A_85, B_86))=k2_pre_topc(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.14/2.08  tff(c_606, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_602])).
% 4.14/2.08  tff(c_610, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_606])).
% 4.14/2.08  tff(c_331, plain, (![A_61, B_62, C_63]: (k7_subset_1(A_61, B_62, C_63)=k4_xboole_0(B_62, C_63) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.14/2.08  tff(c_335, plain, (![C_64]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_64)=k4_xboole_0('#skF_2', C_64))), inference(resolution, [status(thm)], [c_30, c_331])).
% 4.14/2.08  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.14/2.08  tff(c_282, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_121, c_42])).
% 4.14/2.08  tff(c_341, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_335, c_282])).
% 4.14/2.08  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.14/2.08  tff(c_116, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.14/2.08  tff(c_290, plain, (![A_57, B_58]: (k3_xboole_0(k4_xboole_0(A_57, B_58), A_57)=k4_xboole_0(A_57, B_58))), inference(resolution, [status(thm)], [c_8, c_116])).
% 4.14/2.08  tff(c_10, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.14/2.08  tff(c_101, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.14/2.08  tff(c_178, plain, (![B_49, A_50]: (k1_setfam_1(k2_tarski(B_49, A_50))=k3_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_10, c_101])).
% 4.14/2.08  tff(c_18, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.14/2.08  tff(c_210, plain, (![B_53, A_54]: (k3_xboole_0(B_53, A_54)=k3_xboole_0(A_54, B_53))), inference(superposition, [status(thm), theory('equality')], [c_178, c_18])).
% 4.14/2.08  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.14/2.08  tff(c_234, plain, (![B_53, A_54]: (k2_xboole_0(B_53, k3_xboole_0(A_54, B_53))=B_53)), inference(superposition, [status(thm), theory('equality')], [c_210, c_4])).
% 4.14/2.08  tff(c_296, plain, (![A_57, B_58]: (k2_xboole_0(A_57, k4_xboole_0(A_57, B_58))=A_57)), inference(superposition, [status(thm), theory('equality')], [c_290, c_234])).
% 4.14/2.08  tff(c_353, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_341, c_296])).
% 4.14/2.08  tff(c_24, plain, (![A_24, B_25]: (m1_subset_1(k2_tops_1(A_24, B_25), k1_zfmisc_1(u1_struct_0(A_24))) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.14/2.08  tff(c_565, plain, (![A_79, B_80, C_81]: (k4_subset_1(A_79, B_80, C_81)=k2_xboole_0(B_80, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_79)) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.14/2.08  tff(c_697, plain, (![A_104, B_105, B_106]: (k4_subset_1(u1_struct_0(A_104), B_105, k2_tops_1(A_104, B_106))=k2_xboole_0(B_105, k2_tops_1(A_104, B_106)) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_104))) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(resolution, [status(thm)], [c_24, c_565])).
% 4.14/2.08  tff(c_701, plain, (![B_106]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_106))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_106)) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_697])).
% 4.14/2.08  tff(c_706, plain, (![B_107]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_107))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_107)) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_701])).
% 4.14/2.08  tff(c_713, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_706])).
% 4.14/2.09  tff(c_718, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_610, c_353, c_713])).
% 4.14/2.09  tff(c_720, plain, $false, inference(negUnitSimplification, [status(thm)], [c_601, c_718])).
% 4.14/2.09  tff(c_721, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 4.14/2.09  tff(c_985, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_984, c_721])).
% 4.14/2.09  tff(c_722, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 4.14/2.09  tff(c_1021, plain, (![A_138, B_139]: (k2_pre_topc(A_138, B_139)=B_139 | ~v4_pre_topc(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.14/2.09  tff(c_1027, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1021])).
% 4.14/2.09  tff(c_1031, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_722, c_1027])).
% 4.14/2.09  tff(c_1108, plain, (![A_151, B_152]: (k7_subset_1(u1_struct_0(A_151), k2_pre_topc(A_151, B_152), k1_tops_1(A_151, B_152))=k2_tops_1(A_151, B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.14/2.09  tff(c_1117, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1031, c_1108])).
% 4.14/2.09  tff(c_1121, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_984, c_1117])).
% 4.14/2.09  tff(c_1123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_985, c_1121])).
% 4.14/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.14/2.09  
% 4.14/2.09  Inference rules
% 4.14/2.09  ----------------------
% 4.14/2.09  #Ref     : 0
% 4.14/2.09  #Sup     : 266
% 4.14/2.09  #Fact    : 0
% 4.14/2.09  #Define  : 0
% 4.14/2.09  #Split   : 2
% 4.14/2.09  #Chain   : 0
% 4.14/2.09  #Close   : 0
% 4.14/2.09  
% 4.14/2.09  Ordering : KBO
% 4.14/2.09  
% 4.14/2.09  Simplification rules
% 4.14/2.09  ----------------------
% 4.14/2.09  #Subsume      : 9
% 4.14/2.09  #Demod        : 97
% 4.14/2.09  #Tautology    : 198
% 4.14/2.09  #SimpNegUnit  : 4
% 4.14/2.09  #BackRed      : 1
% 4.14/2.09  
% 4.14/2.09  #Partial instantiations: 0
% 4.14/2.09  #Strategies tried      : 1
% 4.14/2.09  
% 4.14/2.09  Timing (in seconds)
% 4.14/2.09  ----------------------
% 4.19/2.09  Preprocessing        : 0.51
% 4.19/2.09  Parsing              : 0.28
% 4.19/2.09  CNF conversion       : 0.03
% 4.19/2.09  Main loop            : 0.65
% 4.19/2.09  Inferencing          : 0.25
% 4.19/2.09  Reduction            : 0.22
% 4.19/2.09  Demodulation         : 0.17
% 4.19/2.09  BG Simplification    : 0.03
% 4.19/2.09  Subsumption          : 0.10
% 4.19/2.09  Abstraction          : 0.04
% 4.19/2.09  MUC search           : 0.00
% 4.19/2.09  Cooper               : 0.00
% 4.19/2.09  Total                : 1.22
% 4.19/2.09  Index Insertion      : 0.00
% 4.19/2.09  Index Deletion       : 0.00
% 4.19/2.09  Index Matching       : 0.00
% 4.19/2.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
