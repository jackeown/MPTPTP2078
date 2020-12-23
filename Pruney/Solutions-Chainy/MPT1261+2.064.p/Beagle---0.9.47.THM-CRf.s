%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:20 EST 2020

% Result     : Theorem 5.98s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 166 expanded)
%              Number of leaves         :   40 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  136 ( 294 expanded)
%              Number of equality atoms :   61 ( 110 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_78,axiom,(
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

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6554,plain,(
    ! [A_246,B_247,C_248] :
      ( k7_subset_1(A_246,B_247,C_248) = k4_xboole_0(B_247,C_248)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(A_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6557,plain,(
    ! [C_248] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_248) = k4_xboole_0('#skF_2',C_248) ),
    inference(resolution,[status(thm)],[c_42,c_6554])).

tff(c_48,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_108,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2305,plain,(
    ! [B_139,A_140] :
      ( v4_pre_topc(B_139,A_140)
      | k2_pre_topc(A_140,B_139) != B_139
      | ~ v2_pre_topc(A_140)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_140)))
      | ~ l1_pre_topc(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2311,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2305])).

tff(c_2315,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_2311])).

tff(c_2316,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_2315])).

tff(c_2574,plain,(
    ! [A_146,B_147] :
      ( k4_subset_1(u1_struct_0(A_146),B_147,k2_tops_1(A_146,B_147)) = k2_pre_topc(A_146,B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2578,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_2574])).

tff(c_2582,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2578])).

tff(c_20,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    ! [A_57,B_58] : k1_setfam_1(k2_tarski(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_199,plain,(
    ! [A_61,B_62] : k1_setfam_1(k2_tarski(A_61,B_62)) = k3_xboole_0(B_62,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_169])).

tff(c_28,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_222,plain,(
    ! [B_63,A_64] : k3_xboole_0(B_63,A_64) = k3_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_28])).

tff(c_102,plain,(
    ! [A_50,B_51] : r1_tarski(k3_xboole_0(A_50,B_51),A_50) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_107,plain,(
    ! [B_51] : k3_xboole_0(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_102,c_12])).

tff(c_286,plain,(
    ! [B_65] : k3_xboole_0(B_65,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_107])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_297,plain,(
    ! [B_65] : k2_xboole_0(B_65,k1_xboole_0) = B_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_6])).

tff(c_65,plain,(
    ! [A_46,B_47] : r1_tarski(k4_xboole_0(A_46,B_47),A_46) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [B_47] : k4_xboole_0(k1_xboole_0,B_47) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_12])).

tff(c_406,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k4_xboole_0(B_73,A_72)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_418,plain,(
    ! [B_47] : k5_xboole_0(B_47,k1_xboole_0) = k2_xboole_0(B_47,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_406])).

tff(c_424,plain,(
    ! [B_47] : k5_xboole_0(B_47,k1_xboole_0) = B_47 ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_418])).

tff(c_721,plain,(
    ! [A_89,B_90,C_91] :
      ( k7_subset_1(A_89,B_90,C_91) = k4_xboole_0(B_90,C_91)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_753,plain,(
    ! [C_94] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_94) = k4_xboole_0('#skF_2',C_94) ),
    inference(resolution,[status(thm)],[c_42,c_721])).

tff(c_54,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_281,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_54])).

tff(c_759,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_281])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1060,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_8])).

tff(c_660,plain,(
    ! [A_85,B_86,C_87] :
      ( r1_tarski(k4_xboole_0(A_85,B_86),C_87)
      | ~ r1_tarski(A_85,k2_xboole_0(B_86,C_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_664,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k1_xboole_0
      | ~ r1_tarski(A_85,k2_xboole_0(B_86,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_660,c_12])).

tff(c_675,plain,(
    ! [A_85,B_86] :
      ( k4_xboole_0(A_85,B_86) = k1_xboole_0
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_664])).

tff(c_1068,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1060,c_675])).

tff(c_18,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1081,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1068,c_18])).

tff(c_1090,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_1081])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(k2_tops_1(A_33,B_34),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1730,plain,(
    ! [A_127,B_128,C_129] :
      ( k4_subset_1(A_127,B_128,C_129) = k2_xboole_0(B_128,C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(A_127))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5552,plain,(
    ! [A_199,B_200,B_201] :
      ( k4_subset_1(u1_struct_0(A_199),B_200,k2_tops_1(A_199,B_201)) = k2_xboole_0(B_200,k2_tops_1(A_199,B_201))
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0(A_199)))
      | ~ l1_pre_topc(A_199) ) ),
    inference(resolution,[status(thm)],[c_34,c_1730])).

tff(c_5556,plain,(
    ! [B_201] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_201)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_201))
      | ~ m1_subset_1(B_201,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_5552])).

tff(c_5922,plain,(
    ! [B_208] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_208)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_208))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5556])).

tff(c_5929,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_5922])).

tff(c_5934,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_1090,c_5929])).

tff(c_5936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2316,c_5934])).

tff(c_5937,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6813,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6557,c_5937])).

tff(c_5938,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_6980,plain,(
    ! [A_268,B_269] :
      ( k2_pre_topc(A_268,B_269) = B_269
      | ~ v4_pre_topc(B_269,A_268)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(u1_struct_0(A_268)))
      | ~ l1_pre_topc(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6986,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_6980])).

tff(c_6990,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5938,c_6986])).

tff(c_8780,plain,(
    ! [A_310,B_311] :
      ( k7_subset_1(u1_struct_0(A_310),k2_pre_topc(A_310,B_311),k1_tops_1(A_310,B_311)) = k2_tops_1(A_310,B_311)
      | ~ m1_subset_1(B_311,k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ l1_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8789,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6990,c_8780])).

tff(c_8793,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6557,c_8789])).

tff(c_8795,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6813,c_8793])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:55:57 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.98/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.26  
% 5.98/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.26  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.98/2.26  
% 5.98/2.26  %Foreground sorts:
% 5.98/2.26  
% 5.98/2.26  
% 5.98/2.26  %Background operators:
% 5.98/2.26  
% 5.98/2.26  
% 5.98/2.26  %Foreground operators:
% 5.98/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.98/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.98/2.26  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.98/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.98/2.26  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.98/2.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.98/2.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.98/2.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.98/2.26  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.98/2.26  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.98/2.26  tff('#skF_2', type, '#skF_2': $i).
% 5.98/2.26  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.98/2.26  tff('#skF_1', type, '#skF_1': $i).
% 5.98/2.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.98/2.26  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.98/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.98/2.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.98/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.98/2.26  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.98/2.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.98/2.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.98/2.26  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.98/2.26  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.98/2.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.98/2.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.98/2.26  
% 5.98/2.27  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.98/2.27  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.98/2.27  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.98/2.27  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.98/2.27  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.98/2.27  tff(f_63, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.98/2.27  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.98/2.27  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 5.98/2.27  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 5.98/2.27  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.98/2.27  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.98/2.27  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 5.98/2.27  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.98/2.27  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.98/2.27  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.98/2.27  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.98/2.27  tff(c_6554, plain, (![A_246, B_247, C_248]: (k7_subset_1(A_246, B_247, C_248)=k4_xboole_0(B_247, C_248) | ~m1_subset_1(B_247, k1_zfmisc_1(A_246)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.98/2.27  tff(c_6557, plain, (![C_248]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_248)=k4_xboole_0('#skF_2', C_248))), inference(resolution, [status(thm)], [c_42, c_6554])).
% 5.98/2.27  tff(c_48, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.98/2.27  tff(c_108, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 5.98/2.27  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.98/2.27  tff(c_46, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.98/2.27  tff(c_2305, plain, (![B_139, A_140]: (v4_pre_topc(B_139, A_140) | k2_pre_topc(A_140, B_139)!=B_139 | ~v2_pre_topc(A_140) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_140))) | ~l1_pre_topc(A_140))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.98/2.27  tff(c_2311, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2305])).
% 5.98/2.27  tff(c_2315, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_2311])).
% 5.98/2.27  tff(c_2316, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_108, c_2315])).
% 5.98/2.27  tff(c_2574, plain, (![A_146, B_147]: (k4_subset_1(u1_struct_0(A_146), B_147, k2_tops_1(A_146, B_147))=k2_pre_topc(A_146, B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.98/2.27  tff(c_2578, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_2574])).
% 5.98/2.27  tff(c_2582, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2578])).
% 5.98/2.27  tff(c_20, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.98/2.27  tff(c_169, plain, (![A_57, B_58]: (k1_setfam_1(k2_tarski(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.98/2.27  tff(c_199, plain, (![A_61, B_62]: (k1_setfam_1(k2_tarski(A_61, B_62))=k3_xboole_0(B_62, A_61))), inference(superposition, [status(thm), theory('equality')], [c_20, c_169])).
% 5.98/2.27  tff(c_28, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.98/2.27  tff(c_222, plain, (![B_63, A_64]: (k3_xboole_0(B_63, A_64)=k3_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_199, c_28])).
% 5.98/2.27  tff(c_102, plain, (![A_50, B_51]: (r1_tarski(k3_xboole_0(A_50, B_51), A_50))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.98/2.27  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.98/2.27  tff(c_107, plain, (![B_51]: (k3_xboole_0(k1_xboole_0, B_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_102, c_12])).
% 5.98/2.27  tff(c_286, plain, (![B_65]: (k3_xboole_0(B_65, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_222, c_107])).
% 5.98/2.27  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.98/2.27  tff(c_297, plain, (![B_65]: (k2_xboole_0(B_65, k1_xboole_0)=B_65)), inference(superposition, [status(thm), theory('equality')], [c_286, c_6])).
% 5.98/2.27  tff(c_65, plain, (![A_46, B_47]: (r1_tarski(k4_xboole_0(A_46, B_47), A_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.98/2.27  tff(c_73, plain, (![B_47]: (k4_xboole_0(k1_xboole_0, B_47)=k1_xboole_0)), inference(resolution, [status(thm)], [c_65, c_12])).
% 5.98/2.27  tff(c_406, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k4_xboole_0(B_73, A_72))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.27  tff(c_418, plain, (![B_47]: (k5_xboole_0(B_47, k1_xboole_0)=k2_xboole_0(B_47, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_73, c_406])).
% 5.98/2.27  tff(c_424, plain, (![B_47]: (k5_xboole_0(B_47, k1_xboole_0)=B_47)), inference(demodulation, [status(thm), theory('equality')], [c_297, c_418])).
% 5.98/2.27  tff(c_721, plain, (![A_89, B_90, C_91]: (k7_subset_1(A_89, B_90, C_91)=k4_xboole_0(B_90, C_91) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.98/2.27  tff(c_753, plain, (![C_94]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_94)=k4_xboole_0('#skF_2', C_94))), inference(resolution, [status(thm)], [c_42, c_721])).
% 5.98/2.27  tff(c_54, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.98/2.27  tff(c_281, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_108, c_54])).
% 5.98/2.27  tff(c_759, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_753, c_281])).
% 5.98/2.27  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.98/2.27  tff(c_1060, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_759, c_8])).
% 5.98/2.27  tff(c_660, plain, (![A_85, B_86, C_87]: (r1_tarski(k4_xboole_0(A_85, B_86), C_87) | ~r1_tarski(A_85, k2_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.98/2.27  tff(c_664, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k1_xboole_0 | ~r1_tarski(A_85, k2_xboole_0(B_86, k1_xboole_0)))), inference(resolution, [status(thm)], [c_660, c_12])).
% 5.98/2.27  tff(c_675, plain, (![A_85, B_86]: (k4_xboole_0(A_85, B_86)=k1_xboole_0 | ~r1_tarski(A_85, B_86))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_664])).
% 5.98/2.27  tff(c_1068, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1060, c_675])).
% 5.98/2.27  tff(c_18, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.98/2.27  tff(c_1081, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1068, c_18])).
% 5.98/2.27  tff(c_1090, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_424, c_1081])).
% 5.98/2.27  tff(c_34, plain, (![A_33, B_34]: (m1_subset_1(k2_tops_1(A_33, B_34), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_subset_1(B_34, k1_zfmisc_1(u1_struct_0(A_33))) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.98/2.27  tff(c_1730, plain, (![A_127, B_128, C_129]: (k4_subset_1(A_127, B_128, C_129)=k2_xboole_0(B_128, C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(A_127)) | ~m1_subset_1(B_128, k1_zfmisc_1(A_127)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.98/2.27  tff(c_5552, plain, (![A_199, B_200, B_201]: (k4_subset_1(u1_struct_0(A_199), B_200, k2_tops_1(A_199, B_201))=k2_xboole_0(B_200, k2_tops_1(A_199, B_201)) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_199))) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0(A_199))) | ~l1_pre_topc(A_199))), inference(resolution, [status(thm)], [c_34, c_1730])).
% 5.98/2.27  tff(c_5556, plain, (![B_201]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_201))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_201)) | ~m1_subset_1(B_201, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_5552])).
% 5.98/2.27  tff(c_5922, plain, (![B_208]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_208))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_208)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5556])).
% 5.98/2.27  tff(c_5929, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_5922])).
% 5.98/2.27  tff(c_5934, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_1090, c_5929])).
% 5.98/2.27  tff(c_5936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2316, c_5934])).
% 5.98/2.27  tff(c_5937, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 5.98/2.27  tff(c_6813, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6557, c_5937])).
% 5.98/2.27  tff(c_5938, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 5.98/2.27  tff(c_6980, plain, (![A_268, B_269]: (k2_pre_topc(A_268, B_269)=B_269 | ~v4_pre_topc(B_269, A_268) | ~m1_subset_1(B_269, k1_zfmisc_1(u1_struct_0(A_268))) | ~l1_pre_topc(A_268))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.98/2.27  tff(c_6986, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_6980])).
% 5.98/2.27  tff(c_6990, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5938, c_6986])).
% 5.98/2.27  tff(c_8780, plain, (![A_310, B_311]: (k7_subset_1(u1_struct_0(A_310), k2_pre_topc(A_310, B_311), k1_tops_1(A_310, B_311))=k2_tops_1(A_310, B_311) | ~m1_subset_1(B_311, k1_zfmisc_1(u1_struct_0(A_310))) | ~l1_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.98/2.27  tff(c_8789, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6990, c_8780])).
% 5.98/2.27  tff(c_8793, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6557, c_8789])).
% 5.98/2.27  tff(c_8795, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6813, c_8793])).
% 5.98/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.98/2.27  
% 5.98/2.27  Inference rules
% 5.98/2.27  ----------------------
% 5.98/2.27  #Ref     : 0
% 5.98/2.27  #Sup     : 2130
% 5.98/2.27  #Fact    : 0
% 5.98/2.27  #Define  : 0
% 5.98/2.27  #Split   : 3
% 5.98/2.27  #Chain   : 0
% 5.98/2.27  #Close   : 0
% 5.98/2.27  
% 5.98/2.27  Ordering : KBO
% 5.98/2.27  
% 5.98/2.27  Simplification rules
% 5.98/2.27  ----------------------
% 5.98/2.27  #Subsume      : 142
% 5.98/2.28  #Demod        : 2921
% 5.98/2.28  #Tautology    : 1759
% 5.98/2.28  #SimpNegUnit  : 4
% 5.98/2.28  #BackRed      : 5
% 5.98/2.28  
% 5.98/2.28  #Partial instantiations: 0
% 5.98/2.28  #Strategies tried      : 1
% 5.98/2.28  
% 5.98/2.28  Timing (in seconds)
% 5.98/2.28  ----------------------
% 5.98/2.28  Preprocessing        : 0.33
% 5.98/2.28  Parsing              : 0.18
% 5.98/2.28  CNF conversion       : 0.02
% 5.98/2.28  Main loop            : 1.18
% 5.98/2.28  Inferencing          : 0.35
% 5.98/2.28  Reduction            : 0.58
% 5.98/2.28  Demodulation         : 0.49
% 5.98/2.28  BG Simplification    : 0.03
% 5.98/2.28  Subsumption          : 0.15
% 5.98/2.28  Abstraction          : 0.06
% 5.98/2.28  MUC search           : 0.00
% 5.98/2.28  Cooper               : 0.00
% 5.98/2.28  Total                : 1.55
% 5.98/2.28  Index Insertion      : 0.00
% 5.98/2.28  Index Deletion       : 0.00
% 5.98/2.28  Index Matching       : 0.00
% 5.98/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
