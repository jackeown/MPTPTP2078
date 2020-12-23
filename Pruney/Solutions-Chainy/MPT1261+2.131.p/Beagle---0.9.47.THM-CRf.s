%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:30 EST 2020

% Result     : Theorem 12.94s
% Output     : CNFRefutation 13.13s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 260 expanded)
%              Number of leaves         :   51 ( 107 expanded)
%              Depth                    :   12
%              Number of atoms          :  184 ( 404 expanded)
%              Number of equality atoms :   90 ( 178 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_158,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_110,axiom,(
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

tff(f_51,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_130,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_116,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_139,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_146,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_25737,plain,(
    ! [A_627,B_628,C_629] :
      ( k7_subset_1(A_627,B_628,C_629) = k4_xboole_0(B_628,C_629)
      | ~ m1_subset_1(B_628,k1_zfmisc_1(A_627)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_25752,plain,(
    ! [C_629] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_629) = k4_xboole_0('#skF_4',C_629) ),
    inference(resolution,[status(thm)],[c_78,c_25737])).

tff(c_84,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_120,plain,(
    ~ v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_80,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_82,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3785,plain,(
    ! [B_200,A_201] :
      ( v4_pre_topc(B_200,A_201)
      | k2_pre_topc(A_201,B_200) != B_200
      | ~ v2_pre_topc(A_201)
      | ~ m1_subset_1(B_200,k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_pre_topc(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_3803,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4'
    | ~ v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_3785])).

tff(c_3814,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_82,c_3803])).

tff(c_3815,plain,(
    k2_pre_topc('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_3814])).

tff(c_32,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_154,plain,(
    ! [A_70,B_71] :
      ( k3_xboole_0(A_70,B_71) = A_70
      | ~ r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_176,plain,(
    ! [A_73] : k3_xboole_0(k1_xboole_0,A_73) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_154])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_185,plain,(
    ! [A_73] : k3_xboole_0(A_73,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_2])).

tff(c_38,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_459,plain,(
    ! [A_100,B_101] : k4_xboole_0(A_100,k4_xboole_0(A_100,B_101)) = k3_xboole_0(A_100,B_101) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_500,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k3_xboole_0(A_20,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_459])).

tff(c_507,plain,(
    ! [A_20] : k4_xboole_0(A_20,A_20) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_500])).

tff(c_42,plain,(
    ! [A_23] : k2_subset_1(A_23) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_46,plain,(
    ! [A_26] : m1_subset_1(k2_subset_1(A_26),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_92,plain,(
    ! [A_26] : m1_subset_1(A_26,k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_756,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(A_118,B_119) = k3_subset_1(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_768,plain,(
    ! [A_26] : k4_xboole_0(A_26,A_26) = k3_subset_1(A_26,A_26) ),
    inference(resolution,[status(thm)],[c_92,c_756])).

tff(c_773,plain,(
    ! [A_26] : k3_subset_1(A_26,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_768])).

tff(c_56,plain,(
    ! [A_37,B_38] :
      ( k4_subset_1(A_37,B_38,k3_subset_1(A_37,B_38)) = k2_subset_1(A_37)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1393,plain,(
    ! [A_141,B_142] :
      ( k4_subset_1(A_141,B_142,k3_subset_1(A_141,B_142)) = A_141
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_141)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_56])).

tff(c_1403,plain,(
    ! [A_26] : k4_subset_1(A_26,A_26,k3_subset_1(A_26,A_26)) = A_26 ),
    inference(resolution,[status(thm)],[c_92,c_1393])).

tff(c_1410,plain,(
    ! [A_26] : k4_subset_1(A_26,A_26,k1_xboole_0) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_1403])).

tff(c_62,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_3534,plain,(
    ! [A_192,B_193,C_194] :
      ( k4_subset_1(A_192,B_193,C_194) = k2_xboole_0(B_193,C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(A_192))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(A_192)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_13916,plain,(
    ! [B_371,B_372,A_373] :
      ( k4_subset_1(B_371,B_372,A_373) = k2_xboole_0(B_372,A_373)
      | ~ m1_subset_1(B_372,k1_zfmisc_1(B_371))
      | ~ r1_tarski(A_373,B_371) ) ),
    inference(resolution,[status(thm)],[c_62,c_3534])).

tff(c_14994,plain,(
    ! [A_393,A_394] :
      ( k4_subset_1(A_393,A_393,A_394) = k2_xboole_0(A_393,A_394)
      | ~ r1_tarski(A_394,A_393) ) ),
    inference(resolution,[status(thm)],[c_92,c_13916])).

tff(c_15034,plain,(
    ! [A_15] : k4_subset_1(A_15,A_15,k1_xboole_0) = k2_xboole_0(A_15,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_14994])).

tff(c_15064,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1410,c_15034])).

tff(c_511,plain,(
    ! [A_102] : k4_xboole_0(A_102,A_102) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_500])).

tff(c_36,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_519,plain,(
    ! [A_102] : k2_xboole_0(A_102,k1_xboole_0) = k2_xboole_0(A_102,A_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_36])).

tff(c_15069,plain,(
    ! [A_102] : k2_xboole_0(A_102,A_102) = A_102 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15064,c_519])).

tff(c_2147,plain,(
    ! [A_161,B_162,C_163] :
      ( k7_subset_1(A_161,B_162,C_163) = k4_xboole_0(B_162,C_163)
      | ~ m1_subset_1(B_162,k1_zfmisc_1(A_161)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2190,plain,(
    ! [C_168] : k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',C_168) = k4_xboole_0('#skF_4',C_168) ),
    inference(resolution,[status(thm)],[c_78,c_2147])).

tff(c_90,plain,
    ( v4_pre_topc('#skF_4','#skF_3')
    | k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_253,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_90])).

tff(c_2196,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2190,c_253])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_165,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_26,c_154])).

tff(c_354,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_372,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k4_xboole_0(B_10,B_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_354])).

tff(c_510,plain,(
    ! [B_10] : k5_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_372])).

tff(c_34,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_848,plain,(
    ! [A_123,B_124] : k3_xboole_0(k4_xboole_0(A_123,B_124),A_123) = k4_xboole_0(A_123,B_124) ),
    inference(resolution,[status(thm)],[c_34,c_154])).

tff(c_28,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_866,plain,(
    ! [A_123,B_124] : k5_xboole_0(k4_xboole_0(A_123,B_124),k4_xboole_0(A_123,B_124)) = k4_xboole_0(k4_xboole_0(A_123,B_124),A_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_848,c_28])).

tff(c_924,plain,(
    ! [A_125,B_126] : k4_xboole_0(k4_xboole_0(A_125,B_126),A_125) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_866])).

tff(c_2321,plain,(
    ! [A_171,B_172] : k2_xboole_0(A_171,k4_xboole_0(A_171,B_172)) = k2_xboole_0(A_171,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_924,c_36])).

tff(c_2337,plain,(
    k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2196,c_2321])).

tff(c_2381,plain,(
    k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_2337])).

tff(c_15093,plain,(
    k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15069,c_2381])).

tff(c_5413,plain,(
    ! [A_233,B_234] :
      ( k4_subset_1(u1_struct_0(A_233),B_234,k2_tops_1(A_233,B_234)) = k2_pre_topc(A_233,B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(u1_struct_0(A_233)))
      | ~ l1_pre_topc(A_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_5426,plain,
    ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_5413])).

tff(c_5436,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5426])).

tff(c_68,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k2_tops_1(A_46,B_47),k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(u1_struct_0(A_46)))
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24338,plain,(
    ! [A_549,B_550,B_551] :
      ( k4_subset_1(u1_struct_0(A_549),B_550,k2_tops_1(A_549,B_551)) = k2_xboole_0(B_550,k2_tops_1(A_549,B_551))
      | ~ m1_subset_1(B_550,k1_zfmisc_1(u1_struct_0(A_549)))
      | ~ m1_subset_1(B_551,k1_zfmisc_1(u1_struct_0(A_549)))
      | ~ l1_pre_topc(A_549) ) ),
    inference(resolution,[status(thm)],[c_68,c_3534])).

tff(c_24353,plain,(
    ! [B_551] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3',B_551)) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3',B_551))
      | ~ m1_subset_1(B_551,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_78,c_24338])).

tff(c_24370,plain,(
    ! [B_552] :
      ( k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3',B_552)) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3',B_552))
      | ~ m1_subset_1(B_552,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_24353])).

tff(c_24393,plain,(
    k4_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_78,c_24370])).

tff(c_24409,plain,(
    k2_pre_topc('#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15093,c_5436,c_24393])).

tff(c_24411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3815,c_24409])).

tff(c_24412,plain,(
    k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_25780,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) != k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25752,c_24412])).

tff(c_24447,plain,(
    ! [A_555,B_556] :
      ( k3_xboole_0(A_555,B_556) = A_555
      | ~ r1_tarski(A_555,B_556) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24458,plain,(
    ! [B_10] : k3_xboole_0(B_10,B_10) = B_10 ),
    inference(resolution,[status(thm)],[c_26,c_24447])).

tff(c_24413,plain,(
    v4_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_27323,plain,(
    ! [A_667,B_668] :
      ( r1_tarski(k2_tops_1(A_667,B_668),B_668)
      | ~ v4_pre_topc(B_668,A_667)
      | ~ m1_subset_1(B_668,k1_zfmisc_1(u1_struct_0(A_667)))
      | ~ l1_pre_topc(A_667) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_27336,plain,
    ( r1_tarski(k2_tops_1('#skF_3','#skF_4'),'#skF_4')
    | ~ v4_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_27323])).

tff(c_27346,plain,(
    r1_tarski(k2_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_24413,c_27336])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_27354,plain,(
    k3_xboole_0(k2_tops_1('#skF_3','#skF_4'),'#skF_4') = k2_tops_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_27346,c_30])).

tff(c_24584,plain,(
    ! [A_571,B_572] : k4_xboole_0(A_571,k4_xboole_0(A_571,B_572)) = k3_xboole_0(A_571,B_572) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24637,plain,(
    ! [A_574,B_575] : r1_tarski(k3_xboole_0(A_574,B_575),A_574) ),
    inference(superposition,[status(thm),theory(equality)],[c_24584,c_34])).

tff(c_24659,plain,(
    ! [A_574,B_575] : k3_xboole_0(k3_xboole_0(A_574,B_575),A_574) = k3_xboole_0(A_574,B_575) ),
    inference(resolution,[status(thm)],[c_24637,c_30])).

tff(c_27391,plain,(
    k3_xboole_0(k2_tops_1('#skF_3','#skF_4'),k2_tops_1('#skF_3','#skF_4')) = k3_xboole_0(k2_tops_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_27354,c_24659])).

tff(c_27438,plain,(
    k3_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24458,c_2,c_27391])).

tff(c_29088,plain,(
    ! [A_716,B_717] :
      ( k7_subset_1(u1_struct_0(A_716),B_717,k2_tops_1(A_716,B_717)) = k1_tops_1(A_716,B_717)
      | ~ m1_subset_1(B_717,k1_zfmisc_1(u1_struct_0(A_716)))
      | ~ l1_pre_topc(A_716) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_29101,plain,
    ( k7_subset_1(u1_struct_0('#skF_3'),'#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_29088])).

tff(c_29112,plain,(
    k4_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) = k1_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_25752,c_29101])).

tff(c_40,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_29157,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4',k2_tops_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_29112,c_40])).

tff(c_29172,plain,(
    k4_xboole_0('#skF_4',k1_tops_1('#skF_3','#skF_4')) = k2_tops_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27438,c_29157])).

tff(c_29174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25780,c_29172])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:51:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.94/5.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.94/5.90  
% 12.94/5.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.94/5.91  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 12.94/5.91  
% 12.94/5.91  %Foreground sorts:
% 12.94/5.91  
% 12.94/5.91  
% 12.94/5.91  %Background operators:
% 12.94/5.91  
% 12.94/5.91  
% 12.94/5.91  %Foreground operators:
% 12.94/5.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.94/5.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.94/5.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.94/5.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.94/5.91  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 12.94/5.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.94/5.91  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 12.94/5.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.94/5.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.94/5.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.94/5.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.94/5.91  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.94/5.91  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 12.94/5.91  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 12.94/5.91  tff('#skF_3', type, '#skF_3': $i).
% 12.94/5.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.94/5.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.94/5.91  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 12.94/5.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.94/5.91  tff('#skF_4', type, '#skF_4': $i).
% 12.94/5.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.94/5.91  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 12.94/5.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.94/5.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.94/5.91  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 12.94/5.91  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.94/5.91  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 12.94/5.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.94/5.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.94/5.91  
% 13.13/5.93  tff(f_158, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 13.13/5.93  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 13.13/5.93  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 13.13/5.93  tff(f_51, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.13/5.93  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 13.13/5.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.13/5.93  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 13.13/5.93  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.13/5.93  tff(f_61, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 13.13/5.93  tff(f_67, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 13.13/5.93  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 13.13/5.93  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 13.13/5.93  tff(f_95, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.13/5.93  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 13.13/5.93  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 13.13/5.93  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.13/5.93  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.13/5.93  tff(f_53, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 13.13/5.93  tff(f_130, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 13.13/5.93  tff(f_116, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 13.13/5.93  tff(f_139, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 13.13/5.93  tff(f_146, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 13.13/5.93  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.13/5.93  tff(c_25737, plain, (![A_627, B_628, C_629]: (k7_subset_1(A_627, B_628, C_629)=k4_xboole_0(B_628, C_629) | ~m1_subset_1(B_628, k1_zfmisc_1(A_627)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.13/5.93  tff(c_25752, plain, (![C_629]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_629)=k4_xboole_0('#skF_4', C_629))), inference(resolution, [status(thm)], [c_78, c_25737])).
% 13.13/5.93  tff(c_84, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.13/5.93  tff(c_120, plain, (~v4_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_84])).
% 13.13/5.93  tff(c_80, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.13/5.93  tff(c_82, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.13/5.93  tff(c_3785, plain, (![B_200, A_201]: (v4_pre_topc(B_200, A_201) | k2_pre_topc(A_201, B_200)!=B_200 | ~v2_pre_topc(A_201) | ~m1_subset_1(B_200, k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_pre_topc(A_201))), inference(cnfTransformation, [status(thm)], [f_110])).
% 13.13/5.93  tff(c_3803, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4' | ~v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_78, c_3785])).
% 13.13/5.93  tff(c_3814, plain, (v4_pre_topc('#skF_4', '#skF_3') | k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_82, c_3803])).
% 13.13/5.93  tff(c_3815, plain, (k2_pre_topc('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_120, c_3814])).
% 13.13/5.93  tff(c_32, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.13/5.93  tff(c_154, plain, (![A_70, B_71]: (k3_xboole_0(A_70, B_71)=A_70 | ~r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.13/5.93  tff(c_176, plain, (![A_73]: (k3_xboole_0(k1_xboole_0, A_73)=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_154])).
% 13.13/5.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.13/5.93  tff(c_185, plain, (![A_73]: (k3_xboole_0(A_73, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_176, c_2])).
% 13.13/5.93  tff(c_38, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.13/5.93  tff(c_459, plain, (![A_100, B_101]: (k4_xboole_0(A_100, k4_xboole_0(A_100, B_101))=k3_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.13/5.93  tff(c_500, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k3_xboole_0(A_20, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_459])).
% 13.13/5.93  tff(c_507, plain, (![A_20]: (k4_xboole_0(A_20, A_20)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_500])).
% 13.13/5.93  tff(c_42, plain, (![A_23]: (k2_subset_1(A_23)=A_23)), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.13/5.93  tff(c_46, plain, (![A_26]: (m1_subset_1(k2_subset_1(A_26), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.13/5.93  tff(c_92, plain, (![A_26]: (m1_subset_1(A_26, k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 13.13/5.93  tff(c_756, plain, (![A_118, B_119]: (k4_xboole_0(A_118, B_119)=k3_subset_1(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.13/5.93  tff(c_768, plain, (![A_26]: (k4_xboole_0(A_26, A_26)=k3_subset_1(A_26, A_26))), inference(resolution, [status(thm)], [c_92, c_756])).
% 13.13/5.93  tff(c_773, plain, (![A_26]: (k3_subset_1(A_26, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_507, c_768])).
% 13.13/5.93  tff(c_56, plain, (![A_37, B_38]: (k4_subset_1(A_37, B_38, k3_subset_1(A_37, B_38))=k2_subset_1(A_37) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.13/5.93  tff(c_1393, plain, (![A_141, B_142]: (k4_subset_1(A_141, B_142, k3_subset_1(A_141, B_142))=A_141 | ~m1_subset_1(B_142, k1_zfmisc_1(A_141)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_56])).
% 13.13/5.93  tff(c_1403, plain, (![A_26]: (k4_subset_1(A_26, A_26, k3_subset_1(A_26, A_26))=A_26)), inference(resolution, [status(thm)], [c_92, c_1393])).
% 13.13/5.93  tff(c_1410, plain, (![A_26]: (k4_subset_1(A_26, A_26, k1_xboole_0)=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_773, c_1403])).
% 13.13/5.93  tff(c_62, plain, (![A_41, B_42]: (m1_subset_1(A_41, k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.13/5.93  tff(c_3534, plain, (![A_192, B_193, C_194]: (k4_subset_1(A_192, B_193, C_194)=k2_xboole_0(B_193, C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(A_192)) | ~m1_subset_1(B_193, k1_zfmisc_1(A_192)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.13/5.93  tff(c_13916, plain, (![B_371, B_372, A_373]: (k4_subset_1(B_371, B_372, A_373)=k2_xboole_0(B_372, A_373) | ~m1_subset_1(B_372, k1_zfmisc_1(B_371)) | ~r1_tarski(A_373, B_371))), inference(resolution, [status(thm)], [c_62, c_3534])).
% 13.13/5.93  tff(c_14994, plain, (![A_393, A_394]: (k4_subset_1(A_393, A_393, A_394)=k2_xboole_0(A_393, A_394) | ~r1_tarski(A_394, A_393))), inference(resolution, [status(thm)], [c_92, c_13916])).
% 13.13/5.93  tff(c_15034, plain, (![A_15]: (k4_subset_1(A_15, A_15, k1_xboole_0)=k2_xboole_0(A_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_14994])).
% 13.13/5.93  tff(c_15064, plain, (![A_15]: (k2_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_1410, c_15034])).
% 13.13/5.93  tff(c_511, plain, (![A_102]: (k4_xboole_0(A_102, A_102)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_185, c_500])).
% 13.13/5.93  tff(c_36, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.13/5.93  tff(c_519, plain, (![A_102]: (k2_xboole_0(A_102, k1_xboole_0)=k2_xboole_0(A_102, A_102))), inference(superposition, [status(thm), theory('equality')], [c_511, c_36])).
% 13.13/5.93  tff(c_15069, plain, (![A_102]: (k2_xboole_0(A_102, A_102)=A_102)), inference(demodulation, [status(thm), theory('equality')], [c_15064, c_519])).
% 13.13/5.93  tff(c_2147, plain, (![A_161, B_162, C_163]: (k7_subset_1(A_161, B_162, C_163)=k4_xboole_0(B_162, C_163) | ~m1_subset_1(B_162, k1_zfmisc_1(A_161)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.13/5.93  tff(c_2190, plain, (![C_168]: (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', C_168)=k4_xboole_0('#skF_4', C_168))), inference(resolution, [status(thm)], [c_78, c_2147])).
% 13.13/5.93  tff(c_90, plain, (v4_pre_topc('#skF_4', '#skF_3') | k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_158])).
% 13.13/5.93  tff(c_253, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_120, c_90])).
% 13.13/5.93  tff(c_2196, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2190, c_253])).
% 13.13/5.93  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.13/5.93  tff(c_165, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_26, c_154])).
% 13.13/5.93  tff(c_354, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.13/5.93  tff(c_372, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k4_xboole_0(B_10, B_10))), inference(superposition, [status(thm), theory('equality')], [c_165, c_354])).
% 13.13/5.93  tff(c_510, plain, (![B_10]: (k5_xboole_0(B_10, B_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_507, c_372])).
% 13.13/5.93  tff(c_34, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.13/5.93  tff(c_848, plain, (![A_123, B_124]: (k3_xboole_0(k4_xboole_0(A_123, B_124), A_123)=k4_xboole_0(A_123, B_124))), inference(resolution, [status(thm)], [c_34, c_154])).
% 13.13/5.93  tff(c_28, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.13/5.93  tff(c_866, plain, (![A_123, B_124]: (k5_xboole_0(k4_xboole_0(A_123, B_124), k4_xboole_0(A_123, B_124))=k4_xboole_0(k4_xboole_0(A_123, B_124), A_123))), inference(superposition, [status(thm), theory('equality')], [c_848, c_28])).
% 13.13/5.93  tff(c_924, plain, (![A_125, B_126]: (k4_xboole_0(k4_xboole_0(A_125, B_126), A_125)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_510, c_866])).
% 13.13/5.93  tff(c_2321, plain, (![A_171, B_172]: (k2_xboole_0(A_171, k4_xboole_0(A_171, B_172))=k2_xboole_0(A_171, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_924, c_36])).
% 13.13/5.93  tff(c_2337, plain, (k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2196, c_2321])).
% 13.13/5.93  tff(c_2381, plain, (k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_519, c_2337])).
% 13.13/5.93  tff(c_15093, plain, (k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15069, c_2381])).
% 13.13/5.93  tff(c_5413, plain, (![A_233, B_234]: (k4_subset_1(u1_struct_0(A_233), B_234, k2_tops_1(A_233, B_234))=k2_pre_topc(A_233, B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(u1_struct_0(A_233))) | ~l1_pre_topc(A_233))), inference(cnfTransformation, [status(thm)], [f_130])).
% 13.13/5.93  tff(c_5426, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_78, c_5413])).
% 13.13/5.93  tff(c_5436, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5426])).
% 13.13/5.93  tff(c_68, plain, (![A_46, B_47]: (m1_subset_1(k2_tops_1(A_46, B_47), k1_zfmisc_1(u1_struct_0(A_46))) | ~m1_subset_1(B_47, k1_zfmisc_1(u1_struct_0(A_46))) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_116])).
% 13.13/5.93  tff(c_24338, plain, (![A_549, B_550, B_551]: (k4_subset_1(u1_struct_0(A_549), B_550, k2_tops_1(A_549, B_551))=k2_xboole_0(B_550, k2_tops_1(A_549, B_551)) | ~m1_subset_1(B_550, k1_zfmisc_1(u1_struct_0(A_549))) | ~m1_subset_1(B_551, k1_zfmisc_1(u1_struct_0(A_549))) | ~l1_pre_topc(A_549))), inference(resolution, [status(thm)], [c_68, c_3534])).
% 13.13/5.93  tff(c_24353, plain, (![B_551]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', B_551))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', B_551)) | ~m1_subset_1(B_551, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_24338])).
% 13.13/5.93  tff(c_24370, plain, (![B_552]: (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', B_552))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', B_552)) | ~m1_subset_1(B_552, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_24353])).
% 13.13/5.93  tff(c_24393, plain, (k4_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_78, c_24370])).
% 13.13/5.93  tff(c_24409, plain, (k2_pre_topc('#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_15093, c_5436, c_24393])).
% 13.13/5.93  tff(c_24411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3815, c_24409])).
% 13.13/5.93  tff(c_24412, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_84])).
% 13.13/5.93  tff(c_25780, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))!=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25752, c_24412])).
% 13.13/5.93  tff(c_24447, plain, (![A_555, B_556]: (k3_xboole_0(A_555, B_556)=A_555 | ~r1_tarski(A_555, B_556))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.13/5.93  tff(c_24458, plain, (![B_10]: (k3_xboole_0(B_10, B_10)=B_10)), inference(resolution, [status(thm)], [c_26, c_24447])).
% 13.13/5.93  tff(c_24413, plain, (v4_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_84])).
% 13.13/5.93  tff(c_27323, plain, (![A_667, B_668]: (r1_tarski(k2_tops_1(A_667, B_668), B_668) | ~v4_pre_topc(B_668, A_667) | ~m1_subset_1(B_668, k1_zfmisc_1(u1_struct_0(A_667))) | ~l1_pre_topc(A_667))), inference(cnfTransformation, [status(thm)], [f_139])).
% 13.13/5.93  tff(c_27336, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), '#skF_4') | ~v4_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_78, c_27323])).
% 13.13/5.93  tff(c_27346, plain, (r1_tarski(k2_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_24413, c_27336])).
% 13.13/5.93  tff(c_30, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.13/5.93  tff(c_27354, plain, (k3_xboole_0(k2_tops_1('#skF_3', '#skF_4'), '#skF_4')=k2_tops_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_27346, c_30])).
% 13.13/5.93  tff(c_24584, plain, (![A_571, B_572]: (k4_xboole_0(A_571, k4_xboole_0(A_571, B_572))=k3_xboole_0(A_571, B_572))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.13/5.93  tff(c_24637, plain, (![A_574, B_575]: (r1_tarski(k3_xboole_0(A_574, B_575), A_574))), inference(superposition, [status(thm), theory('equality')], [c_24584, c_34])).
% 13.13/5.93  tff(c_24659, plain, (![A_574, B_575]: (k3_xboole_0(k3_xboole_0(A_574, B_575), A_574)=k3_xboole_0(A_574, B_575))), inference(resolution, [status(thm)], [c_24637, c_30])).
% 13.13/5.93  tff(c_27391, plain, (k3_xboole_0(k2_tops_1('#skF_3', '#skF_4'), k2_tops_1('#skF_3', '#skF_4'))=k3_xboole_0(k2_tops_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_27354, c_24659])).
% 13.13/5.93  tff(c_27438, plain, (k3_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_24458, c_2, c_27391])).
% 13.13/5.93  tff(c_29088, plain, (![A_716, B_717]: (k7_subset_1(u1_struct_0(A_716), B_717, k2_tops_1(A_716, B_717))=k1_tops_1(A_716, B_717) | ~m1_subset_1(B_717, k1_zfmisc_1(u1_struct_0(A_716))) | ~l1_pre_topc(A_716))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.13/5.93  tff(c_29101, plain, (k7_subset_1(u1_struct_0('#skF_3'), '#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_78, c_29088])).
% 13.13/5.93  tff(c_29112, plain, (k4_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))=k1_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_25752, c_29101])).
% 13.13/5.93  tff(c_40, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.13/5.93  tff(c_29157, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', k2_tops_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_29112, c_40])).
% 13.13/5.93  tff(c_29172, plain, (k4_xboole_0('#skF_4', k1_tops_1('#skF_3', '#skF_4'))=k2_tops_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_27438, c_29157])).
% 13.13/5.93  tff(c_29174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25780, c_29172])).
% 13.13/5.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.13/5.93  
% 13.13/5.93  Inference rules
% 13.13/5.93  ----------------------
% 13.13/5.93  #Ref     : 0
% 13.13/5.93  #Sup     : 7168
% 13.13/5.93  #Fact    : 0
% 13.13/5.93  #Define  : 0
% 13.13/5.93  #Split   : 8
% 13.13/5.93  #Chain   : 0
% 13.13/5.93  #Close   : 0
% 13.13/5.93  
% 13.13/5.93  Ordering : KBO
% 13.13/5.93  
% 13.13/5.93  Simplification rules
% 13.13/5.93  ----------------------
% 13.13/5.93  #Subsume      : 754
% 13.13/5.93  #Demod        : 9396
% 13.13/5.93  #Tautology    : 4547
% 13.13/5.93  #SimpNegUnit  : 7
% 13.13/5.93  #BackRed      : 20
% 13.13/5.93  
% 13.13/5.93  #Partial instantiations: 0
% 13.13/5.93  #Strategies tried      : 1
% 13.13/5.93  
% 13.13/5.93  Timing (in seconds)
% 13.13/5.93  ----------------------
% 13.13/5.93  Preprocessing        : 0.51
% 13.13/5.93  Parsing              : 0.26
% 13.13/5.93  CNF conversion       : 0.04
% 13.13/5.93  Main loop            : 4.58
% 13.13/5.93  Inferencing          : 0.96
% 13.13/5.93  Reduction            : 2.45
% 13.13/5.93  Demodulation         : 2.12
% 13.13/5.93  BG Simplification    : 0.10
% 13.13/5.93  Subsumption          : 0.83
% 13.13/5.93  Abstraction          : 0.17
% 13.13/5.93  MUC search           : 0.00
% 13.13/5.93  Cooper               : 0.00
% 13.13/5.93  Total                : 5.14
% 13.13/5.93  Index Insertion      : 0.00
% 13.13/5.93  Index Deletion       : 0.00
% 13.13/5.93  Index Matching       : 0.00
% 13.13/5.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
