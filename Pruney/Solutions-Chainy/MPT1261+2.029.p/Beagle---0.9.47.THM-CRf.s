%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:15 EST 2020

% Result     : Theorem 16.21s
% Output     : CNFRefutation 16.44s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 562 expanded)
%              Number of leaves         :   55 ( 208 expanded)
%              Depth                    :   17
%              Number of atoms          :  281 ( 920 expanded)
%              Number of equality atoms :  134 ( 389 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_116,axiom,(
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

tff(f_101,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_87,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_75,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_137,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k2_tops_1(A,k3_subset_1(u1_struct_0(A),B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

tff(f_122,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_151,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_97,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_17897,plain,(
    ! [A_543,B_544,C_545] :
      ( k7_subset_1(A_543,B_544,C_545) = k4_xboole_0(B_544,C_545)
      | ~ m1_subset_1(B_544,k1_zfmisc_1(A_543)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_17919,plain,(
    ! [C_545] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_545) = k4_xboole_0('#skF_2',C_545) ),
    inference(resolution,[status(thm)],[c_68,c_17897])).

tff(c_74,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_212,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_3684,plain,(
    ! [B_245,A_246] :
      ( v4_pre_topc(B_245,A_246)
      | k2_pre_topc(A_246,B_245) != B_245
      | ~ v2_pre_topc(A_246)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_246)))
      | ~ l1_pre_topc(A_246) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3713,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_3684])).

tff(c_3725,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_3713])).

tff(c_3726,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_212,c_3725])).

tff(c_188,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(A_89,B_90)
      | ~ m1_subset_1(A_89,k1_zfmisc_1(B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_206,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_68,c_188])).

tff(c_4218,plain,(
    ! [A_256,B_257] :
      ( k4_subset_1(u1_struct_0(A_256),B_257,k2_tops_1(A_256,B_257)) = k2_pre_topc(A_256,B_257)
      | ~ m1_subset_1(B_257,k1_zfmisc_1(u1_struct_0(A_256)))
      | ~ l1_pre_topc(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_4239,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_4218])).

tff(c_4251,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4239])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [B_27,A_26] : k2_tarski(B_27,A_26) = k2_tarski(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_213,plain,(
    ! [A_93,B_94] : k3_tarski(k2_tarski(A_93,B_94)) = k2_xboole_0(A_93,B_94) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_338,plain,(
    ! [A_103,B_104] : k3_tarski(k2_tarski(A_103,B_104)) = k2_xboole_0(B_104,A_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_213])).

tff(c_28,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_361,plain,(
    ! [B_105,A_106] : k2_xboole_0(B_105,A_106) = k2_xboole_0(A_106,B_105) ),
    inference(superposition,[status(thm),theory(equality)],[c_338,c_28])).

tff(c_408,plain,(
    ! [A_107] : k2_xboole_0(k1_xboole_0,A_107) = A_107 ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_4])).

tff(c_448,plain,(
    ! [B_8] : k3_xboole_0(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_408])).

tff(c_377,plain,(
    ! [A_106] : k2_xboole_0(k1_xboole_0,A_106) = A_106 ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_4])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_575,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k4_xboole_0(B_113,A_112)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_587,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,A_13) = k2_xboole_0(k1_xboole_0,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_575])).

tff(c_592,plain,(
    ! [A_114] : k5_xboole_0(k1_xboole_0,A_114) = A_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_587])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_603,plain,(
    ! [B_2] : k4_xboole_0(k1_xboole_0,B_2) = k3_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_2])).

tff(c_623,plain,(
    ! [B_115] : k4_xboole_0(k1_xboole_0,B_115) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_448,c_603])).

tff(c_24,plain,(
    ! [A_24,B_25] : k5_xboole_0(A_24,k4_xboole_0(B_25,A_24)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_628,plain,(
    ! [B_115] : k5_xboole_0(B_115,k1_xboole_0) = k2_xboole_0(B_115,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_24])).

tff(c_657,plain,(
    ! [B_115] : k5_xboole_0(B_115,k1_xboole_0) = B_115 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_628])).

tff(c_80,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_148,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_1958,plain,(
    ! [A_188,B_189,C_190] :
      ( k7_subset_1(A_188,B_189,C_190) = k4_xboole_0(B_189,C_190)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(A_188)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2059,plain,(
    ! [C_198] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_198) = k4_xboole_0('#skF_2',C_198) ),
    inference(resolution,[status(thm)],[c_68,c_1958])).

tff(c_2071,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_2059])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2892,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2071,c_10])).

tff(c_1665,plain,(
    ! [A_175,B_176,C_177] :
      ( r1_tarski(k4_xboole_0(A_175,B_176),C_177)
      | ~ r1_tarski(A_175,k2_xboole_0(B_176,C_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_635,plain,(
    ! [B_115] :
      ( k1_xboole_0 = B_115
      | ~ r1_tarski(B_115,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_12])).

tff(c_1678,plain,(
    ! [A_175,B_176] :
      ( k4_xboole_0(A_175,B_176) = k1_xboole_0
      | ~ r1_tarski(A_175,k2_xboole_0(B_176,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_1665,c_635])).

tff(c_1708,plain,(
    ! [A_175,B_176] :
      ( k4_xboole_0(A_175,B_176) = k1_xboole_0
      | ~ r1_tarski(A_175,B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1678])).

tff(c_2904,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2892,c_1708])).

tff(c_3598,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2904,c_24])).

tff(c_3620,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_3598])).

tff(c_783,plain,(
    ! [A_123,B_124,C_125] :
      ( r1_tarski(A_123,k2_xboole_0(B_124,C_125))
      | ~ r1_tarski(k4_xboole_0(A_123,B_124),C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_805,plain,(
    ! [A_126,B_127] : r1_tarski(A_126,k2_xboole_0(B_127,A_126)) ),
    inference(resolution,[status(thm)],[c_10,c_783])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(A_4,C_6)
      | ~ r1_tarski(B_5,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_837,plain,(
    ! [A_4,B_127,A_126] :
      ( r1_tarski(A_4,k2_xboole_0(B_127,A_126))
      | ~ r1_tarski(A_4,A_126) ) ),
    inference(resolution,[status(thm)],[c_805,c_6])).

tff(c_20,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k3_xboole_0(A_20,B_21)) = k4_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_9532,plain,(
    ! [A_340,B_341,C_342] :
      ( r1_tarski(k4_xboole_0(A_340,B_341),C_342)
      | ~ r1_tarski(A_340,k2_xboole_0(k3_xboole_0(A_340,B_341),C_342)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1665])).

tff(c_9840,plain,(
    ! [A_347,B_348,A_349] :
      ( r1_tarski(k4_xboole_0(A_347,B_348),A_349)
      | ~ r1_tarski(A_347,A_349) ) ),
    inference(resolution,[status(thm)],[c_837,c_9532])).

tff(c_9950,plain,(
    ! [A_349] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),A_349)
      | ~ r1_tarski('#skF_2',A_349) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2071,c_9840])).

tff(c_52,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(A_51,k1_zfmisc_1(B_52))
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3158,plain,(
    ! [A_235,B_236,C_237] :
      ( k4_subset_1(A_235,B_236,C_237) = k2_xboole_0(B_236,C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(A_235))
      | ~ m1_subset_1(B_236,k1_zfmisc_1(A_235)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_15493,plain,(
    ! [B_427,B_428,A_429] :
      ( k4_subset_1(B_427,B_428,A_429) = k2_xboole_0(B_428,A_429)
      | ~ m1_subset_1(B_428,k1_zfmisc_1(B_427))
      | ~ r1_tarski(A_429,B_427) ) ),
    inference(resolution,[status(thm)],[c_52,c_3158])).

tff(c_15751,plain,(
    ! [A_431] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_431) = k2_xboole_0('#skF_2',A_431)
      | ~ r1_tarski(A_431,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_68,c_15493])).

tff(c_15758,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_9950,c_15751])).

tff(c_15890,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_4251,c_3620,c_15758])).

tff(c_15892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3726,c_15890])).

tff(c_15893,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_16257,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_15893,c_148])).

tff(c_16258,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_16319,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16258,c_74])).

tff(c_18025,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17919,c_16319])).

tff(c_18833,plain,(
    ! [A_576,B_577] :
      ( k2_pre_topc(A_576,B_577) = B_577
      | ~ v4_pre_topc(B_577,A_576)
      | ~ m1_subset_1(B_577,k1_zfmisc_1(u1_struct_0(A_576)))
      | ~ l1_pre_topc(A_576) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_18859,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_18833])).

tff(c_18870,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_16258,c_18859])).

tff(c_20482,plain,(
    ! [A_636,B_637] :
      ( k4_subset_1(u1_struct_0(A_636),B_637,k2_tops_1(A_636,B_637)) = k2_pre_topc(A_636,B_637)
      | ~ m1_subset_1(B_637,k1_zfmisc_1(u1_struct_0(A_636)))
      | ~ l1_pre_topc(A_636) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_20505,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_20482])).

tff(c_20520,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_18870,c_20505])).

tff(c_17197,plain,(
    ! [A_513,B_514] :
      ( k4_xboole_0(A_513,B_514) = k3_subset_1(A_513,B_514)
      | ~ m1_subset_1(B_514,k1_zfmisc_1(A_513)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_17219,plain,(
    k4_xboole_0(u1_struct_0('#skF_1'),'#skF_2') = k3_subset_1(u1_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_17197])).

tff(c_42,plain,(
    ! [A_42,B_43] : k6_subset_1(A_42,B_43) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_36,plain,(
    ! [A_35,B_36] : m1_subset_1(k6_subset_1(A_35,B_36),k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,(
    ! [A_35,B_36] : m1_subset_1(k4_xboole_0(A_35,B_36),k1_zfmisc_1(A_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36])).

tff(c_17266,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_17219,c_81])).

tff(c_20378,plain,(
    ! [A_634,B_635] :
      ( k2_tops_1(A_634,k3_subset_1(u1_struct_0(A_634),B_635)) = k2_tops_1(A_634,B_635)
      | ~ m1_subset_1(B_635,k1_zfmisc_1(u1_struct_0(A_634)))
      | ~ l1_pre_topc(A_634) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_20399,plain,
    ( k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_20378])).

tff(c_20413,plain,(
    k2_tops_1('#skF_1',k3_subset_1(u1_struct_0('#skF_1'),'#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_20399])).

tff(c_58,plain,(
    ! [A_56,B_57] :
      ( m1_subset_1(k2_tops_1(A_56,B_57),k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_20420,plain,
    ( m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_20413,c_58])).

tff(c_20424,plain,(
    m1_subset_1(k2_tops_1('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_17266,c_20420])).

tff(c_50,plain,(
    ! [A_51,B_52] :
      ( r1_tarski(A_51,B_52)
      | ~ m1_subset_1(A_51,k1_zfmisc_1(B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_20472,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20424,c_50])).

tff(c_19699,plain,(
    ! [A_606,B_607,C_608] :
      ( k4_subset_1(A_606,B_607,C_608) = k2_xboole_0(B_607,C_608)
      | ~ m1_subset_1(C_608,k1_zfmisc_1(A_606))
      | ~ m1_subset_1(B_607,k1_zfmisc_1(A_606)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_34554,plain,(
    ! [B_830,B_831,A_832] :
      ( k4_subset_1(B_830,B_831,A_832) = k2_xboole_0(B_831,A_832)
      | ~ m1_subset_1(B_831,k1_zfmisc_1(B_830))
      | ~ r1_tarski(A_832,B_830) ) ),
    inference(resolution,[status(thm)],[c_52,c_19699])).

tff(c_35199,plain,(
    ! [A_837] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_837) = k2_xboole_0('#skF_2',A_837)
      | ~ r1_tarski(A_837,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_68,c_34554])).

tff(c_35247,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20472,c_35199])).

tff(c_35347,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20520,c_35247])).

tff(c_17630,plain,(
    ! [A_532,B_533,C_534] :
      ( r1_tarski(A_532,k2_xboole_0(B_533,C_534))
      | ~ r1_tarski(k4_xboole_0(A_532,B_533),C_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_17681,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(B_10,A_9)) ),
    inference(resolution,[status(thm)],[c_10,c_17630])).

tff(c_35461,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35347,c_17681])).

tff(c_20665,plain,(
    ! [A_641,B_642] :
      ( k7_subset_1(u1_struct_0(A_641),B_642,k2_tops_1(A_641,B_642)) = k1_tops_1(A_641,B_642)
      | ~ m1_subset_1(B_642,k1_zfmisc_1(u1_struct_0(A_641)))
      | ~ l1_pre_topc(A_641) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_20688,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_20665])).

tff(c_20705,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_17919,c_20688])).

tff(c_17215,plain,(
    ! [B_52,A_51] :
      ( k4_xboole_0(B_52,A_51) = k3_subset_1(B_52,A_51)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_52,c_17197])).

tff(c_35490,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_35461,c_17215])).

tff(c_35498,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20705,c_35490])).

tff(c_16891,plain,(
    ! [A_496,B_497] :
      ( k3_subset_1(A_496,k3_subset_1(A_496,B_497)) = B_497
      | ~ m1_subset_1(B_497,k1_zfmisc_1(A_496)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16900,plain,(
    ! [B_52,A_51] :
      ( k3_subset_1(B_52,k3_subset_1(B_52,A_51)) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_52,c_16891])).

tff(c_36845,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35498,c_16900])).

tff(c_36862,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35461,c_36845])).

tff(c_110,plain,(
    ! [A_73,B_74] : r1_tarski(k4_xboole_0(A_73,B_74),A_73) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_13] : r1_tarski(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_110])).

tff(c_16938,plain,(
    ! [A_501,B_502,C_503] :
      ( r1_tarski(k4_xboole_0(A_501,B_502),C_503)
      | ~ r1_tarski(A_501,k2_xboole_0(B_502,C_503)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16325,plain,(
    ! [A_466,B_467] : k3_tarski(k2_tarski(A_466,B_467)) = k2_xboole_0(A_466,B_467) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16446,plain,(
    ! [A_476,B_477] : k3_tarski(k2_tarski(A_476,B_477)) = k2_xboole_0(B_477,A_476) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_16325])).

tff(c_16469,plain,(
    ! [B_478,A_479] : k2_xboole_0(B_478,A_479) = k2_xboole_0(A_479,B_478) ),
    inference(superposition,[status(thm),theory(equality)],[c_16446,c_28])).

tff(c_16516,plain,(
    ! [A_480] : k2_xboole_0(k1_xboole_0,A_480) = A_480 ),
    inference(superposition,[status(thm),theory(equality)],[c_16469,c_4])).

tff(c_16556,plain,(
    ! [B_8] : k3_xboole_0(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_16516])).

tff(c_16485,plain,(
    ! [A_479] : k2_xboole_0(k1_xboole_0,A_479) = A_479 ),
    inference(superposition,[status(thm),theory(equality)],[c_16469,c_4])).

tff(c_16683,plain,(
    ! [A_485,B_486] : k5_xboole_0(A_485,k4_xboole_0(B_486,A_485)) = k2_xboole_0(A_485,B_486) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16695,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,A_13) = k2_xboole_0(k1_xboole_0,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_16683])).

tff(c_16700,plain,(
    ! [A_487] : k5_xboole_0(k1_xboole_0,A_487) = A_487 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16485,c_16695])).

tff(c_16711,plain,(
    ! [B_2] : k4_xboole_0(k1_xboole_0,B_2) = k3_xboole_0(k1_xboole_0,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_16700,c_2])).

tff(c_16731,plain,(
    ! [B_488] : k4_xboole_0(k1_xboole_0,B_488) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16556,c_16711])).

tff(c_16743,plain,(
    ! [B_488] :
      ( k1_xboole_0 = B_488
      | ~ r1_tarski(B_488,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16731,c_12])).

tff(c_16942,plain,(
    ! [A_501,B_502] :
      ( k4_xboole_0(A_501,B_502) = k1_xboole_0
      | ~ r1_tarski(A_501,k2_xboole_0(B_502,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_16938,c_16743])).

tff(c_16963,plain,(
    ! [A_504,B_505] :
      ( k4_xboole_0(A_504,B_505) = k1_xboole_0
      | ~ r1_tarski(A_504,B_505) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16942])).

tff(c_16982,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_113,c_16963])).

tff(c_16278,plain,(
    ! [A_455,B_456] : m1_subset_1(k4_xboole_0(A_455,B_456),k1_zfmisc_1(A_455)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36])).

tff(c_16281,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_16278])).

tff(c_17206,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k3_subset_1(A_13,A_13) ),
    inference(resolution,[status(thm)],[c_16281,c_17197])).

tff(c_17217,plain,(
    ! [A_13] : k3_subset_1(A_13,A_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16982,c_17206])).

tff(c_16901,plain,(
    ! [A_13] : k3_subset_1(A_13,k3_subset_1(A_13,A_13)) = A_13 ),
    inference(resolution,[status(thm)],[c_16281,c_16891])).

tff(c_17220,plain,(
    ! [A_13] : k3_subset_1(A_13,k1_xboole_0) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17217,c_16901])).

tff(c_20766,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20705,c_10])).

tff(c_16959,plain,(
    ! [A_501,B_502] :
      ( k4_xboole_0(A_501,B_502) = k1_xboole_0
      | ~ r1_tarski(A_501,B_502) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_16942])).

tff(c_20777,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20766,c_16959])).

tff(c_17683,plain,(
    ! [A_535,B_536] : r1_tarski(A_535,k2_xboole_0(B_536,A_535)) ),
    inference(resolution,[status(thm)],[c_10,c_17630])).

tff(c_17719,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_17683])).

tff(c_21258,plain,(
    ! [B_655,A_656] :
      ( k4_xboole_0(B_655,A_656) = k3_subset_1(B_655,A_656)
      | ~ r1_tarski(A_656,B_655) ) ),
    inference(resolution,[status(thm)],[c_52,c_17197])).

tff(c_21378,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_subset_1(A_7,k3_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_17719,c_21258])).

tff(c_25347,plain,(
    ! [A_708,B_709] : k3_subset_1(A_708,k3_xboole_0(A_708,B_709)) = k4_xboole_0(A_708,B_709) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_21378])).

tff(c_25359,plain,(
    ! [A_708,B_709] :
      ( k3_subset_1(A_708,k4_xboole_0(A_708,B_709)) = k3_xboole_0(A_708,B_709)
      | ~ r1_tarski(k3_xboole_0(A_708,B_709),A_708) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25347,c_16900])).

tff(c_26217,plain,(
    ! [A_722,B_723] : k3_subset_1(A_722,k4_xboole_0(A_722,B_723)) = k3_xboole_0(A_722,B_723) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17719,c_25359])).

tff(c_26265,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20777,c_26217])).

tff(c_26326,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17220,c_26265])).

tff(c_16283,plain,(
    ! [A_458,B_459] : k1_setfam_1(k2_tarski(A_458,B_459)) = k3_xboole_0(A_458,B_459) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16340,plain,(
    ! [A_468,B_469] : k1_setfam_1(k2_tarski(A_468,B_469)) = k3_xboole_0(B_469,A_468) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_16283])).

tff(c_48,plain,(
    ! [A_49,B_50] : k1_setfam_1(k2_tarski(A_49,B_50)) = k3_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_16346,plain,(
    ! [B_469,A_468] : k3_xboole_0(B_469,A_468) = k3_xboole_0(A_468,B_469) ),
    inference(superposition,[status(thm),theory(equality)],[c_16340,c_48])).

tff(c_25392,plain,(
    ! [A_468,B_469] : k3_subset_1(A_468,k3_xboole_0(B_469,A_468)) = k4_xboole_0(A_468,B_469) ),
    inference(superposition,[status(thm),theory(equality)],[c_16346,c_25347])).

tff(c_68065,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26326,c_25392])).

tff(c_68206,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36862,c_68065])).

tff(c_68208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18025,c_68206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:45:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.21/8.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.21/8.85  
% 16.21/8.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.21/8.85  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 16.21/8.85  
% 16.21/8.85  %Foreground sorts:
% 16.21/8.85  
% 16.21/8.85  
% 16.21/8.85  %Background operators:
% 16.21/8.85  
% 16.21/8.85  
% 16.21/8.85  %Foreground operators:
% 16.21/8.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.21/8.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.21/8.85  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 16.21/8.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.21/8.85  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 16.21/8.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 16.21/8.85  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.21/8.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.21/8.85  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 16.21/8.85  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 16.21/8.85  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 16.21/8.85  tff('#skF_2', type, '#skF_2': $i).
% 16.21/8.85  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 16.21/8.85  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 16.21/8.85  tff('#skF_1', type, '#skF_1': $i).
% 16.21/8.85  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.21/8.85  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 16.21/8.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.21/8.85  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.21/8.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.21/8.85  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 16.21/8.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 16.21/8.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.21/8.85  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 16.21/8.85  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 16.21/8.85  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 16.21/8.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.21/8.85  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 16.21/8.85  
% 16.44/8.88  tff(f_163, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 16.44/8.88  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 16.44/8.88  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 16.44/8.88  tff(f_101, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.44/8.88  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 16.44/8.88  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 16.44/8.88  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 16.44/8.88  tff(f_61, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 16.44/8.88  tff(f_63, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 16.44/8.88  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 16.44/8.88  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 16.44/8.88  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 16.44/8.88  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 16.44/8.88  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 16.44/8.88  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 16.44/8.88  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 16.44/8.88  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 16.44/8.88  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 16.44/8.88  tff(f_85, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 16.44/8.88  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 16.44/8.88  tff(f_87, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 16.44/8.88  tff(f_75, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 16.44/8.88  tff(f_137, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k2_tops_1(A, k3_subset_1(u1_struct_0(A), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_tops_1)).
% 16.44/8.88  tff(f_122, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 16.44/8.88  tff(f_151, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 16.44/8.88  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 16.44/8.88  tff(f_97, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 16.44/8.88  tff(c_68, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.44/8.88  tff(c_17897, plain, (![A_543, B_544, C_545]: (k7_subset_1(A_543, B_544, C_545)=k4_xboole_0(B_544, C_545) | ~m1_subset_1(B_544, k1_zfmisc_1(A_543)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.44/8.88  tff(c_17919, plain, (![C_545]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_545)=k4_xboole_0('#skF_2', C_545))), inference(resolution, [status(thm)], [c_68, c_17897])).
% 16.44/8.88  tff(c_74, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.44/8.88  tff(c_212, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_74])).
% 16.44/8.88  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.44/8.88  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.44/8.88  tff(c_3684, plain, (![B_245, A_246]: (v4_pre_topc(B_245, A_246) | k2_pre_topc(A_246, B_245)!=B_245 | ~v2_pre_topc(A_246) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_246))) | ~l1_pre_topc(A_246))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.44/8.88  tff(c_3713, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_3684])).
% 16.44/8.88  tff(c_3725, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_3713])).
% 16.44/8.88  tff(c_3726, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_212, c_3725])).
% 16.44/8.88  tff(c_188, plain, (![A_89, B_90]: (r1_tarski(A_89, B_90) | ~m1_subset_1(A_89, k1_zfmisc_1(B_90)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.44/8.88  tff(c_206, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_68, c_188])).
% 16.44/8.88  tff(c_4218, plain, (![A_256, B_257]: (k4_subset_1(u1_struct_0(A_256), B_257, k2_tops_1(A_256, B_257))=k2_pre_topc(A_256, B_257) | ~m1_subset_1(B_257, k1_zfmisc_1(u1_struct_0(A_256))) | ~l1_pre_topc(A_256))), inference(cnfTransformation, [status(thm)], [f_144])).
% 16.44/8.88  tff(c_4239, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_4218])).
% 16.44/8.88  tff(c_4251, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4239])).
% 16.44/8.88  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 16.44/8.88  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 16.44/8.88  tff(c_26, plain, (![B_27, A_26]: (k2_tarski(B_27, A_26)=k2_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.44/8.88  tff(c_213, plain, (![A_93, B_94]: (k3_tarski(k2_tarski(A_93, B_94))=k2_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.44/8.88  tff(c_338, plain, (![A_103, B_104]: (k3_tarski(k2_tarski(A_103, B_104))=k2_xboole_0(B_104, A_103))), inference(superposition, [status(thm), theory('equality')], [c_26, c_213])).
% 16.44/8.88  tff(c_28, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.44/8.88  tff(c_361, plain, (![B_105, A_106]: (k2_xboole_0(B_105, A_106)=k2_xboole_0(A_106, B_105))), inference(superposition, [status(thm), theory('equality')], [c_338, c_28])).
% 16.44/8.88  tff(c_408, plain, (![A_107]: (k2_xboole_0(k1_xboole_0, A_107)=A_107)), inference(superposition, [status(thm), theory('equality')], [c_361, c_4])).
% 16.44/8.88  tff(c_448, plain, (![B_8]: (k3_xboole_0(k1_xboole_0, B_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_408])).
% 16.44/8.88  tff(c_377, plain, (![A_106]: (k2_xboole_0(k1_xboole_0, A_106)=A_106)), inference(superposition, [status(thm), theory('equality')], [c_361, c_4])).
% 16.44/8.88  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_45])).
% 16.44/8.88  tff(c_575, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k4_xboole_0(B_113, A_112))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.44/8.88  tff(c_587, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, A_13)=k2_xboole_0(k1_xboole_0, A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_575])).
% 16.44/8.88  tff(c_592, plain, (![A_114]: (k5_xboole_0(k1_xboole_0, A_114)=A_114)), inference(demodulation, [status(thm), theory('equality')], [c_377, c_587])).
% 16.44/8.88  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 16.44/8.88  tff(c_603, plain, (![B_2]: (k4_xboole_0(k1_xboole_0, B_2)=k3_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_592, c_2])).
% 16.44/8.88  tff(c_623, plain, (![B_115]: (k4_xboole_0(k1_xboole_0, B_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_448, c_603])).
% 16.44/8.88  tff(c_24, plain, (![A_24, B_25]: (k5_xboole_0(A_24, k4_xboole_0(B_25, A_24))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.44/8.88  tff(c_628, plain, (![B_115]: (k5_xboole_0(B_115, k1_xboole_0)=k2_xboole_0(B_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_623, c_24])).
% 16.44/8.88  tff(c_657, plain, (![B_115]: (k5_xboole_0(B_115, k1_xboole_0)=B_115)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_628])).
% 16.44/8.88  tff(c_80, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 16.44/8.88  tff(c_148, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_80])).
% 16.44/8.88  tff(c_1958, plain, (![A_188, B_189, C_190]: (k7_subset_1(A_188, B_189, C_190)=k4_xboole_0(B_189, C_190) | ~m1_subset_1(B_189, k1_zfmisc_1(A_188)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.44/8.88  tff(c_2059, plain, (![C_198]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_198)=k4_xboole_0('#skF_2', C_198))), inference(resolution, [status(thm)], [c_68, c_1958])).
% 16.44/8.88  tff(c_2071, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_148, c_2059])).
% 16.44/8.88  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.44/8.88  tff(c_2892, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2071, c_10])).
% 16.44/8.88  tff(c_1665, plain, (![A_175, B_176, C_177]: (r1_tarski(k4_xboole_0(A_175, B_176), C_177) | ~r1_tarski(A_175, k2_xboole_0(B_176, C_177)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.44/8.88  tff(c_12, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.44/8.88  tff(c_635, plain, (![B_115]: (k1_xboole_0=B_115 | ~r1_tarski(B_115, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_623, c_12])).
% 16.44/8.88  tff(c_1678, plain, (![A_175, B_176]: (k4_xboole_0(A_175, B_176)=k1_xboole_0 | ~r1_tarski(A_175, k2_xboole_0(B_176, k1_xboole_0)))), inference(resolution, [status(thm)], [c_1665, c_635])).
% 16.44/8.88  tff(c_1708, plain, (![A_175, B_176]: (k4_xboole_0(A_175, B_176)=k1_xboole_0 | ~r1_tarski(A_175, B_176))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1678])).
% 16.44/8.88  tff(c_2904, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2892, c_1708])).
% 16.44/8.88  tff(c_3598, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2904, c_24])).
% 16.44/8.88  tff(c_3620, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_657, c_3598])).
% 16.44/8.88  tff(c_783, plain, (![A_123, B_124, C_125]: (r1_tarski(A_123, k2_xboole_0(B_124, C_125)) | ~r1_tarski(k4_xboole_0(A_123, B_124), C_125))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.44/8.88  tff(c_805, plain, (![A_126, B_127]: (r1_tarski(A_126, k2_xboole_0(B_127, A_126)))), inference(resolution, [status(thm)], [c_10, c_783])).
% 16.44/8.88  tff(c_6, plain, (![A_4, C_6, B_5]: (r1_tarski(A_4, C_6) | ~r1_tarski(B_5, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 16.44/8.88  tff(c_837, plain, (![A_4, B_127, A_126]: (r1_tarski(A_4, k2_xboole_0(B_127, A_126)) | ~r1_tarski(A_4, A_126))), inference(resolution, [status(thm)], [c_805, c_6])).
% 16.44/8.88  tff(c_20, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k3_xboole_0(A_20, B_21))=k4_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 16.44/8.88  tff(c_9532, plain, (![A_340, B_341, C_342]: (r1_tarski(k4_xboole_0(A_340, B_341), C_342) | ~r1_tarski(A_340, k2_xboole_0(k3_xboole_0(A_340, B_341), C_342)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1665])).
% 16.44/8.88  tff(c_9840, plain, (![A_347, B_348, A_349]: (r1_tarski(k4_xboole_0(A_347, B_348), A_349) | ~r1_tarski(A_347, A_349))), inference(resolution, [status(thm)], [c_837, c_9532])).
% 16.44/8.88  tff(c_9950, plain, (![A_349]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), A_349) | ~r1_tarski('#skF_2', A_349))), inference(superposition, [status(thm), theory('equality')], [c_2071, c_9840])).
% 16.44/8.88  tff(c_52, plain, (![A_51, B_52]: (m1_subset_1(A_51, k1_zfmisc_1(B_52)) | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.44/8.88  tff(c_3158, plain, (![A_235, B_236, C_237]: (k4_subset_1(A_235, B_236, C_237)=k2_xboole_0(B_236, C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(A_235)) | ~m1_subset_1(B_236, k1_zfmisc_1(A_235)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 16.44/8.88  tff(c_15493, plain, (![B_427, B_428, A_429]: (k4_subset_1(B_427, B_428, A_429)=k2_xboole_0(B_428, A_429) | ~m1_subset_1(B_428, k1_zfmisc_1(B_427)) | ~r1_tarski(A_429, B_427))), inference(resolution, [status(thm)], [c_52, c_3158])).
% 16.44/8.88  tff(c_15751, plain, (![A_431]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_431)=k2_xboole_0('#skF_2', A_431) | ~r1_tarski(A_431, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_68, c_15493])).
% 16.44/8.88  tff(c_15758, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_9950, c_15751])).
% 16.44/8.88  tff(c_15890, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_206, c_4251, c_3620, c_15758])).
% 16.44/8.88  tff(c_15892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3726, c_15890])).
% 16.44/8.88  tff(c_15893, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_74])).
% 16.44/8.88  tff(c_16257, plain, $false, inference(negUnitSimplification, [status(thm)], [c_15893, c_148])).
% 16.44/8.88  tff(c_16258, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_80])).
% 16.44/8.88  tff(c_16319, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16258, c_74])).
% 16.44/8.88  tff(c_18025, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17919, c_16319])).
% 16.44/8.88  tff(c_18833, plain, (![A_576, B_577]: (k2_pre_topc(A_576, B_577)=B_577 | ~v4_pre_topc(B_577, A_576) | ~m1_subset_1(B_577, k1_zfmisc_1(u1_struct_0(A_576))) | ~l1_pre_topc(A_576))), inference(cnfTransformation, [status(thm)], [f_116])).
% 16.44/8.88  tff(c_18859, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_18833])).
% 16.44/8.88  tff(c_18870, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_16258, c_18859])).
% 16.44/8.88  tff(c_20482, plain, (![A_636, B_637]: (k4_subset_1(u1_struct_0(A_636), B_637, k2_tops_1(A_636, B_637))=k2_pre_topc(A_636, B_637) | ~m1_subset_1(B_637, k1_zfmisc_1(u1_struct_0(A_636))) | ~l1_pre_topc(A_636))), inference(cnfTransformation, [status(thm)], [f_144])).
% 16.44/8.88  tff(c_20505, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_20482])).
% 16.44/8.88  tff(c_20520, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_18870, c_20505])).
% 16.44/8.88  tff(c_17197, plain, (![A_513, B_514]: (k4_xboole_0(A_513, B_514)=k3_subset_1(A_513, B_514) | ~m1_subset_1(B_514, k1_zfmisc_1(A_513)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.44/8.88  tff(c_17219, plain, (k4_xboole_0(u1_struct_0('#skF_1'), '#skF_2')=k3_subset_1(u1_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_68, c_17197])).
% 16.44/8.88  tff(c_42, plain, (![A_42, B_43]: (k6_subset_1(A_42, B_43)=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.44/8.88  tff(c_36, plain, (![A_35, B_36]: (m1_subset_1(k6_subset_1(A_35, B_36), k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.44/8.88  tff(c_81, plain, (![A_35, B_36]: (m1_subset_1(k4_xboole_0(A_35, B_36), k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36])).
% 16.44/8.88  tff(c_17266, plain, (m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_17219, c_81])).
% 16.44/8.88  tff(c_20378, plain, (![A_634, B_635]: (k2_tops_1(A_634, k3_subset_1(u1_struct_0(A_634), B_635))=k2_tops_1(A_634, B_635) | ~m1_subset_1(B_635, k1_zfmisc_1(u1_struct_0(A_634))) | ~l1_pre_topc(A_634))), inference(cnfTransformation, [status(thm)], [f_137])).
% 16.44/8.88  tff(c_20399, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_20378])).
% 16.44/8.88  tff(c_20413, plain, (k2_tops_1('#skF_1', k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_20399])).
% 16.44/8.88  tff(c_58, plain, (![A_56, B_57]: (m1_subset_1(k2_tops_1(A_56, B_57), k1_zfmisc_1(u1_struct_0(A_56))) | ~m1_subset_1(B_57, k1_zfmisc_1(u1_struct_0(A_56))) | ~l1_pre_topc(A_56))), inference(cnfTransformation, [status(thm)], [f_122])).
% 16.44/8.88  tff(c_20420, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k3_subset_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_20413, c_58])).
% 16.44/8.88  tff(c_20424, plain, (m1_subset_1(k2_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_17266, c_20420])).
% 16.44/8.88  tff(c_50, plain, (![A_51, B_52]: (r1_tarski(A_51, B_52) | ~m1_subset_1(A_51, k1_zfmisc_1(B_52)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 16.44/8.88  tff(c_20472, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_20424, c_50])).
% 16.44/8.88  tff(c_19699, plain, (![A_606, B_607, C_608]: (k4_subset_1(A_606, B_607, C_608)=k2_xboole_0(B_607, C_608) | ~m1_subset_1(C_608, k1_zfmisc_1(A_606)) | ~m1_subset_1(B_607, k1_zfmisc_1(A_606)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 16.44/8.88  tff(c_34554, plain, (![B_830, B_831, A_832]: (k4_subset_1(B_830, B_831, A_832)=k2_xboole_0(B_831, A_832) | ~m1_subset_1(B_831, k1_zfmisc_1(B_830)) | ~r1_tarski(A_832, B_830))), inference(resolution, [status(thm)], [c_52, c_19699])).
% 16.44/8.88  tff(c_35199, plain, (![A_837]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_837)=k2_xboole_0('#skF_2', A_837) | ~r1_tarski(A_837, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_68, c_34554])).
% 16.44/8.88  tff(c_35247, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20472, c_35199])).
% 16.44/8.88  tff(c_35347, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20520, c_35247])).
% 16.44/8.88  tff(c_17630, plain, (![A_532, B_533, C_534]: (r1_tarski(A_532, k2_xboole_0(B_533, C_534)) | ~r1_tarski(k4_xboole_0(A_532, B_533), C_534))), inference(cnfTransformation, [status(thm)], [f_53])).
% 16.44/8.88  tff(c_17681, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(B_10, A_9)))), inference(resolution, [status(thm)], [c_10, c_17630])).
% 16.44/8.88  tff(c_35461, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35347, c_17681])).
% 16.44/8.88  tff(c_20665, plain, (![A_641, B_642]: (k7_subset_1(u1_struct_0(A_641), B_642, k2_tops_1(A_641, B_642))=k1_tops_1(A_641, B_642) | ~m1_subset_1(B_642, k1_zfmisc_1(u1_struct_0(A_641))) | ~l1_pre_topc(A_641))), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.44/8.88  tff(c_20688, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_20665])).
% 16.44/8.88  tff(c_20705, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_17919, c_20688])).
% 16.44/8.88  tff(c_17215, plain, (![B_52, A_51]: (k4_xboole_0(B_52, A_51)=k3_subset_1(B_52, A_51) | ~r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_52, c_17197])).
% 16.44/8.88  tff(c_35490, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_35461, c_17215])).
% 16.44/8.88  tff(c_35498, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20705, c_35490])).
% 16.44/8.88  tff(c_16891, plain, (![A_496, B_497]: (k3_subset_1(A_496, k3_subset_1(A_496, B_497))=B_497 | ~m1_subset_1(B_497, k1_zfmisc_1(A_496)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 16.44/8.88  tff(c_16900, plain, (![B_52, A_51]: (k3_subset_1(B_52, k3_subset_1(B_52, A_51))=A_51 | ~r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_52, c_16891])).
% 16.44/8.88  tff(c_36845, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35498, c_16900])).
% 16.44/8.88  tff(c_36862, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35461, c_36845])).
% 16.44/8.88  tff(c_110, plain, (![A_73, B_74]: (r1_tarski(k4_xboole_0(A_73, B_74), A_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.44/8.88  tff(c_113, plain, (![A_13]: (r1_tarski(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_110])).
% 16.44/8.88  tff(c_16938, plain, (![A_501, B_502, C_503]: (r1_tarski(k4_xboole_0(A_501, B_502), C_503) | ~r1_tarski(A_501, k2_xboole_0(B_502, C_503)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.44/8.88  tff(c_16325, plain, (![A_466, B_467]: (k3_tarski(k2_tarski(A_466, B_467))=k2_xboole_0(A_466, B_467))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.44/8.88  tff(c_16446, plain, (![A_476, B_477]: (k3_tarski(k2_tarski(A_476, B_477))=k2_xboole_0(B_477, A_476))), inference(superposition, [status(thm), theory('equality')], [c_26, c_16325])).
% 16.44/8.88  tff(c_16469, plain, (![B_478, A_479]: (k2_xboole_0(B_478, A_479)=k2_xboole_0(A_479, B_478))), inference(superposition, [status(thm), theory('equality')], [c_16446, c_28])).
% 16.44/8.88  tff(c_16516, plain, (![A_480]: (k2_xboole_0(k1_xboole_0, A_480)=A_480)), inference(superposition, [status(thm), theory('equality')], [c_16469, c_4])).
% 16.44/8.88  tff(c_16556, plain, (![B_8]: (k3_xboole_0(k1_xboole_0, B_8)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_16516])).
% 16.44/8.88  tff(c_16485, plain, (![A_479]: (k2_xboole_0(k1_xboole_0, A_479)=A_479)), inference(superposition, [status(thm), theory('equality')], [c_16469, c_4])).
% 16.44/8.88  tff(c_16683, plain, (![A_485, B_486]: (k5_xboole_0(A_485, k4_xboole_0(B_486, A_485))=k2_xboole_0(A_485, B_486))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.44/8.88  tff(c_16695, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, A_13)=k2_xboole_0(k1_xboole_0, A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_16683])).
% 16.44/8.88  tff(c_16700, plain, (![A_487]: (k5_xboole_0(k1_xboole_0, A_487)=A_487)), inference(demodulation, [status(thm), theory('equality')], [c_16485, c_16695])).
% 16.44/8.88  tff(c_16711, plain, (![B_2]: (k4_xboole_0(k1_xboole_0, B_2)=k3_xboole_0(k1_xboole_0, B_2))), inference(superposition, [status(thm), theory('equality')], [c_16700, c_2])).
% 16.44/8.88  tff(c_16731, plain, (![B_488]: (k4_xboole_0(k1_xboole_0, B_488)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16556, c_16711])).
% 16.44/8.88  tff(c_16743, plain, (![B_488]: (k1_xboole_0=B_488 | ~r1_tarski(B_488, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16731, c_12])).
% 16.44/8.88  tff(c_16942, plain, (![A_501, B_502]: (k4_xboole_0(A_501, B_502)=k1_xboole_0 | ~r1_tarski(A_501, k2_xboole_0(B_502, k1_xboole_0)))), inference(resolution, [status(thm)], [c_16938, c_16743])).
% 16.44/8.88  tff(c_16963, plain, (![A_504, B_505]: (k4_xboole_0(A_504, B_505)=k1_xboole_0 | ~r1_tarski(A_504, B_505))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16942])).
% 16.44/8.88  tff(c_16982, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_113, c_16963])).
% 16.44/8.88  tff(c_16278, plain, (![A_455, B_456]: (m1_subset_1(k4_xboole_0(A_455, B_456), k1_zfmisc_1(A_455)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36])).
% 16.44/8.88  tff(c_16281, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_16278])).
% 16.44/8.88  tff(c_17206, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k3_subset_1(A_13, A_13))), inference(resolution, [status(thm)], [c_16281, c_17197])).
% 16.44/8.88  tff(c_17217, plain, (![A_13]: (k3_subset_1(A_13, A_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16982, c_17206])).
% 16.44/8.88  tff(c_16901, plain, (![A_13]: (k3_subset_1(A_13, k3_subset_1(A_13, A_13))=A_13)), inference(resolution, [status(thm)], [c_16281, c_16891])).
% 16.44/8.88  tff(c_17220, plain, (![A_13]: (k3_subset_1(A_13, k1_xboole_0)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_17217, c_16901])).
% 16.44/8.88  tff(c_20766, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20705, c_10])).
% 16.44/8.88  tff(c_16959, plain, (![A_501, B_502]: (k4_xboole_0(A_501, B_502)=k1_xboole_0 | ~r1_tarski(A_501, B_502))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_16942])).
% 16.44/8.88  tff(c_20777, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20766, c_16959])).
% 16.44/8.88  tff(c_17683, plain, (![A_535, B_536]: (r1_tarski(A_535, k2_xboole_0(B_536, A_535)))), inference(resolution, [status(thm)], [c_10, c_17630])).
% 16.44/8.88  tff(c_17719, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_17683])).
% 16.44/8.88  tff(c_21258, plain, (![B_655, A_656]: (k4_xboole_0(B_655, A_656)=k3_subset_1(B_655, A_656) | ~r1_tarski(A_656, B_655))), inference(resolution, [status(thm)], [c_52, c_17197])).
% 16.44/8.88  tff(c_21378, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_subset_1(A_7, k3_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_17719, c_21258])).
% 16.44/8.88  tff(c_25347, plain, (![A_708, B_709]: (k3_subset_1(A_708, k3_xboole_0(A_708, B_709))=k4_xboole_0(A_708, B_709))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_21378])).
% 16.44/8.88  tff(c_25359, plain, (![A_708, B_709]: (k3_subset_1(A_708, k4_xboole_0(A_708, B_709))=k3_xboole_0(A_708, B_709) | ~r1_tarski(k3_xboole_0(A_708, B_709), A_708))), inference(superposition, [status(thm), theory('equality')], [c_25347, c_16900])).
% 16.44/8.88  tff(c_26217, plain, (![A_722, B_723]: (k3_subset_1(A_722, k4_xboole_0(A_722, B_723))=k3_xboole_0(A_722, B_723))), inference(demodulation, [status(thm), theory('equality')], [c_17719, c_25359])).
% 16.44/8.88  tff(c_26265, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20777, c_26217])).
% 16.44/8.88  tff(c_26326, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_17220, c_26265])).
% 16.44/8.88  tff(c_16283, plain, (![A_458, B_459]: (k1_setfam_1(k2_tarski(A_458, B_459))=k3_xboole_0(A_458, B_459))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.44/8.88  tff(c_16340, plain, (![A_468, B_469]: (k1_setfam_1(k2_tarski(A_468, B_469))=k3_xboole_0(B_469, A_468))), inference(superposition, [status(thm), theory('equality')], [c_26, c_16283])).
% 16.44/8.88  tff(c_48, plain, (![A_49, B_50]: (k1_setfam_1(k2_tarski(A_49, B_50))=k3_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_97])).
% 16.44/8.88  tff(c_16346, plain, (![B_469, A_468]: (k3_xboole_0(B_469, A_468)=k3_xboole_0(A_468, B_469))), inference(superposition, [status(thm), theory('equality')], [c_16340, c_48])).
% 16.44/8.88  tff(c_25392, plain, (![A_468, B_469]: (k3_subset_1(A_468, k3_xboole_0(B_469, A_468))=k4_xboole_0(A_468, B_469))), inference(superposition, [status(thm), theory('equality')], [c_16346, c_25347])).
% 16.44/8.88  tff(c_68065, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_26326, c_25392])).
% 16.44/8.88  tff(c_68206, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36862, c_68065])).
% 16.44/8.88  tff(c_68208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18025, c_68206])).
% 16.44/8.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.44/8.88  
% 16.44/8.88  Inference rules
% 16.44/8.88  ----------------------
% 16.44/8.88  #Ref     : 0
% 16.44/8.88  #Sup     : 16630
% 16.44/8.88  #Fact    : 0
% 16.44/8.88  #Define  : 0
% 16.44/8.88  #Split   : 9
% 16.44/8.88  #Chain   : 0
% 16.44/8.88  #Close   : 0
% 16.44/8.88  
% 16.44/8.88  Ordering : KBO
% 16.44/8.88  
% 16.44/8.88  Simplification rules
% 16.44/8.88  ----------------------
% 16.44/8.88  #Subsume      : 767
% 16.44/8.88  #Demod        : 16074
% 16.44/8.88  #Tautology    : 11262
% 16.44/8.88  #SimpNegUnit  : 5
% 16.44/8.88  #BackRed      : 30
% 16.44/8.88  
% 16.44/8.88  #Partial instantiations: 0
% 16.44/8.88  #Strategies tried      : 1
% 16.44/8.88  
% 16.44/8.88  Timing (in seconds)
% 16.44/8.88  ----------------------
% 16.44/8.88  Preprocessing        : 0.39
% 16.44/8.88  Parsing              : 0.21
% 16.44/8.88  CNF conversion       : 0.03
% 16.44/8.88  Main loop            : 7.65
% 16.44/8.88  Inferencing          : 1.21
% 16.44/8.88  Reduction            : 4.39
% 16.44/8.88  Demodulation         : 3.85
% 16.44/8.88  BG Simplification    : 0.12
% 16.44/8.88  Subsumption          : 1.56
% 16.44/8.88  Abstraction          : 0.21
% 16.44/8.88  MUC search           : 0.00
% 16.44/8.88  Cooper               : 0.00
% 16.44/8.88  Total                : 8.09
% 16.44/8.88  Index Insertion      : 0.00
% 16.44/8.88  Index Deletion       : 0.00
% 16.44/8.88  Index Matching       : 0.00
% 16.44/8.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
