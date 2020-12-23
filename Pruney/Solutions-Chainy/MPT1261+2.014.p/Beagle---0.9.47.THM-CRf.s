%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:13 EST 2020

% Result     : Theorem 6.07s
% Output     : CNFRefutation 6.07s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 239 expanded)
%              Number of leaves         :   42 (  98 expanded)
%              Depth                    :   14
%              Number of atoms          :  158 ( 444 expanded)
%              Number of equality atoms :   88 ( 182 expanded)
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

tff(f_125,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6792,plain,(
    ! [A_264,B_265,C_266] :
      ( k7_subset_1(A_264,B_265,C_266) = k4_xboole_0(B_265,C_266)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(A_264)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6795,plain,(
    ! [C_266] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_266) = k4_xboole_0('#skF_2',C_266) ),
    inference(resolution,[status(thm)],[c_48,c_6792])).

tff(c_7828,plain,(
    ! [A_313,B_314] :
      ( k7_subset_1(u1_struct_0(A_313),B_314,k2_tops_1(A_313,B_314)) = k1_tops_1(A_313,B_314)
      | ~ m1_subset_1(B_314,k1_zfmisc_1(u1_struct_0(A_313)))
      | ~ l1_pre_topc(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_7832,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_7828])).

tff(c_7836,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6795,c_7832])).

tff(c_20,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7840,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7836,c_20])).

tff(c_54,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_300,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1855,plain,(
    ! [B_137,A_138] :
      ( v4_pre_topc(B_137,A_138)
      | k2_pre_topc(A_138,B_137) != B_137
      | ~ v2_pre_topc(A_138)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1861,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1855])).

tff(c_1865,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_1861])).

tff(c_1866,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_1865])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_138,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_168,plain,(
    ! [B_61,A_62] : k3_tarski(k2_tarski(B_61,A_62)) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_138])).

tff(c_26,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_206,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_26])).

tff(c_259,plain,(
    ! [A_67] : k2_xboole_0(k1_xboole_0,A_67) = A_67 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_14])).

tff(c_18,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_303,plain,(
    ! [A_68] : k4_xboole_0(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_18])).

tff(c_22,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_308,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = k2_xboole_0(A_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_22])).

tff(c_324,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = A_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_308])).

tff(c_87,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k2_xboole_0(A_52,B_53)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_553,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_571,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_553])).

tff(c_575,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_571])).

tff(c_777,plain,(
    ! [A_89,B_90,C_91] :
      ( k7_subset_1(A_89,B_90,C_91) = k4_xboole_0(B_90,C_91)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_812,plain,(
    ! [C_94] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_94) = k4_xboole_0('#skF_2',C_94) ),
    inference(resolution,[status(thm)],[c_48,c_777])).

tff(c_60,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_97,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_818,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_812,c_97])).

tff(c_997,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_818,c_20])).

tff(c_780,plain,(
    ! [C_91] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_91) = k4_xboole_0('#skF_2',C_91) ),
    inference(resolution,[status(thm)],[c_48,c_777])).

tff(c_2066,plain,(
    ! [A_150,B_151] :
      ( k7_subset_1(u1_struct_0(A_150),B_151,k2_tops_1(A_150,B_151)) = k1_tops_1(A_150,B_151)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_150)))
      | ~ l1_pre_topc(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2070,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_2066])).

tff(c_2074,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_997,c_780,c_2070])).

tff(c_2075,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_997])).

tff(c_2135,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2075,c_20])).

tff(c_2141,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_818,c_2135])).

tff(c_153,plain,(
    ! [A_59,B_60] : k1_setfam_1(k2_tarski(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_477,plain,(
    ! [B_77,A_78] : k1_setfam_1(k2_tarski(B_77,A_78)) = k3_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_153])).

tff(c_32,plain,(
    ! [A_27,B_28] : k1_setfam_1(k2_tarski(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_483,plain,(
    ! [B_77,A_78] : k3_xboole_0(B_77,A_78) = k3_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_32])).

tff(c_562,plain,(
    ! [A_78,B_77] : k5_xboole_0(A_78,k3_xboole_0(B_77,A_78)) = k4_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_553])).

tff(c_2338,plain,(
    k5_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2141,c_562])).

tff(c_2357,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_575,c_2338])).

tff(c_2379,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2357,c_22])).

tff(c_2383,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_2379])).

tff(c_1994,plain,(
    ! [A_146,B_147] :
      ( k4_subset_1(u1_struct_0(A_146),B_147,k2_tops_1(A_146,B_147)) = k2_pre_topc(A_146,B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1998,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_1994])).

tff(c_2002,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1998])).

tff(c_38,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k2_tops_1(A_32,B_33),k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_32)))
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1645,plain,(
    ! [A_123,B_124,C_125] :
      ( k4_subset_1(A_123,B_124,C_125) = k2_xboole_0(B_124,C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(A_123))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5512,plain,(
    ! [A_207,B_208,B_209] :
      ( k4_subset_1(u1_struct_0(A_207),B_208,k2_tops_1(A_207,B_209)) = k2_xboole_0(B_208,k2_tops_1(A_207,B_209))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_207)))
      | ~ l1_pre_topc(A_207) ) ),
    inference(resolution,[status(thm)],[c_38,c_1645])).

tff(c_5516,plain,(
    ! [B_209] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_209)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_209))
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_5512])).

tff(c_5722,plain,(
    ! [B_212] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_212)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_212))
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_5516])).

tff(c_5729,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_5722])).

tff(c_5734,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2383,c_2002,c_5729])).

tff(c_5736,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1866,c_5734])).

tff(c_5737,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_6051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5737,c_97])).

tff(c_6052,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_6197,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6052,c_54])).

tff(c_6821,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6795,c_6197])).

tff(c_8019,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7840,c_6821])).

tff(c_6995,plain,(
    ! [A_278,B_279] :
      ( k2_pre_topc(A_278,B_279) = B_279
      | ~ v4_pre_topc(B_279,A_278)
      | ~ m1_subset_1(B_279,k1_zfmisc_1(u1_struct_0(A_278)))
      | ~ l1_pre_topc(A_278) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6998,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_6995])).

tff(c_7001,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6052,c_6998])).

tff(c_8033,plain,(
    ! [A_325,B_326] :
      ( k7_subset_1(u1_struct_0(A_325),k2_pre_topc(A_325,B_326),k1_tops_1(A_325,B_326)) = k2_tops_1(A_325,B_326)
      | ~ m1_subset_1(B_326,k1_zfmisc_1(u1_struct_0(A_325)))
      | ~ l1_pre_topc(A_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8042,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7001,c_8033])).

tff(c_8046,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_7840,c_6795,c_8042])).

tff(c_8048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8019,c_8046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n006.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 18:45:37 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.07/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.22  
% 6.07/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.22  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.07/2.22  
% 6.07/2.22  %Foreground sorts:
% 6.07/2.22  
% 6.07/2.22  
% 6.07/2.22  %Background operators:
% 6.07/2.22  
% 6.07/2.22  
% 6.07/2.22  %Foreground operators:
% 6.07/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.07/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.07/2.22  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 6.07/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.07/2.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.07/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.07/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.07/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.07/2.22  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.07/2.22  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 6.07/2.22  tff('#skF_2', type, '#skF_2': $i).
% 6.07/2.22  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 6.07/2.22  tff('#skF_1', type, '#skF_1': $i).
% 6.07/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.07/2.22  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 6.07/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.07/2.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.07/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.07/2.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.07/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.07/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.07/2.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.07/2.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 6.07/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.07/2.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.07/2.22  
% 6.07/2.24  tff(f_125, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 6.07/2.24  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 6.07/2.24  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 6.07/2.24  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.07/2.24  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 6.07/2.24  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.07/2.24  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.07/2.24  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.07/2.24  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 6.07/2.24  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.07/2.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.07/2.24  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.07/2.24  tff(f_63, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.07/2.24  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 6.07/2.24  tff(f_84, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 6.07/2.24  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.07/2.24  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 6.07/2.24  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.07/2.24  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.07/2.24  tff(c_6792, plain, (![A_264, B_265, C_266]: (k7_subset_1(A_264, B_265, C_266)=k4_xboole_0(B_265, C_266) | ~m1_subset_1(B_265, k1_zfmisc_1(A_264)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.07/2.24  tff(c_6795, plain, (![C_266]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_266)=k4_xboole_0('#skF_2', C_266))), inference(resolution, [status(thm)], [c_48, c_6792])).
% 6.07/2.24  tff(c_7828, plain, (![A_313, B_314]: (k7_subset_1(u1_struct_0(A_313), B_314, k2_tops_1(A_313, B_314))=k1_tops_1(A_313, B_314) | ~m1_subset_1(B_314, k1_zfmisc_1(u1_struct_0(A_313))) | ~l1_pre_topc(A_313))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.07/2.24  tff(c_7832, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_7828])).
% 6.07/2.24  tff(c_7836, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6795, c_7832])).
% 6.07/2.24  tff(c_20, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.07/2.24  tff(c_7840, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_7836, c_20])).
% 6.07/2.24  tff(c_54, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.07/2.24  tff(c_300, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_54])).
% 6.07/2.24  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.07/2.24  tff(c_1855, plain, (![B_137, A_138]: (v4_pre_topc(B_137, A_138) | k2_pre_topc(A_138, B_137)!=B_137 | ~v2_pre_topc(A_138) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.07/2.24  tff(c_1861, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1855])).
% 6.07/2.24  tff(c_1865, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_1861])).
% 6.07/2.24  tff(c_1866, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_300, c_1865])).
% 6.07/2.24  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.07/2.24  tff(c_24, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.07/2.24  tff(c_138, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.07/2.24  tff(c_168, plain, (![B_61, A_62]: (k3_tarski(k2_tarski(B_61, A_62))=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_24, c_138])).
% 6.07/2.24  tff(c_26, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.07/2.24  tff(c_206, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_168, c_26])).
% 6.07/2.24  tff(c_259, plain, (![A_67]: (k2_xboole_0(k1_xboole_0, A_67)=A_67)), inference(superposition, [status(thm), theory('equality')], [c_206, c_14])).
% 6.07/2.24  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.07/2.24  tff(c_303, plain, (![A_68]: (k4_xboole_0(k1_xboole_0, A_68)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_259, c_18])).
% 6.07/2.24  tff(c_22, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.07/2.24  tff(c_308, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=k2_xboole_0(A_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_303, c_22])).
% 6.07/2.24  tff(c_324, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_308])).
% 6.07/2.24  tff(c_87, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k2_xboole_0(A_52, B_53))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.07/2.24  tff(c_94, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_87])).
% 6.07/2.24  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.07/2.24  tff(c_553, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.07/2.24  tff(c_571, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_553])).
% 6.07/2.24  tff(c_575, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_571])).
% 6.07/2.24  tff(c_777, plain, (![A_89, B_90, C_91]: (k7_subset_1(A_89, B_90, C_91)=k4_xboole_0(B_90, C_91) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.07/2.24  tff(c_812, plain, (![C_94]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_94)=k4_xboole_0('#skF_2', C_94))), inference(resolution, [status(thm)], [c_48, c_777])).
% 6.07/2.24  tff(c_60, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_125])).
% 6.07/2.24  tff(c_97, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_60])).
% 6.07/2.24  tff(c_818, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_812, c_97])).
% 6.07/2.24  tff(c_997, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_818, c_20])).
% 6.07/2.24  tff(c_780, plain, (![C_91]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_91)=k4_xboole_0('#skF_2', C_91))), inference(resolution, [status(thm)], [c_48, c_777])).
% 6.07/2.24  tff(c_2066, plain, (![A_150, B_151]: (k7_subset_1(u1_struct_0(A_150), B_151, k2_tops_1(A_150, B_151))=k1_tops_1(A_150, B_151) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_150))) | ~l1_pre_topc(A_150))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.07/2.24  tff(c_2070, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_2066])).
% 6.07/2.24  tff(c_2074, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_997, c_780, c_2070])).
% 6.07/2.24  tff(c_2075, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_997])).
% 6.07/2.24  tff(c_2135, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2075, c_20])).
% 6.07/2.24  tff(c_2141, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_818, c_2135])).
% 6.07/2.24  tff(c_153, plain, (![A_59, B_60]: (k1_setfam_1(k2_tarski(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.07/2.24  tff(c_477, plain, (![B_77, A_78]: (k1_setfam_1(k2_tarski(B_77, A_78))=k3_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_24, c_153])).
% 6.07/2.24  tff(c_32, plain, (![A_27, B_28]: (k1_setfam_1(k2_tarski(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.07/2.24  tff(c_483, plain, (![B_77, A_78]: (k3_xboole_0(B_77, A_78)=k3_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_477, c_32])).
% 6.07/2.24  tff(c_562, plain, (![A_78, B_77]: (k5_xboole_0(A_78, k3_xboole_0(B_77, A_78))=k4_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_483, c_553])).
% 6.07/2.24  tff(c_2338, plain, (k5_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2141, c_562])).
% 6.07/2.24  tff(c_2357, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_575, c_2338])).
% 6.07/2.24  tff(c_2379, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2357, c_22])).
% 6.07/2.24  tff(c_2383, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_324, c_2379])).
% 6.07/2.24  tff(c_1994, plain, (![A_146, B_147]: (k4_subset_1(u1_struct_0(A_146), B_147, k2_tops_1(A_146, B_147))=k2_pre_topc(A_146, B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.07/2.24  tff(c_1998, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_1994])).
% 6.07/2.24  tff(c_2002, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1998])).
% 6.07/2.24  tff(c_38, plain, (![A_32, B_33]: (m1_subset_1(k2_tops_1(A_32, B_33), k1_zfmisc_1(u1_struct_0(A_32))) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_32))) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.07/2.24  tff(c_1645, plain, (![A_123, B_124, C_125]: (k4_subset_1(A_123, B_124, C_125)=k2_xboole_0(B_124, C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(A_123)) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.07/2.24  tff(c_5512, plain, (![A_207, B_208, B_209]: (k4_subset_1(u1_struct_0(A_207), B_208, k2_tops_1(A_207, B_209))=k2_xboole_0(B_208, k2_tops_1(A_207, B_209)) | ~m1_subset_1(B_208, k1_zfmisc_1(u1_struct_0(A_207))) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_207))) | ~l1_pre_topc(A_207))), inference(resolution, [status(thm)], [c_38, c_1645])).
% 6.07/2.24  tff(c_5516, plain, (![B_209]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_209))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_209)) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_48, c_5512])).
% 6.07/2.24  tff(c_5722, plain, (![B_212]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_212))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_212)) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_5516])).
% 6.07/2.24  tff(c_5729, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_5722])).
% 6.07/2.24  tff(c_5734, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2383, c_2002, c_5729])).
% 6.07/2.24  tff(c_5736, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1866, c_5734])).
% 6.07/2.24  tff(c_5737, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 6.07/2.24  tff(c_6051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5737, c_97])).
% 6.07/2.24  tff(c_6052, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_60])).
% 6.07/2.24  tff(c_6197, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6052, c_54])).
% 6.07/2.24  tff(c_6821, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6795, c_6197])).
% 6.07/2.24  tff(c_8019, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7840, c_6821])).
% 6.07/2.24  tff(c_6995, plain, (![A_278, B_279]: (k2_pre_topc(A_278, B_279)=B_279 | ~v4_pre_topc(B_279, A_278) | ~m1_subset_1(B_279, k1_zfmisc_1(u1_struct_0(A_278))) | ~l1_pre_topc(A_278))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.07/2.24  tff(c_6998, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_6995])).
% 6.07/2.24  tff(c_7001, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6052, c_6998])).
% 6.07/2.24  tff(c_8033, plain, (![A_325, B_326]: (k7_subset_1(u1_struct_0(A_325), k2_pre_topc(A_325, B_326), k1_tops_1(A_325, B_326))=k2_tops_1(A_325, B_326) | ~m1_subset_1(B_326, k1_zfmisc_1(u1_struct_0(A_325))) | ~l1_pre_topc(A_325))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.07/2.24  tff(c_8042, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7001, c_8033])).
% 6.07/2.24  tff(c_8046, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_7840, c_6795, c_8042])).
% 6.07/2.24  tff(c_8048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8019, c_8046])).
% 6.07/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.07/2.24  
% 6.07/2.24  Inference rules
% 6.07/2.24  ----------------------
% 6.07/2.24  #Ref     : 0
% 6.07/2.24  #Sup     : 1935
% 6.07/2.24  #Fact    : 0
% 6.07/2.24  #Define  : 0
% 6.07/2.24  #Split   : 5
% 6.07/2.24  #Chain   : 0
% 6.07/2.24  #Close   : 0
% 6.07/2.24  
% 6.07/2.24  Ordering : KBO
% 6.07/2.24  
% 6.07/2.24  Simplification rules
% 6.07/2.24  ----------------------
% 6.07/2.24  #Subsume      : 151
% 6.07/2.24  #Demod        : 2641
% 6.07/2.24  #Tautology    : 1552
% 6.07/2.24  #SimpNegUnit  : 4
% 6.07/2.24  #BackRed      : 7
% 6.07/2.24  
% 6.07/2.24  #Partial instantiations: 0
% 6.07/2.24  #Strategies tried      : 1
% 6.07/2.24  
% 6.07/2.24  Timing (in seconds)
% 6.07/2.24  ----------------------
% 6.07/2.24  Preprocessing        : 0.35
% 6.07/2.24  Parsing              : 0.19
% 6.07/2.24  CNF conversion       : 0.02
% 6.07/2.24  Main loop            : 1.14
% 6.07/2.24  Inferencing          : 0.35
% 6.07/2.24  Reduction            : 0.53
% 6.07/2.24  Demodulation         : 0.45
% 6.07/2.24  BG Simplification    : 0.03
% 6.07/2.24  Subsumption          : 0.15
% 6.07/2.24  Abstraction          : 0.06
% 6.07/2.24  MUC search           : 0.00
% 6.07/2.24  Cooper               : 0.00
% 6.07/2.24  Total                : 1.53
% 6.07/2.24  Index Insertion      : 0.00
% 6.07/2.24  Index Deletion       : 0.00
% 6.07/2.24  Index Matching       : 0.00
% 6.07/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
