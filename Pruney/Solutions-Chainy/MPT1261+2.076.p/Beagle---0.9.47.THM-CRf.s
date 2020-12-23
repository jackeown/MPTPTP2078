%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:22 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.80s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 155 expanded)
%              Number of leaves         :   39 (  68 expanded)
%              Depth                    :   11
%              Number of atoms          :  133 ( 273 expanded)
%              Number of equality atoms :   72 ( 112 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_68,axiom,(
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

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_5504,plain,(
    ! [A_183,B_184,C_185] :
      ( k7_subset_1(A_183,B_184,C_185) = k4_xboole_0(B_184,C_185)
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5507,plain,(
    ! [C_185] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_185) = k4_xboole_0('#skF_2',C_185) ),
    inference(resolution,[status(thm)],[c_34,c_5504])).

tff(c_40,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_153,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2172,plain,(
    ! [B_107,A_108] :
      ( v4_pre_topc(B_107,A_108)
      | k2_pre_topc(A_108,B_107) != B_107
      | ~ v2_pre_topc(A_108)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2178,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_2172])).

tff(c_2182,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38,c_2178])).

tff(c_2183,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_2182])).

tff(c_2501,plain,(
    ! [A_116,B_117] :
      ( k4_subset_1(u1_struct_0(A_116),B_117,k2_tops_1(A_116,B_117)) = k2_pre_topc(A_116,B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_2505,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_2501])).

tff(c_2509,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2505])).

tff(c_739,plain,(
    ! [A_71,B_72,C_73] :
      ( k7_subset_1(A_71,B_72,C_73) = k4_xboole_0(B_72,C_73)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_844,plain,(
    ! [C_78] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_78) = k4_xboole_0('#skF_2',C_78) ),
    inference(resolution,[status(thm)],[c_34,c_739])).

tff(c_46,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_300,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_46])).

tff(c_850,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_300])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_246,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_267,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k4_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_246])).

tff(c_270,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_267])).

tff(c_349,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_378,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_349])).

tff(c_384,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_378])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_264,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_246])).

tff(c_385,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_264])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_352,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,k4_xboole_0(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_12])).

tff(c_2186,plain,(
    ! [A_109,B_110] : k3_xboole_0(A_109,k4_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_352])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_115,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_130,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_22,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_22])).

tff(c_258,plain,(
    ! [A_43,B_42] : k5_xboole_0(A_43,k3_xboole_0(B_42,A_43)) = k4_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_246])).

tff(c_2222,plain,(
    ! [A_109,B_110] : k5_xboole_0(k4_xboole_0(A_109,B_110),k4_xboole_0(A_109,B_110)) = k4_xboole_0(k4_xboole_0(A_109,B_110),A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_2186,c_258])).

tff(c_2339,plain,(
    ! [A_112,B_113] : k4_xboole_0(k4_xboole_0(A_112,B_113),A_112) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_2222])).

tff(c_14,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2353,plain,(
    ! [A_112,B_113] : k2_xboole_0(A_112,k4_xboole_0(A_112,B_113)) = k5_xboole_0(A_112,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2339,c_14])).

tff(c_2421,plain,(
    ! [A_114,B_115] : k2_xboole_0(A_114,k4_xboole_0(A_114,B_115)) = A_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_2353])).

tff(c_2439,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_2421])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k2_tops_1(A_26,B_27),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1966,plain,(
    ! [A_101,B_102,C_103] :
      ( k4_subset_1(A_101,B_102,C_103) = k2_xboole_0(B_102,C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(A_101))
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4925,plain,(
    ! [A_154,B_155,B_156] :
      ( k4_subset_1(u1_struct_0(A_154),B_155,k2_tops_1(A_154,B_156)) = k2_xboole_0(B_155,k2_tops_1(A_154,B_156))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0(A_154)))
      | ~ l1_pre_topc(A_154) ) ),
    inference(resolution,[status(thm)],[c_28,c_1966])).

tff(c_4929,plain,(
    ! [B_156] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_156)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_156))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_4925])).

tff(c_4937,plain,(
    ! [B_157] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_157)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_157))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4929])).

tff(c_4944,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_4937])).

tff(c_4949,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2509,c_2439,c_4944])).

tff(c_4951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2183,c_4949])).

tff(c_4952,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5597,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5507,c_4952])).

tff(c_4953,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5743,plain,(
    ! [A_195,B_196] :
      ( k2_pre_topc(A_195,B_196) = B_196
      | ~ v4_pre_topc(B_196,A_195)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(u1_struct_0(A_195)))
      | ~ l1_pre_topc(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5746,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_5743])).

tff(c_5749,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4953,c_5746])).

tff(c_7241,plain,(
    ! [A_232,B_233] :
      ( k7_subset_1(u1_struct_0(A_232),k2_pre_topc(A_232,B_233),k1_tops_1(A_232,B_233)) = k2_tops_1(A_232,B_233)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_7250,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5749,c_7241])).

tff(c_7254,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_5507,c_7250])).

tff(c_7256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5597,c_7254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:31:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.44/3.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/3.20  
% 7.44/3.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/3.20  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.44/3.20  
% 7.44/3.20  %Foreground sorts:
% 7.44/3.20  
% 7.44/3.20  
% 7.44/3.20  %Background operators:
% 7.44/3.20  
% 7.44/3.20  
% 7.44/3.20  %Foreground operators:
% 7.44/3.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.44/3.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.44/3.20  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.44/3.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.44/3.20  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.44/3.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.44/3.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.44/3.20  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.44/3.20  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.44/3.20  tff('#skF_2', type, '#skF_2': $i).
% 7.44/3.20  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.44/3.20  tff('#skF_1', type, '#skF_1': $i).
% 7.44/3.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.44/3.20  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.44/3.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.44/3.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.44/3.20  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.44/3.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.44/3.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.44/3.20  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.44/3.20  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.44/3.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.44/3.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.44/3.20  
% 7.80/3.23  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 7.80/3.23  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.80/3.23  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.80/3.23  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 7.80/3.23  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.80/3.23  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.80/3.23  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.80/3.23  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.80/3.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.80/3.23  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 7.80/3.23  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.80/3.23  tff(f_53, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.80/3.23  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.80/3.23  tff(f_74, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 7.80/3.23  tff(f_47, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.80/3.23  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 7.80/3.23  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.80/3.23  tff(c_5504, plain, (![A_183, B_184, C_185]: (k7_subset_1(A_183, B_184, C_185)=k4_xboole_0(B_184, C_185) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.80/3.23  tff(c_5507, plain, (![C_185]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_185)=k4_xboole_0('#skF_2', C_185))), inference(resolution, [status(thm)], [c_34, c_5504])).
% 7.80/3.23  tff(c_40, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.80/3.23  tff(c_153, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 7.80/3.23  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.80/3.23  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.80/3.23  tff(c_2172, plain, (![B_107, A_108]: (v4_pre_topc(B_107, A_108) | k2_pre_topc(A_108, B_107)!=B_107 | ~v2_pre_topc(A_108) | ~m1_subset_1(B_107, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.80/3.23  tff(c_2178, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_2172])).
% 7.80/3.23  tff(c_2182, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38, c_2178])).
% 7.80/3.23  tff(c_2183, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_153, c_2182])).
% 7.80/3.23  tff(c_2501, plain, (![A_116, B_117]: (k4_subset_1(u1_struct_0(A_116), B_117, k2_tops_1(A_116, B_117))=k2_pre_topc(A_116, B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(u1_struct_0(A_116))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.80/3.23  tff(c_2505, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_2501])).
% 7.80/3.23  tff(c_2509, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2505])).
% 7.80/3.23  tff(c_739, plain, (![A_71, B_72, C_73]: (k7_subset_1(A_71, B_72, C_73)=k4_xboole_0(B_72, C_73) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.80/3.23  tff(c_844, plain, (![C_78]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_78)=k4_xboole_0('#skF_2', C_78))), inference(resolution, [status(thm)], [c_34, c_739])).
% 7.80/3.23  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.80/3.23  tff(c_300, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_153, c_46])).
% 7.80/3.23  tff(c_850, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_844, c_300])).
% 7.80/3.23  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.80/3.23  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.80/3.23  tff(c_246, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.80/3.23  tff(c_267, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k4_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_246])).
% 7.80/3.23  tff(c_270, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_267])).
% 7.80/3.23  tff(c_349, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.80/3.23  tff(c_378, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_349])).
% 7.80/3.23  tff(c_384, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_378])).
% 7.80/3.23  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.80/3.23  tff(c_264, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_246])).
% 7.80/3.23  tff(c_385, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_384, c_264])).
% 7.80/3.23  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.80/3.23  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.80/3.23  tff(c_352, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k3_xboole_0(A_55, k4_xboole_0(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_349, c_12])).
% 7.80/3.23  tff(c_2186, plain, (![A_109, B_110]: (k3_xboole_0(A_109, k4_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_352])).
% 7.80/3.23  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.80/3.23  tff(c_115, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.80/3.23  tff(c_130, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_16, c_115])).
% 7.80/3.23  tff(c_22, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.80/3.23  tff(c_136, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_130, c_22])).
% 7.80/3.23  tff(c_258, plain, (![A_43, B_42]: (k5_xboole_0(A_43, k3_xboole_0(B_42, A_43))=k4_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_136, c_246])).
% 7.80/3.23  tff(c_2222, plain, (![A_109, B_110]: (k5_xboole_0(k4_xboole_0(A_109, B_110), k4_xboole_0(A_109, B_110))=k4_xboole_0(k4_xboole_0(A_109, B_110), A_109))), inference(superposition, [status(thm), theory('equality')], [c_2186, c_258])).
% 7.80/3.23  tff(c_2339, plain, (![A_112, B_113]: (k4_xboole_0(k4_xboole_0(A_112, B_113), A_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_385, c_2222])).
% 7.80/3.23  tff(c_14, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.80/3.23  tff(c_2353, plain, (![A_112, B_113]: (k2_xboole_0(A_112, k4_xboole_0(A_112, B_113))=k5_xboole_0(A_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2339, c_14])).
% 7.80/3.23  tff(c_2421, plain, (![A_114, B_115]: (k2_xboole_0(A_114, k4_xboole_0(A_114, B_115))=A_114)), inference(demodulation, [status(thm), theory('equality')], [c_270, c_2353])).
% 7.80/3.23  tff(c_2439, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_850, c_2421])).
% 7.80/3.23  tff(c_28, plain, (![A_26, B_27]: (m1_subset_1(k2_tops_1(A_26, B_27), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_26))) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.80/3.23  tff(c_1966, plain, (![A_101, B_102, C_103]: (k4_subset_1(A_101, B_102, C_103)=k2_xboole_0(B_102, C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(A_101)) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.80/3.23  tff(c_4925, plain, (![A_154, B_155, B_156]: (k4_subset_1(u1_struct_0(A_154), B_155, k2_tops_1(A_154, B_156))=k2_xboole_0(B_155, k2_tops_1(A_154, B_156)) | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0(A_154))) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0(A_154))) | ~l1_pre_topc(A_154))), inference(resolution, [status(thm)], [c_28, c_1966])).
% 7.80/3.23  tff(c_4929, plain, (![B_156]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_156))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_156)) | ~m1_subset_1(B_156, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_4925])).
% 7.80/3.23  tff(c_4937, plain, (![B_157]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_157))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_157)) | ~m1_subset_1(B_157, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4929])).
% 7.80/3.23  tff(c_4944, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_4937])).
% 7.80/3.23  tff(c_4949, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2509, c_2439, c_4944])).
% 7.80/3.23  tff(c_4951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2183, c_4949])).
% 7.80/3.23  tff(c_4952, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 7.80/3.23  tff(c_5597, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5507, c_4952])).
% 7.80/3.23  tff(c_4953, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_40])).
% 7.80/3.23  tff(c_5743, plain, (![A_195, B_196]: (k2_pre_topc(A_195, B_196)=B_196 | ~v4_pre_topc(B_196, A_195) | ~m1_subset_1(B_196, k1_zfmisc_1(u1_struct_0(A_195))) | ~l1_pre_topc(A_195))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.80/3.23  tff(c_5746, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_34, c_5743])).
% 7.80/3.23  tff(c_5749, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4953, c_5746])).
% 7.80/3.23  tff(c_7241, plain, (![A_232, B_233]: (k7_subset_1(u1_struct_0(A_232), k2_pre_topc(A_232, B_233), k1_tops_1(A_232, B_233))=k2_tops_1(A_232, B_233) | ~m1_subset_1(B_233, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.80/3.23  tff(c_7250, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5749, c_7241])).
% 7.80/3.23  tff(c_7254, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_5507, c_7250])).
% 7.80/3.23  tff(c_7256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5597, c_7254])).
% 7.80/3.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.80/3.23  
% 7.80/3.23  Inference rules
% 7.80/3.23  ----------------------
% 7.80/3.23  #Ref     : 0
% 7.80/3.23  #Sup     : 1753
% 7.80/3.23  #Fact    : 0
% 7.80/3.23  #Define  : 0
% 7.80/3.23  #Split   : 2
% 7.80/3.23  #Chain   : 0
% 7.80/3.23  #Close   : 0
% 7.80/3.23  
% 7.80/3.23  Ordering : KBO
% 7.80/3.23  
% 7.80/3.23  Simplification rules
% 7.80/3.23  ----------------------
% 7.80/3.23  #Subsume      : 116
% 7.80/3.23  #Demod        : 2685
% 7.80/3.23  #Tautology    : 1482
% 7.80/3.23  #SimpNegUnit  : 4
% 7.80/3.23  #BackRed      : 3
% 7.80/3.23  
% 7.80/3.23  #Partial instantiations: 0
% 7.80/3.23  #Strategies tried      : 1
% 7.80/3.23  
% 7.80/3.23  Timing (in seconds)
% 7.80/3.23  ----------------------
% 7.80/3.23  Preprocessing        : 0.53
% 7.80/3.23  Parsing              : 0.28
% 7.80/3.23  CNF conversion       : 0.03
% 7.80/3.23  Main loop            : 1.79
% 7.80/3.23  Inferencing          : 0.52
% 7.80/3.23  Reduction            : 0.92
% 7.80/3.24  Demodulation         : 0.79
% 7.80/3.24  BG Simplification    : 0.06
% 7.80/3.24  Subsumption          : 0.20
% 7.80/3.24  Abstraction          : 0.10
% 7.80/3.24  MUC search           : 0.00
% 7.80/3.24  Cooper               : 0.00
% 7.80/3.24  Total                : 2.39
% 7.80/3.24  Index Insertion      : 0.00
% 7.80/3.24  Index Deletion       : 0.00
% 7.80/3.24  Index Matching       : 0.00
% 7.80/3.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
