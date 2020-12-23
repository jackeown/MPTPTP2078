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
% DateTime   : Thu Dec  3 10:21:32 EST 2020

% Result     : Theorem 4.93s
% Output     : CNFRefutation 5.20s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 174 expanded)
%              Number of leaves         :   40 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 ( 297 expanded)
%              Number of equality atoms :   77 ( 121 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4975,plain,(
    ! [A_194,B_195,C_196] :
      ( k7_subset_1(A_194,B_195,C_196) = k4_xboole_0(B_195,C_196)
      | ~ m1_subset_1(B_195,k1_zfmisc_1(A_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4978,plain,(
    ! [C_196] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_196) = k4_xboole_0('#skF_2',C_196) ),
    inference(resolution,[status(thm)],[c_38,c_4975])).

tff(c_44,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_116,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1477,plain,(
    ! [B_112,A_113] :
      ( v4_pre_topc(B_112,A_113)
      | k2_pre_topc(A_113,B_112) != B_112
      | ~ v2_pre_topc(A_113)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1483,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1477])).

tff(c_1487,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42,c_1483])).

tff(c_1488,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_1487])).

tff(c_2203,plain,(
    ! [A_128,B_129] :
      ( k4_subset_1(u1_struct_0(A_128),B_129,k2_tops_1(A_128,B_129)) = k2_pre_topc(A_128,B_129)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2207,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_2203])).

tff(c_2211,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2207])).

tff(c_10,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_328,plain,(
    ! [A_64,B_65,C_66] :
      ( k7_subset_1(A_64,B_65,C_66) = k4_xboole_0(B_65,C_66)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_381,plain,(
    ! [C_68] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_68) = k4_xboole_0('#skF_2',C_68) ),
    inference(resolution,[status(thm)],[c_38,c_328])).

tff(c_50,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_229,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_50])).

tff(c_387,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_229])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_251,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_14,plain,(
    ! [A_12,B_13] : r1_tarski(k4_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_51,B_52] : k2_xboole_0(k4_xboole_0(A_51,B_52),A_51) = A_51 ),
    inference(resolution,[status(thm)],[c_14,c_117])).

tff(c_152,plain,(
    ! [B_52] : k4_xboole_0(k1_xboole_0,B_52) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_10])).

tff(c_291,plain,(
    ! [B_63] : k3_xboole_0(k1_xboole_0,B_63) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_152])).

tff(c_312,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_291])).

tff(c_18,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_286,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k3_xboole_0(A_16,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_251])).

tff(c_562,plain,(
    ! [A_16] : k4_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_286])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_202,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_202])).

tff(c_563,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_562,c_217])).

tff(c_191,plain,(
    ! [A_54,B_55] :
      ( k3_xboole_0(A_54,B_55) = A_54
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_767,plain,(
    ! [A_88,B_89] : k3_xboole_0(k4_xboole_0(A_88,B_89),A_88) = k4_xboole_0(A_88,B_89) ),
    inference(resolution,[status(thm)],[c_14,c_191])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_792,plain,(
    ! [A_88,B_89] : k5_xboole_0(k4_xboole_0(A_88,B_89),k4_xboole_0(A_88,B_89)) = k4_xboole_0(k4_xboole_0(A_88,B_89),A_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_6])).

tff(c_844,plain,(
    ! [A_90,B_91] : k4_xboole_0(k4_xboole_0(A_90,B_91),A_90) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_563,c_792])).

tff(c_879,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_844])).

tff(c_16,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1047,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_879,c_16])).

tff(c_1060,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1047])).

tff(c_30,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k2_tops_1(A_28,B_29),k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_28)))
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_907,plain,(
    ! [A_92,B_93,C_94] :
      ( k4_subset_1(A_92,B_93,C_94) = k2_xboole_0(B_93,C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(A_92))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4580,plain,(
    ! [A_167,B_168,B_169] :
      ( k4_subset_1(u1_struct_0(A_167),B_168,k2_tops_1(A_167,B_169)) = k2_xboole_0(B_168,k2_tops_1(A_167,B_169))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0(A_167)))
      | ~ l1_pre_topc(A_167) ) ),
    inference(resolution,[status(thm)],[c_30,c_907])).

tff(c_4584,plain,(
    ! [B_169] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_169)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_169))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_38,c_4580])).

tff(c_4592,plain,(
    ! [B_170] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_170)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_170))
      | ~ m1_subset_1(B_170,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4584])).

tff(c_4599,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_4592])).

tff(c_4604,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2211,c_1060,c_4599])).

tff(c_4606,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1488,c_4604])).

tff(c_4607,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5042,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4978,c_4607])).

tff(c_4608,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5705,plain,(
    ! [A_230,B_231] :
      ( r1_tarski(k2_tops_1(A_230,B_231),B_231)
      | ~ v4_pre_topc(B_231,A_230)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_230)))
      | ~ l1_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5709,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_5705])).

tff(c_5713,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4608,c_5709])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5720,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_5713,c_12])).

tff(c_20,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4683,plain,(
    ! [A_177,B_178] :
      ( k3_xboole_0(A_177,B_178) = A_177
      | ~ r1_tarski(A_177,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5169,plain,(
    ! [A_207,B_208] : k3_xboole_0(k4_xboole_0(A_207,B_208),A_207) = k4_xboole_0(A_207,B_208) ),
    inference(resolution,[status(thm)],[c_14,c_4683])).

tff(c_5210,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(k3_xboole_0(A_17,B_18),A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_5169])).

tff(c_6200,plain,(
    ! [A_244,B_245] : k3_xboole_0(A_244,k3_xboole_0(A_244,B_245)) = k3_xboole_0(A_244,B_245) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_5210])).

tff(c_6261,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5720,c_6200])).

tff(c_6305,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_2,c_6261])).

tff(c_6628,plain,(
    ! [A_252,B_253] :
      ( k7_subset_1(u1_struct_0(A_252),B_253,k2_tops_1(A_252,B_253)) = k1_tops_1(A_252,B_253)
      | ~ m1_subset_1(B_253,k1_zfmisc_1(u1_struct_0(A_252)))
      | ~ l1_pre_topc(A_252) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6632,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_6628])).

tff(c_6636,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4978,c_6632])).

tff(c_6661,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6636,c_20])).

tff(c_6678,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6305,c_6661])).

tff(c_6680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5042,c_6678])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.93/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/2.00  
% 5.20/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/2.00  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.20/2.00  
% 5.20/2.00  %Foreground sorts:
% 5.20/2.00  
% 5.20/2.00  
% 5.20/2.00  %Background operators:
% 5.20/2.00  
% 5.20/2.00  
% 5.20/2.00  %Foreground operators:
% 5.20/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.20/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.20/2.00  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.20/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.20/2.00  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.20/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.20/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.20/2.00  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.20/2.00  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.20/2.00  tff('#skF_2', type, '#skF_2': $i).
% 5.20/2.00  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.20/2.00  tff('#skF_1', type, '#skF_1': $i).
% 5.20/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.20/2.00  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.20/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.20/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.20/2.00  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.20/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.20/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.20/2.00  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.20/2.00  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.20/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.20/2.00  
% 5.20/2.02  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 5.20/2.02  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.20/2.02  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 5.20/2.02  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 5.20/2.02  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 5.20/2.02  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.20/2.02  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.20/2.02  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.20/2.02  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.20/2.02  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.20/2.02  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.20/2.02  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.20/2.02  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.20/2.02  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.20/2.02  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.20/2.02  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.20/2.02  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 5.20/2.02  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 5.20/2.02  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.20/2.02  tff(c_4975, plain, (![A_194, B_195, C_196]: (k7_subset_1(A_194, B_195, C_196)=k4_xboole_0(B_195, C_196) | ~m1_subset_1(B_195, k1_zfmisc_1(A_194)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.20/2.02  tff(c_4978, plain, (![C_196]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_196)=k4_xboole_0('#skF_2', C_196))), inference(resolution, [status(thm)], [c_38, c_4975])).
% 5.20/2.02  tff(c_44, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.20/2.02  tff(c_116, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 5.20/2.02  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.20/2.02  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.20/2.02  tff(c_1477, plain, (![B_112, A_113]: (v4_pre_topc(B_112, A_113) | k2_pre_topc(A_113, B_112)!=B_112 | ~v2_pre_topc(A_113) | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.20/2.02  tff(c_1483, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_1477])).
% 5.20/2.02  tff(c_1487, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42, c_1483])).
% 5.20/2.02  tff(c_1488, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_116, c_1487])).
% 5.20/2.02  tff(c_2203, plain, (![A_128, B_129]: (k4_subset_1(u1_struct_0(A_128), B_129, k2_tops_1(A_128, B_129))=k2_pre_topc(A_128, B_129) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_128))) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.20/2.02  tff(c_2207, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_2203])).
% 5.20/2.02  tff(c_2211, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2207])).
% 5.20/2.02  tff(c_10, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.20/2.02  tff(c_328, plain, (![A_64, B_65, C_66]: (k7_subset_1(A_64, B_65, C_66)=k4_xboole_0(B_65, C_66) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.20/2.02  tff(c_381, plain, (![C_68]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_68)=k4_xboole_0('#skF_2', C_68))), inference(resolution, [status(thm)], [c_38, c_328])).
% 5.20/2.02  tff(c_50, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.20/2.02  tff(c_229, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_116, c_50])).
% 5.20/2.02  tff(c_387, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_381, c_229])).
% 5.20/2.02  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.20/2.02  tff(c_251, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.20/2.02  tff(c_14, plain, (![A_12, B_13]: (r1_tarski(k4_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.20/2.02  tff(c_117, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.20/2.02  tff(c_145, plain, (![A_51, B_52]: (k2_xboole_0(k4_xboole_0(A_51, B_52), A_51)=A_51)), inference(resolution, [status(thm)], [c_14, c_117])).
% 5.20/2.02  tff(c_152, plain, (![B_52]: (k4_xboole_0(k1_xboole_0, B_52)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_145, c_10])).
% 5.20/2.02  tff(c_291, plain, (![B_63]: (k3_xboole_0(k1_xboole_0, B_63)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_251, c_152])).
% 5.20/2.02  tff(c_312, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_291])).
% 5.20/2.02  tff(c_18, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.20/2.02  tff(c_286, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k3_xboole_0(A_16, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_251])).
% 5.20/2.02  tff(c_562, plain, (![A_16]: (k4_xboole_0(A_16, A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_312, c_286])).
% 5.20/2.02  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.20/2.02  tff(c_202, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.20/2.02  tff(c_217, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_202])).
% 5.20/2.02  tff(c_563, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_562, c_217])).
% 5.20/2.02  tff(c_191, plain, (![A_54, B_55]: (k3_xboole_0(A_54, B_55)=A_54 | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.20/2.02  tff(c_767, plain, (![A_88, B_89]: (k3_xboole_0(k4_xboole_0(A_88, B_89), A_88)=k4_xboole_0(A_88, B_89))), inference(resolution, [status(thm)], [c_14, c_191])).
% 5.20/2.02  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.20/2.02  tff(c_792, plain, (![A_88, B_89]: (k5_xboole_0(k4_xboole_0(A_88, B_89), k4_xboole_0(A_88, B_89))=k4_xboole_0(k4_xboole_0(A_88, B_89), A_88))), inference(superposition, [status(thm), theory('equality')], [c_767, c_6])).
% 5.20/2.02  tff(c_844, plain, (![A_90, B_91]: (k4_xboole_0(k4_xboole_0(A_90, B_91), A_90)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_563, c_792])).
% 5.20/2.02  tff(c_879, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_387, c_844])).
% 5.20/2.02  tff(c_16, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.20/2.02  tff(c_1047, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_879, c_16])).
% 5.20/2.02  tff(c_1060, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1047])).
% 5.20/2.02  tff(c_30, plain, (![A_28, B_29]: (m1_subset_1(k2_tops_1(A_28, B_29), k1_zfmisc_1(u1_struct_0(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_28))) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_80])).
% 5.20/2.02  tff(c_907, plain, (![A_92, B_93, C_94]: (k4_subset_1(A_92, B_93, C_94)=k2_xboole_0(B_93, C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(A_92)) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.20/2.02  tff(c_4580, plain, (![A_167, B_168, B_169]: (k4_subset_1(u1_struct_0(A_167), B_168, k2_tops_1(A_167, B_169))=k2_xboole_0(B_168, k2_tops_1(A_167, B_169)) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_167))) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0(A_167))) | ~l1_pre_topc(A_167))), inference(resolution, [status(thm)], [c_30, c_907])).
% 5.20/2.02  tff(c_4584, plain, (![B_169]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_169))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_169)) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_4580])).
% 5.20/2.02  tff(c_4592, plain, (![B_170]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_170))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_170)) | ~m1_subset_1(B_170, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4584])).
% 5.20/2.02  tff(c_4599, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_4592])).
% 5.20/2.02  tff(c_4604, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2211, c_1060, c_4599])).
% 5.20/2.02  tff(c_4606, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1488, c_4604])).
% 5.20/2.02  tff(c_4607, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_44])).
% 5.20/2.02  tff(c_5042, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4978, c_4607])).
% 5.20/2.02  tff(c_4608, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 5.20/2.02  tff(c_5705, plain, (![A_230, B_231]: (r1_tarski(k2_tops_1(A_230, B_231), B_231) | ~v4_pre_topc(B_231, A_230) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_230))) | ~l1_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.20/2.02  tff(c_5709, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_5705])).
% 5.20/2.02  tff(c_5713, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4608, c_5709])).
% 5.20/2.02  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.20/2.02  tff(c_5720, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_5713, c_12])).
% 5.20/2.02  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.20/2.02  tff(c_4683, plain, (![A_177, B_178]: (k3_xboole_0(A_177, B_178)=A_177 | ~r1_tarski(A_177, B_178))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.20/2.02  tff(c_5169, plain, (![A_207, B_208]: (k3_xboole_0(k4_xboole_0(A_207, B_208), A_207)=k4_xboole_0(A_207, B_208))), inference(resolution, [status(thm)], [c_14, c_4683])).
% 5.20/2.02  tff(c_5210, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(k3_xboole_0(A_17, B_18), A_17))), inference(superposition, [status(thm), theory('equality')], [c_20, c_5169])).
% 5.20/2.02  tff(c_6200, plain, (![A_244, B_245]: (k3_xboole_0(A_244, k3_xboole_0(A_244, B_245))=k3_xboole_0(A_244, B_245))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2, c_5210])).
% 5.20/2.02  tff(c_6261, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5720, c_6200])).
% 5.20/2.02  tff(c_6305, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_2, c_6261])).
% 5.20/2.02  tff(c_6628, plain, (![A_252, B_253]: (k7_subset_1(u1_struct_0(A_252), B_253, k2_tops_1(A_252, B_253))=k1_tops_1(A_252, B_253) | ~m1_subset_1(B_253, k1_zfmisc_1(u1_struct_0(A_252))) | ~l1_pre_topc(A_252))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.20/2.02  tff(c_6632, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_6628])).
% 5.20/2.02  tff(c_6636, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_4978, c_6632])).
% 5.20/2.02  tff(c_6661, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_6636, c_20])).
% 5.20/2.02  tff(c_6678, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6305, c_6661])).
% 5.20/2.02  tff(c_6680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5042, c_6678])).
% 5.20/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/2.02  
% 5.20/2.02  Inference rules
% 5.20/2.02  ----------------------
% 5.20/2.02  #Ref     : 0
% 5.20/2.02  #Sup     : 1632
% 5.20/2.02  #Fact    : 0
% 5.20/2.02  #Define  : 0
% 5.20/2.02  #Split   : 2
% 5.20/2.02  #Chain   : 0
% 5.20/2.02  #Close   : 0
% 5.20/2.02  
% 5.20/2.02  Ordering : KBO
% 5.20/2.02  
% 5.20/2.02  Simplification rules
% 5.20/2.02  ----------------------
% 5.20/2.02  #Subsume      : 30
% 5.20/2.02  #Demod        : 1831
% 5.20/2.02  #Tautology    : 1345
% 5.20/2.02  #SimpNegUnit  : 4
% 5.20/2.02  #BackRed      : 5
% 5.20/2.02  
% 5.20/2.02  #Partial instantiations: 0
% 5.20/2.02  #Strategies tried      : 1
% 5.20/2.02  
% 5.20/2.02  Timing (in seconds)
% 5.20/2.02  ----------------------
% 5.20/2.02  Preprocessing        : 0.33
% 5.20/2.02  Parsing              : 0.18
% 5.20/2.02  CNF conversion       : 0.02
% 5.20/2.02  Main loop            : 0.91
% 5.20/2.02  Inferencing          : 0.28
% 5.20/2.02  Reduction            : 0.42
% 5.20/2.02  Demodulation         : 0.35
% 5.20/2.02  BG Simplification    : 0.03
% 5.20/2.02  Subsumption          : 0.12
% 5.20/2.02  Abstraction          : 0.05
% 5.20/2.02  MUC search           : 0.00
% 5.20/2.02  Cooper               : 0.00
% 5.20/2.02  Total                : 1.28
% 5.20/2.02  Index Insertion      : 0.00
% 5.20/2.02  Index Deletion       : 0.00
% 5.20/2.02  Index Matching       : 0.00
% 5.20/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
