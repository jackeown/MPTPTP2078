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
% DateTime   : Thu Dec  3 10:22:56 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 205 expanded)
%              Number of leaves         :   36 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 468 expanded)
%              Number of equality atoms :   19 (  71 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > v2_tops_2 > v1_tops_2 > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_finset_1 > l1_struct_0 > l1_pre_topc > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_tops_2,type,(
    v1_tops_2: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v2_tops_2,type,(
    v2_tops_2: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ( ( v2_tops_2(B,A)
                & v1_finset_1(B) )
             => v4_pre_topc(k5_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tops_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v2_tops_2(B,A)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(A),B))
          <=> v1_finset_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tops_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k6_setfam_1(A,k7_setfam_1(A,B)) = k3_subset_1(A,k5_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_27,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v1_xboole_0(B)
           => v4_pre_topc(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
         => ( ( v1_tops_2(B,A)
              & v1_finset_1(B) )
           => v3_pre_topc(k6_setfam_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_2)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_48,plain,(
    ! [A_27,B_28] :
      ( k5_setfam_1(A_27,B_28) = k3_tarski(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_48])).

tff(c_32,plain,(
    ~ v4_pre_topc(k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_53,plain,(
    ~ v4_pre_topc(k3_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_32])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k5_setfam_1(A_29,B_30),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(k1_zfmisc_1(A_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,
    ( m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_58])).

tff(c_68,plain,(
    m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_65])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36,plain,(
    v2_tops_2('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_191,plain,(
    ! [A_45,B_46] :
      ( v1_tops_2(k7_setfam_1(u1_struct_0(A_45),B_46),A_45)
      | ~ v2_tops_2(B_46,A_45)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45))))
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_201,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v2_tops_2('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_191])).

tff(c_209,plain,(
    v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_201])).

tff(c_14,plain,(
    ! [A_10] :
      ( l1_struct_0(A_10)
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    v1_finset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_150,plain,(
    ! [A_39,B_40] :
      ( v1_finset_1(k7_setfam_1(u1_struct_0(A_39),B_40))
      | ~ v1_finset_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39))))
      | ~ l1_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_164,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ v1_finset_1('#skF_2')
    | ~ l1_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_150])).

tff(c_170,plain,
    ( v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ l1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_164])).

tff(c_171,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_170])).

tff(c_174,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_171])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_174])).

tff(c_179,plain,(
    v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(splitRight,[status(thm)],[c_170])).

tff(c_224,plain,(
    ! [A_49,B_50] :
      ( k6_setfam_1(A_49,k7_setfam_1(A_49,B_50)) = k3_subset_1(A_49,k5_setfam_1(A_49,B_50))
      | k1_xboole_0 = B_50
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_233,plain,
    ( k6_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k5_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_224])).

tff(c_239,plain,
    ( k6_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_233])).

tff(c_240,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_243,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_2])).

tff(c_4,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_242,plain,(
    k3_tarski('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_240,c_4])).

tff(c_74,plain,(
    ! [B_33,A_34] :
      ( v4_pre_topc(B_33,A_34)
      | ~ v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(u1_struct_0(A_34)))
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,
    ( v4_pre_topc(k3_tarski('#skF_2'),'#skF_1')
    | ~ v1_xboole_0(k3_tarski('#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_74])).

tff(c_84,plain,
    ( v4_pre_topc(k3_tarski('#skF_2'),'#skF_1')
    | ~ v1_xboole_0(k3_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_77])).

tff(c_85,plain,(
    ~ v1_xboole_0(k3_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_84])).

tff(c_267,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_85])).

tff(c_273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_267])).

tff(c_274,plain,(
    k6_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(k7_setfam_1(A_3,B_4),k1_zfmisc_1(k1_zfmisc_1(A_3)))
      | ~ m1_subset_1(B_4,k1_zfmisc_1(k1_zfmisc_1(A_3))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k7_setfam_1(A_31,B_32),k1_zfmisc_1(k1_zfmisc_1(A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(k1_zfmisc_1(A_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k5_setfam_1(A_5,B_6) = k3_tarski(B_6)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_35,B_36] :
      ( k5_setfam_1(A_35,k7_setfam_1(A_35,B_36)) = k3_tarski(k7_setfam_1(A_35,B_36))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(k1_zfmisc_1(A_35))) ) ),
    inference(resolution,[status(thm)],[c_69,c_10])).

tff(c_97,plain,(
    k5_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) = k3_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_87])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k5_setfam_1(A_1,B_2),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(k1_zfmisc_1(A_1))) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,
    ( m1_subset_1(k3_tarski(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_6])).

tff(c_105,plain,(
    ~ m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_108,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_108])).

tff(c_114,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_324,plain,(
    ! [A_57,B_58] :
      ( v3_pre_topc(k6_setfam_1(u1_struct_0(A_57),B_58),A_57)
      | ~ v1_finset_1(B_58)
      | ~ v1_tops_2(B_58,A_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_57))))
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_326,plain,
    ( v3_pre_topc(k6_setfam_1(u1_struct_0('#skF_1'),k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2')),'#skF_1')
    | ~ v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_324])).

tff(c_337,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'),k3_tarski('#skF_2')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_209,c_179,c_274,c_326])).

tff(c_16,plain,(
    ! [B_13,A_11] :
      ( v4_pre_topc(B_13,A_11)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_11),B_13),A_11)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_345,plain,
    ( v4_pre_topc(k3_tarski('#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_337,c_16])).

tff(c_348,plain,(
    v4_pre_topc(k3_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_68,c_345])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.35  
% 2.41/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.36  %$ v4_pre_topc > v3_pre_topc > v2_tops_2 > v1_tops_2 > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_finset_1 > l1_struct_0 > l1_pre_topc > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k3_subset_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.41/1.36  
% 2.41/1.36  %Foreground sorts:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Background operators:
% 2.41/1.36  
% 2.41/1.36  
% 2.41/1.36  %Foreground operators:
% 2.41/1.36  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.36  tff(v1_tops_2, type, v1_tops_2: ($i * $i) > $o).
% 2.41/1.36  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.41/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.41/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.41/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.41/1.36  tff(v2_tops_2, type, v2_tops_2: ($i * $i) > $o).
% 2.41/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.41/1.36  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.41/1.36  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.41/1.36  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.41/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.41/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.41/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.41/1.36  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 2.41/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.41/1.36  
% 2.72/1.38  tff(f_115, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((v2_tops_2(B, A) & v1_finset_1(B)) => v4_pre_topc(k5_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_tops_2)).
% 2.72/1.38  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.72/1.38  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.72/1.38  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v2_tops_2(B, A) <=> v1_tops_2(k7_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tops_2)).
% 2.72/1.38  tff(f_54, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.72/1.38  tff(f_79, axiom, (![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (v1_finset_1(k7_setfam_1(u1_struct_0(A), B)) <=> v1_finset_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tops_2)).
% 2.72/1.38  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k6_setfam_1(A, k7_setfam_1(A, B)) = k3_subset_1(A, k5_setfam_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tops_2)).
% 2.72/1.38  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.72/1.38  tff(f_27, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.72/1.38  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_xboole_0(B) => v4_pre_topc(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_pre_topc)).
% 2.72/1.38  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 2.72/1.38  tff(f_101, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ((v1_tops_2(B, A) & v1_finset_1(B)) => v3_pre_topc(k6_setfam_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_tops_2)).
% 2.72/1.38  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tops_1)).
% 2.72/1.38  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.38  tff(c_48, plain, (![A_27, B_28]: (k5_setfam_1(A_27, B_28)=k3_tarski(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_27))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.38  tff(c_52, plain, (k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_38, c_48])).
% 2.72/1.38  tff(c_32, plain, (~v4_pre_topc(k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.38  tff(c_53, plain, (~v4_pre_topc(k3_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_32])).
% 2.72/1.38  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.38  tff(c_58, plain, (![A_29, B_30]: (m1_subset_1(k5_setfam_1(A_29, B_30), k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(k1_zfmisc_1(A_29))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.38  tff(c_65, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_52, c_58])).
% 2.72/1.38  tff(c_68, plain, (m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_65])).
% 2.72/1.38  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.38  tff(c_36, plain, (v2_tops_2('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.38  tff(c_191, plain, (![A_45, B_46]: (v1_tops_2(k7_setfam_1(u1_struct_0(A_45), B_46), A_45) | ~v2_tops_2(B_46, A_45) | ~m1_subset_1(B_46, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_45)))) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.72/1.38  tff(c_201, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v2_tops_2('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_191])).
% 2.72/1.38  tff(c_209, plain, (v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_201])).
% 2.72/1.38  tff(c_14, plain, (![A_10]: (l1_struct_0(A_10) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.72/1.38  tff(c_34, plain, (v1_finset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.72/1.38  tff(c_150, plain, (![A_39, B_40]: (v1_finset_1(k7_setfam_1(u1_struct_0(A_39), B_40)) | ~v1_finset_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_39)))) | ~l1_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.72/1.38  tff(c_164, plain, (v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~v1_finset_1('#skF_2') | ~l1_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_150])).
% 2.72/1.38  tff(c_170, plain, (v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~l1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_164])).
% 2.72/1.38  tff(c_171, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_170])).
% 2.72/1.38  tff(c_174, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_14, c_171])).
% 2.72/1.38  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_174])).
% 2.72/1.38  tff(c_179, plain, (v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(splitRight, [status(thm)], [c_170])).
% 2.72/1.38  tff(c_224, plain, (![A_49, B_50]: (k6_setfam_1(A_49, k7_setfam_1(A_49, B_50))=k3_subset_1(A_49, k5_setfam_1(A_49, B_50)) | k1_xboole_0=B_50 | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.72/1.38  tff(c_233, plain, (k6_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k5_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_224])).
% 2.72/1.38  tff(c_239, plain, (k6_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_233])).
% 2.72/1.38  tff(c_240, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_239])).
% 2.72/1.38  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.72/1.38  tff(c_243, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_2])).
% 2.72/1.38  tff(c_4, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.38  tff(c_242, plain, (k3_tarski('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_240, c_240, c_4])).
% 2.72/1.38  tff(c_74, plain, (![B_33, A_34]: (v4_pre_topc(B_33, A_34) | ~v1_xboole_0(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(u1_struct_0(A_34))) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.72/1.38  tff(c_77, plain, (v4_pre_topc(k3_tarski('#skF_2'), '#skF_1') | ~v1_xboole_0(k3_tarski('#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_68, c_74])).
% 2.72/1.38  tff(c_84, plain, (v4_pre_topc(k3_tarski('#skF_2'), '#skF_1') | ~v1_xboole_0(k3_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_77])).
% 2.72/1.38  tff(c_85, plain, (~v1_xboole_0(k3_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_53, c_84])).
% 2.72/1.38  tff(c_267, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_85])).
% 2.72/1.38  tff(c_273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_243, c_267])).
% 2.72/1.38  tff(c_274, plain, (k6_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_239])).
% 2.72/1.38  tff(c_8, plain, (![A_3, B_4]: (m1_subset_1(k7_setfam_1(A_3, B_4), k1_zfmisc_1(k1_zfmisc_1(A_3))) | ~m1_subset_1(B_4, k1_zfmisc_1(k1_zfmisc_1(A_3))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.38  tff(c_69, plain, (![A_31, B_32]: (m1_subset_1(k7_setfam_1(A_31, B_32), k1_zfmisc_1(k1_zfmisc_1(A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(k1_zfmisc_1(A_31))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.38  tff(c_10, plain, (![A_5, B_6]: (k5_setfam_1(A_5, B_6)=k3_tarski(B_6) | ~m1_subset_1(B_6, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.38  tff(c_87, plain, (![A_35, B_36]: (k5_setfam_1(A_35, k7_setfam_1(A_35, B_36))=k3_tarski(k7_setfam_1(A_35, B_36)) | ~m1_subset_1(B_36, k1_zfmisc_1(k1_zfmisc_1(A_35))))), inference(resolution, [status(thm)], [c_69, c_10])).
% 2.72/1.38  tff(c_97, plain, (k5_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))=k3_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_87])).
% 2.72/1.38  tff(c_6, plain, (![A_1, B_2]: (m1_subset_1(k5_setfam_1(A_1, B_2), k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(k1_zfmisc_1(A_1))))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.38  tff(c_101, plain, (m1_subset_1(k3_tarski(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_97, c_6])).
% 2.72/1.38  tff(c_105, plain, (~m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_101])).
% 2.72/1.38  tff(c_108, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_8, c_105])).
% 2.72/1.38  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_108])).
% 2.72/1.38  tff(c_114, plain, (m1_subset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_101])).
% 2.72/1.38  tff(c_324, plain, (![A_57, B_58]: (v3_pre_topc(k6_setfam_1(u1_struct_0(A_57), B_58), A_57) | ~v1_finset_1(B_58) | ~v1_tops_2(B_58, A_57) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_57)))) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.72/1.38  tff(c_326, plain, (v3_pre_topc(k6_setfam_1(u1_struct_0('#skF_1'), k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')), '#skF_1') | ~v1_finset_1(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2')) | ~v1_tops_2(k7_setfam_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_114, c_324])).
% 2.72/1.38  tff(c_337, plain, (v3_pre_topc(k3_subset_1(u1_struct_0('#skF_1'), k3_tarski('#skF_2')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_209, c_179, c_274, c_326])).
% 2.72/1.38  tff(c_16, plain, (![B_13, A_11]: (v4_pre_topc(B_13, A_11) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_11), B_13), A_11) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.72/1.38  tff(c_345, plain, (v4_pre_topc(k3_tarski('#skF_2'), '#skF_1') | ~m1_subset_1(k3_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_337, c_16])).
% 2.72/1.38  tff(c_348, plain, (v4_pre_topc(k3_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_68, c_345])).
% 2.72/1.38  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_348])).
% 2.72/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.38  
% 2.72/1.38  Inference rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Ref     : 0
% 2.72/1.38  #Sup     : 63
% 2.72/1.38  #Fact    : 0
% 2.72/1.38  #Define  : 0
% 2.72/1.38  #Split   : 6
% 2.72/1.38  #Chain   : 0
% 2.72/1.38  #Close   : 0
% 2.72/1.38  
% 2.72/1.38  Ordering : KBO
% 2.72/1.38  
% 2.72/1.38  Simplification rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Subsume      : 0
% 2.72/1.38  #Demod        : 65
% 2.72/1.38  #Tautology    : 20
% 2.72/1.38  #SimpNegUnit  : 2
% 2.72/1.38  #BackRed      : 18
% 2.72/1.38  
% 2.72/1.38  #Partial instantiations: 0
% 2.72/1.38  #Strategies tried      : 1
% 2.72/1.38  
% 2.72/1.38  Timing (in seconds)
% 2.72/1.38  ----------------------
% 2.72/1.38  Preprocessing        : 0.33
% 2.72/1.38  Parsing              : 0.18
% 2.72/1.38  CNF conversion       : 0.02
% 2.72/1.38  Main loop            : 0.26
% 2.72/1.38  Inferencing          : 0.09
% 2.72/1.38  Reduction            : 0.09
% 2.72/1.38  Demodulation         : 0.06
% 2.72/1.38  BG Simplification    : 0.02
% 2.72/1.38  Subsumption          : 0.05
% 2.72/1.38  Abstraction          : 0.02
% 2.72/1.38  MUC search           : 0.00
% 2.72/1.38  Cooper               : 0.00
% 2.72/1.38  Total                : 0.63
% 2.72/1.38  Index Insertion      : 0.00
% 2.72/1.38  Index Deletion       : 0.00
% 2.72/1.38  Index Matching       : 0.00
% 2.72/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
