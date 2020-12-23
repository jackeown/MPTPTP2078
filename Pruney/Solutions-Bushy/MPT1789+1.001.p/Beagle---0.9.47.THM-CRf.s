%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1789+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:23 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 163 expanded)
%              Number of leaves         :   22 (  64 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 ( 452 expanded)
%              Number of equality atoms :   41 ( 135 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_tmap_1,type,(
    k6_tmap_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k5_tmap_1,type,(
    k5_tmap_1: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
              & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_18,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) != k5_tmap_1('#skF_1','#skF_2')
    | u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_72,plain,(
    ! [A_29,B_30] :
      ( l1_pre_topc(k6_tmap_1(A_29,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_75,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_72])).

tff(c_78,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_75])).

tff(c_79,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_78])).

tff(c_64,plain,(
    ! [A_27,B_28] :
      ( v1_pre_topc(k6_tmap_1(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_67,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_70,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_67])).

tff(c_71,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_70])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_12,plain,(
    ! [A_7] :
      ( m1_subset_1(u1_pre_topc(A_7),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_7))))
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_80,plain,(
    ! [A_31,B_32] :
      ( g1_pre_topc(u1_struct_0(A_31),k5_tmap_1(A_31,B_32)) = k6_tmap_1(A_31,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_85,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_82])).

tff(c_86,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_85])).

tff(c_16,plain,(
    ! [C_12,A_8,D_13,B_9] :
      ( C_12 = A_8
      | g1_pre_topc(C_12,D_13) != g1_pre_topc(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_99,plain,(
    ! [A_33,B_34] :
      ( u1_struct_0('#skF_1') = A_33
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_16])).

tff(c_109,plain,(
    ! [A_37] :
      ( u1_struct_0(A_37) = u1_struct_0('#skF_1')
      | g1_pre_topc(u1_struct_0(A_37),u1_pre_topc(A_37)) != k6_tmap_1('#skF_1','#skF_2')
      | ~ l1_pre_topc(A_37) ) ),
    inference(resolution,[status(thm)],[c_12,c_99])).

tff(c_114,plain,(
    ! [A_38] :
      ( u1_struct_0(A_38) = u1_struct_0('#skF_1')
      | k6_tmap_1('#skF_1','#skF_2') != A_38
      | ~ l1_pre_topc(A_38)
      | ~ v1_pre_topc(A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_109])).

tff(c_117,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_71,c_114])).

tff(c_120,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_117])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_120])).

tff(c_123,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) != k5_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_313,plain,(
    ! [A_65,B_66] :
      ( g1_pre_topc(u1_struct_0(A_65),k5_tmap_1(A_65,B_66)) = k6_tmap_1(A_65,B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(u1_struct_0(A_65)))
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_317,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_313])).

tff(c_322,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_317])).

tff(c_323,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_322])).

tff(c_124,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_131,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_12])).

tff(c_135,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_147,plain,(
    ! [A_41,B_42] :
      ( l1_pre_topc(k6_tmap_1(A_41,B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_153,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_147])).

tff(c_156,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_135,c_156])).

tff(c_159,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_160,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_128,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_2])).

tff(c_161,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_161])).

tff(c_164,plain,
    ( ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_180,plain,(
    ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_194,plain,(
    ! [A_47,B_48] :
      ( v1_pre_topc(k6_tmap_1(A_47,B_48))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_200,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_194])).

tff(c_205,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_200])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_180,c_205])).

tff(c_208,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_14,plain,(
    ! [D_13,B_9,C_12,A_8] :
      ( D_13 = B_9
      | g1_pre_topc(C_12,D_13) != g1_pre_topc(A_8,B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_218,plain,(
    ! [D_13,C_12] :
      ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = D_13
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_12,D_13)
      | ~ m1_subset_1(u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_14])).

tff(c_224,plain,(
    ! [D_13,C_12] :
      ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = D_13
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_12,D_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_218])).

tff(c_330,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_224])).

tff(c_347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_330])).

%------------------------------------------------------------------------------
