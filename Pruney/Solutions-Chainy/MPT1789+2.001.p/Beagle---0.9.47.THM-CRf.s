%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:48 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 358 expanded)
%              Number of leaves         :   22 ( 138 expanded)
%              Depth                    :    9
%              Number of atoms          :  230 (1138 expanded)
%              Number of equality atoms :   51 ( 326 expanded)
%              Maximal formula depth    :    9 (   4 average)
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

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
              & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k5_tmap_1(A,B),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(c_16,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) != k5_tmap_1('#skF_1','#skF_2')
    | u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_24,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_107,plain,(
    ! [A_49,B_50] :
      ( g1_pre_topc(u1_struct_0(A_49),k5_tmap_1(A_49,B_50)) = k6_tmap_1(A_49,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49)
      | ~ v2_pre_topc(A_49)
      | v2_struct_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_107])).

tff(c_112,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_109])).

tff(c_113,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_112])).

tff(c_91,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k5_tmap_1(A_41,B_42),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41))))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( l1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [A_41,B_42] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_41),k5_tmap_1(A_41,B_42)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_91,c_4])).

tff(c_120,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_98])).

tff(c_143,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_120])).

tff(c_144,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_143])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_pre_topc(g1_pre_topc(A_2,B_3))
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_99,plain,(
    ! [A_41,B_42] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_41),k5_tmap_1(A_41,B_42)))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(u1_struct_0(A_41)))
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_91,c_6])).

tff(c_117,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_99])).

tff(c_140,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_117])).

tff(c_141,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_140])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k5_tmap_1(A_13,B_14),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13))))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(u1_struct_0(A_13)))
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [C_8,A_4,D_9,B_5] :
      ( C_8 = A_4
      | g1_pre_topc(C_8,D_9) != g1_pre_topc(A_4,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,(
    ! [C_8,D_9] :
      ( u1_struct_0('#skF_1') = C_8
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_8,D_9)
      | ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_10])).

tff(c_156,plain,(
    ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_159,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_156])).

tff(c_162,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_159])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_162])).

tff(c_166,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [C_25,A_26,D_27,B_28] :
      ( C_25 = A_26
      | g1_pre_topc(C_25,D_27) != g1_pre_topc(A_26,B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_52,plain,(
    ! [A_1,A_26,B_28] :
      ( u1_struct_0(A_1) = A_26
      | g1_pre_topc(A_26,B_28) != A_1
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_26)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_67,plain,(
    ! [A_26,B_28] :
      ( u1_struct_0(g1_pre_topc(A_26,B_28)) = A_26
      | ~ m1_subset_1(B_28,k1_zfmisc_1(k1_zfmisc_1(A_26)))
      | ~ v1_pre_topc(g1_pre_topc(A_26,B_28))
      | ~ l1_pre_topc(g1_pre_topc(A_26,B_28)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_52])).

tff(c_175,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2'))) = u1_struct_0('#skF_1')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_166,c_67])).

tff(c_192,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_113,c_141,c_113,c_113,c_175])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_192])).

tff(c_195,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) != k5_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_196,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_200,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_2])).

tff(c_240,plain,(
    ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_200])).

tff(c_292,plain,(
    ! [A_85,B_86] :
      ( g1_pre_topc(u1_struct_0(A_85),k5_tmap_1(A_85,B_86)) = k6_tmap_1(A_85,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85)
      | ~ v2_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_296,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_292])).

tff(c_300,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_296])).

tff(c_301,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_300])).

tff(c_241,plain,(
    ! [A_69,B_70] :
      ( m1_subset_1(k5_tmap_1(A_69,B_70),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69))))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_251,plain,(
    ! [A_69,B_70] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_69),k5_tmap_1(A_69,B_70)))
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_241,c_4])).

tff(c_305,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_251])).

tff(c_328,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_305])).

tff(c_330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_240,c_328])).

tff(c_332,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_515,plain,(
    ! [A_124,B_125] :
      ( g1_pre_topc(u1_struct_0(A_124),k5_tmap_1(A_124,B_125)) = k6_tmap_1(A_124,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124)
      | ~ v2_pre_topc(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_519,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_515])).

tff(c_524,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_519])).

tff(c_525,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_524])).

tff(c_331,plain,
    ( ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | g1_pre_topc(u1_struct_0('#skF_1'),u1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_200])).

tff(c_333,plain,(
    ~ v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_381,plain,(
    ! [A_101,B_102] :
      ( g1_pre_topc(u1_struct_0(A_101),k5_tmap_1(A_101,B_102)) = k6_tmap_1(A_101,B_102)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_385,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_381])).

tff(c_390,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_385])).

tff(c_391,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_390])).

tff(c_334,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1(k5_tmap_1(A_87,B_88),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87))))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_345,plain,(
    ! [A_87,B_88] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_87),k5_tmap_1(A_87,B_88)))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_334,c_6])).

tff(c_395,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_345])).

tff(c_418,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_395])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_333,c_418])).

tff(c_422,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_548,plain,(
    ! [C_8,D_9] :
      ( u1_struct_0('#skF_1') = C_8
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_8,D_9)
      | ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_10])).

tff(c_563,plain,(
    ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_548])).

tff(c_566,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_14,c_563])).

tff(c_569,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_18,c_566])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_569])).

tff(c_573,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_548])).

tff(c_217,plain,(
    ! [D_59,B_60,C_61,A_62] :
      ( D_59 = B_60
      | g1_pre_topc(C_61,D_59) != g1_pre_topc(A_62,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_219,plain,(
    ! [A_1,B_60,A_62] :
      ( u1_pre_topc(A_1) = B_60
      | g1_pre_topc(A_62,B_60) != A_1
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_62)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_217])).

tff(c_234,plain,(
    ! [A_62,B_60] :
      ( u1_pre_topc(g1_pre_topc(A_62,B_60)) = B_60
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_62)))
      | ~ v1_pre_topc(g1_pre_topc(A_62,B_60))
      | ~ l1_pre_topc(g1_pre_topc(A_62,B_60)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_219])).

tff(c_580,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2'))) = k5_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_573,c_234])).

tff(c_602,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_525,c_422,c_525,c_525,c_580])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.46  
% 2.68/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.46  %$ m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.68/1.46  
% 2.68/1.46  %Foreground sorts:
% 2.68/1.46  
% 2.68/1.46  
% 2.68/1.46  %Background operators:
% 2.68/1.46  
% 2.68/1.46  
% 2.68/1.46  %Foreground operators:
% 2.68/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.46  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.68/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.46  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.68/1.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.68/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.46  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.68/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.46  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.68/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.68/1.46  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.68/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.46  
% 3.04/1.48  tff(f_84, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 3.04/1.48  tff(f_58, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 3.04/1.48  tff(f_69, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k5_tmap_1(A, B), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_tmap_1)).
% 3.04/1.48  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 3.04/1.48  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.04/1.48  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.04/1.48  tff(c_16, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))!=k5_tmap_1('#skF_1', '#skF_2') | u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.04/1.48  tff(c_36, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_16])).
% 3.04/1.48  tff(c_24, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.04/1.48  tff(c_22, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.04/1.48  tff(c_20, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.04/1.48  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.04/1.48  tff(c_107, plain, (![A_49, B_50]: (g1_pre_topc(u1_struct_0(A_49), k5_tmap_1(A_49, B_50))=k6_tmap_1(A_49, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49) | ~v2_pre_topc(A_49) | v2_struct_0(A_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.04/1.48  tff(c_109, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_107])).
% 3.04/1.48  tff(c_112, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_109])).
% 3.04/1.48  tff(c_113, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_112])).
% 3.04/1.48  tff(c_91, plain, (![A_41, B_42]: (m1_subset_1(k5_tmap_1(A_41, B_42), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_41)))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.04/1.48  tff(c_4, plain, (![A_2, B_3]: (l1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.04/1.48  tff(c_98, plain, (![A_41, B_42]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_41), k5_tmap_1(A_41, B_42))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_91, c_4])).
% 3.04/1.48  tff(c_120, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_113, c_98])).
% 3.04/1.48  tff(c_143, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_120])).
% 3.04/1.48  tff(c_144, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_143])).
% 3.04/1.48  tff(c_6, plain, (![A_2, B_3]: (v1_pre_topc(g1_pre_topc(A_2, B_3)) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.04/1.48  tff(c_99, plain, (![A_41, B_42]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_41), k5_tmap_1(A_41, B_42))) | ~m1_subset_1(B_42, k1_zfmisc_1(u1_struct_0(A_41))) | ~l1_pre_topc(A_41) | ~v2_pre_topc(A_41) | v2_struct_0(A_41))), inference(resolution, [status(thm)], [c_91, c_6])).
% 3.04/1.48  tff(c_117, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_113, c_99])).
% 3.04/1.48  tff(c_140, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_117])).
% 3.04/1.48  tff(c_141, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_140])).
% 3.04/1.48  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(k5_tmap_1(A_13, B_14), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_13)))) | ~m1_subset_1(B_14, k1_zfmisc_1(u1_struct_0(A_13))) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.04/1.48  tff(c_10, plain, (![C_8, A_4, D_9, B_5]: (C_8=A_4 | g1_pre_topc(C_8, D_9)!=g1_pre_topc(A_4, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.04/1.48  tff(c_132, plain, (![C_8, D_9]: (u1_struct_0('#skF_1')=C_8 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_8, D_9) | ~m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_113, c_10])).
% 3.04/1.48  tff(c_156, plain, (~m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_132])).
% 3.04/1.48  tff(c_159, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_156])).
% 3.04/1.48  tff(c_162, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_159])).
% 3.04/1.48  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_162])).
% 3.04/1.48  tff(c_166, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_132])).
% 3.04/1.48  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.04/1.48  tff(c_50, plain, (![C_25, A_26, D_27, B_28]: (C_25=A_26 | g1_pre_topc(C_25, D_27)!=g1_pre_topc(A_26, B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.04/1.48  tff(c_52, plain, (![A_1, A_26, B_28]: (u1_struct_0(A_1)=A_26 | g1_pre_topc(A_26, B_28)!=A_1 | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_26))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_50])).
% 3.04/1.48  tff(c_67, plain, (![A_26, B_28]: (u1_struct_0(g1_pre_topc(A_26, B_28))=A_26 | ~m1_subset_1(B_28, k1_zfmisc_1(k1_zfmisc_1(A_26))) | ~v1_pre_topc(g1_pre_topc(A_26, B_28)) | ~l1_pre_topc(g1_pre_topc(A_26, B_28)))), inference(reflexivity, [status(thm), theory('equality')], [c_52])).
% 3.04/1.48  tff(c_175, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2')))=u1_struct_0('#skF_1') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_166, c_67])).
% 3.04/1.48  tff(c_192, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_113, c_141, c_113, c_113, c_175])).
% 3.04/1.48  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_192])).
% 3.04/1.48  tff(c_195, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))!=k5_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_16])).
% 3.04/1.48  tff(c_196, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_16])).
% 3.04/1.48  tff(c_200, plain, (g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_2])).
% 3.04/1.48  tff(c_240, plain, (~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_200])).
% 3.04/1.48  tff(c_292, plain, (![A_85, B_86]: (g1_pre_topc(u1_struct_0(A_85), k5_tmap_1(A_85, B_86))=k6_tmap_1(A_85, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85) | ~v2_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.04/1.48  tff(c_296, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_292])).
% 3.04/1.48  tff(c_300, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_296])).
% 3.04/1.48  tff(c_301, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_300])).
% 3.04/1.48  tff(c_241, plain, (![A_69, B_70]: (m1_subset_1(k5_tmap_1(A_69, B_70), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_69)))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.04/1.48  tff(c_251, plain, (![A_69, B_70]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_69), k5_tmap_1(A_69, B_70))) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(resolution, [status(thm)], [c_241, c_4])).
% 3.04/1.48  tff(c_305, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_301, c_251])).
% 3.04/1.48  tff(c_328, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_305])).
% 3.04/1.48  tff(c_330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_240, c_328])).
% 3.04/1.48  tff(c_332, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_200])).
% 3.04/1.48  tff(c_515, plain, (![A_124, B_125]: (g1_pre_topc(u1_struct_0(A_124), k5_tmap_1(A_124, B_125))=k6_tmap_1(A_124, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124) | ~v2_pre_topc(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.04/1.48  tff(c_519, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_515])).
% 3.04/1.48  tff(c_524, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_519])).
% 3.04/1.48  tff(c_525, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_524])).
% 3.04/1.48  tff(c_331, plain, (~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | g1_pre_topc(u1_struct_0('#skF_1'), u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')))=k6_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_200])).
% 3.04/1.48  tff(c_333, plain, (~v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_331])).
% 3.04/1.48  tff(c_381, plain, (![A_101, B_102]: (g1_pre_topc(u1_struct_0(A_101), k5_tmap_1(A_101, B_102))=k6_tmap_1(A_101, B_102) | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.04/1.48  tff(c_385, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_381])).
% 3.04/1.48  tff(c_390, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_385])).
% 3.04/1.48  tff(c_391, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_24, c_390])).
% 3.04/1.48  tff(c_334, plain, (![A_87, B_88]: (m1_subset_1(k5_tmap_1(A_87, B_88), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_87)))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.04/1.48  tff(c_345, plain, (![A_87, B_88]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_87), k5_tmap_1(A_87, B_88))) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(resolution, [status(thm)], [c_334, c_6])).
% 3.04/1.48  tff(c_395, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_391, c_345])).
% 3.04/1.48  tff(c_418, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_395])).
% 3.04/1.48  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_333, c_418])).
% 3.04/1.48  tff(c_422, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_331])).
% 3.04/1.48  tff(c_548, plain, (![C_8, D_9]: (u1_struct_0('#skF_1')=C_8 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_8, D_9) | ~m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_525, c_10])).
% 3.04/1.48  tff(c_563, plain, (~m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_548])).
% 3.04/1.48  tff(c_566, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_14, c_563])).
% 3.04/1.48  tff(c_569, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_18, c_566])).
% 3.04/1.48  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_569])).
% 3.04/1.48  tff(c_573, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_548])).
% 3.04/1.48  tff(c_217, plain, (![D_59, B_60, C_61, A_62]: (D_59=B_60 | g1_pre_topc(C_61, D_59)!=g1_pre_topc(A_62, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.04/1.48  tff(c_219, plain, (![A_1, B_60, A_62]: (u1_pre_topc(A_1)=B_60 | g1_pre_topc(A_62, B_60)!=A_1 | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_62))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_217])).
% 3.04/1.48  tff(c_234, plain, (![A_62, B_60]: (u1_pre_topc(g1_pre_topc(A_62, B_60))=B_60 | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_62))) | ~v1_pre_topc(g1_pre_topc(A_62, B_60)) | ~l1_pre_topc(g1_pre_topc(A_62, B_60)))), inference(reflexivity, [status(thm), theory('equality')], [c_219])).
% 3.04/1.48  tff(c_580, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2')))=k5_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_573, c_234])).
% 3.04/1.48  tff(c_602, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_525, c_422, c_525, c_525, c_580])).
% 3.04/1.48  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_602])).
% 3.04/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/1.48  
% 3.04/1.48  Inference rules
% 3.04/1.48  ----------------------
% 3.04/1.48  #Ref     : 16
% 3.04/1.48  #Sup     : 133
% 3.04/1.48  #Fact    : 0
% 3.04/1.48  #Define  : 0
% 3.04/1.48  #Split   : 8
% 3.04/1.48  #Chain   : 0
% 3.04/1.48  #Close   : 0
% 3.04/1.48  
% 3.04/1.48  Ordering : KBO
% 3.04/1.48  
% 3.04/1.48  Simplification rules
% 3.04/1.48  ----------------------
% 3.04/1.48  #Subsume      : 9
% 3.04/1.48  #Demod        : 70
% 3.04/1.48  #Tautology    : 33
% 3.04/1.48  #SimpNegUnit  : 14
% 3.04/1.48  #BackRed      : 0
% 3.04/1.48  
% 3.04/1.48  #Partial instantiations: 0
% 3.04/1.48  #Strategies tried      : 1
% 3.04/1.48  
% 3.04/1.48  Timing (in seconds)
% 3.04/1.48  ----------------------
% 3.04/1.48  Preprocessing        : 0.31
% 3.04/1.48  Parsing              : 0.17
% 3.04/1.48  CNF conversion       : 0.02
% 3.04/1.48  Main loop            : 0.36
% 3.04/1.48  Inferencing          : 0.14
% 3.04/1.48  Reduction            : 0.10
% 3.04/1.48  Demodulation         : 0.07
% 3.04/1.48  BG Simplification    : 0.02
% 3.04/1.48  Subsumption          : 0.08
% 3.04/1.48  Abstraction          : 0.02
% 3.04/1.48  MUC search           : 0.00
% 3.04/1.48  Cooper               : 0.00
% 3.04/1.48  Total                : 0.71
% 3.04/1.48  Index Insertion      : 0.00
% 3.04/1.48  Index Deletion       : 0.00
% 3.04/1.48  Index Matching       : 0.00
% 3.04/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
