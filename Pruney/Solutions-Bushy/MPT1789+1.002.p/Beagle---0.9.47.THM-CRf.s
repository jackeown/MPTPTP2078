%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1789+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:23 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 222 expanded)
%              Number of leaves         :   22 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  169 ( 695 expanded)
%              Number of equality atoms :   39 ( 197 expanded)
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

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
              & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k5_tmap_1(A,B),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(c_18,plain,
    ( u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) != k5_tmap_1('#skF_1','#skF_2')
    | u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_54,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_63,plain,(
    ! [A_27,B_28] :
      ( l1_pre_topc(k6_tmap_1(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_66,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_69,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_66])).

tff(c_70,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_69])).

tff(c_71,plain,(
    ! [A_29,B_30] :
      ( v1_pre_topc(k6_tmap_1(A_29,B_30))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_74,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_77,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_74])).

tff(c_78,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_77])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k5_tmap_1(A_5,B_6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_5))))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    ! [A_42,B_43] :
      ( g1_pre_topc(u1_struct_0(A_42),k5_tmap_1(A_42,B_43)) = k6_tmap_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_109,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_107])).

tff(c_112,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_109])).

tff(c_113,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_112])).

tff(c_16,plain,(
    ! [C_13,A_9,D_14,B_10] :
      ( C_13 = A_9
      | g1_pre_topc(C_13,D_14) != g1_pre_topc(A_9,B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0('#skF_1') = C_13
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_13,D_14)
      | ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_16])).

tff(c_142,plain,(
    ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_145,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_148,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_145])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_148])).

tff(c_178,plain,(
    ! [C_51,D_52] :
      ( u1_struct_0('#skF_1') = C_51
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_51,D_52) ) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_188,plain,(
    ! [A_53] :
      ( u1_struct_0(A_53) = u1_struct_0('#skF_1')
      | k6_tmap_1('#skF_1','#skF_2') != A_53
      | ~ v1_pre_topc(A_53)
      | ~ l1_pre_topc(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_191,plain,
    ( u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1')
    | ~ l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_188])).

tff(c_194,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_191])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_194])).

tff(c_197,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) != k5_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_206,plain,(
    ! [A_54,B_55] :
      ( l1_pre_topc(k6_tmap_1(A_54,B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_pre_topc(A_54)
      | ~ v2_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_212,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_206])).

tff(c_215,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_212])).

tff(c_216,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_215])).

tff(c_340,plain,(
    ! [A_83,B_84] :
      ( g1_pre_topc(u1_struct_0(A_83),k5_tmap_1(A_83,B_84)) = k6_tmap_1(A_83,B_84)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_344,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_340])).

tff(c_349,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_344])).

tff(c_350,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_349])).

tff(c_217,plain,(
    ! [A_56,B_57] :
      ( v1_pre_topc(k6_tmap_1(A_56,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(u1_struct_0(A_56)))
      | ~ l1_pre_topc(A_56)
      | ~ v2_pre_topc(A_56)
      | v2_struct_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_223,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_217])).

tff(c_228,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_223])).

tff(c_229,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_228])).

tff(c_367,plain,(
    ! [C_13,D_14] :
      ( u1_struct_0('#skF_1') = C_13
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_13,D_14)
      | ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_16])).

tff(c_376,plain,(
    ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_380,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_376])).

tff(c_383,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_380])).

tff(c_385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_383])).

tff(c_387,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_49,plain,(
    ! [D_21,B_22,C_23,A_24] :
      ( D_21 = B_22
      | g1_pre_topc(C_23,D_21) != g1_pre_topc(A_24,B_22)
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_51,plain,(
    ! [A_1,B_22,A_24] :
      ( u1_pre_topc(A_1) = B_22
      | g1_pre_topc(A_24,B_22) != A_1
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_24)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_49])).

tff(c_245,plain,(
    ! [A_24,B_22] :
      ( u1_pre_topc(g1_pre_topc(A_24,B_22)) = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_24)))
      | ~ v1_pre_topc(g1_pre_topc(A_24,B_22))
      | ~ l1_pre_topc(g1_pre_topc(A_24,B_22)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_51])).

tff(c_393,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2'))) = k5_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_387,c_245])).

tff(c_409,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_216,c_350,c_229,c_350,c_350,c_393])).

tff(c_411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_409])).

%------------------------------------------------------------------------------
