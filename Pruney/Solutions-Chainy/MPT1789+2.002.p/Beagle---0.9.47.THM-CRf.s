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
% DateTime   : Thu Dec  3 10:27:48 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
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

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( u1_struct_0(k6_tmap_1(A,B)) = u1_struct_0(A)
              & u1_pre_topc(k6_tmap_1(A,B)) = k5_tmap_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k6_tmap_1(A,B))
        & v2_pre_topc(k6_tmap_1(A,B))
        & l1_pre_topc(k6_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k5_tmap_1(A,B),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_tmap_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k6_tmap_1(A,B) = g1_pre_topc(u1_struct_0(A),k5_tmap_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_tmap_1)).

tff(f_40,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_45,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) != u1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_24,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_55,plain,(
    ! [A_25,B_26] :
      ( l1_pre_topc(k6_tmap_1(A_25,B_26))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_58,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_55])).

tff(c_61,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_58])).

tff(c_62,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_61])).

tff(c_63,plain,(
    ! [A_27,B_28] :
      ( v1_pre_topc(k6_tmap_1(A_27,B_28))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_63])).

tff(c_69,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_66])).

tff(c_70,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_69])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k5_tmap_1(A_11,B_12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11))))
      | ~ m1_subset_1(B_12,k1_zfmisc_1(u1_struct_0(A_11)))
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_107,plain,(
    ! [A_42,B_43] :
      ( g1_pre_topc(u1_struct_0(A_42),k5_tmap_1(A_42,B_43)) = k6_tmap_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

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

tff(c_6,plain,(
    ! [C_6,A_2,D_7,B_3] :
      ( C_6 = A_2
      | g1_pre_topc(C_6,D_7) != g1_pre_topc(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(k1_zfmisc_1(A_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_128,plain,(
    ! [C_6,D_7] :
      ( u1_struct_0('#skF_1') = C_6
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_6,D_7)
      | ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_6])).

tff(c_142,plain,(
    ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_145,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_142])).

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
    inference(resolution,[status(thm)],[c_70,c_188])).

tff(c_194,plain,(
    u1_struct_0(k6_tmap_1('#skF_1','#skF_2')) = u1_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_191])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_194])).

tff(c_197,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) != k5_tmap_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_237,plain,(
    ! [A_62,B_63] :
      ( l1_pre_topc(k6_tmap_1(A_62,B_63))
      | ~ m1_subset_1(B_63,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_243,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_237])).

tff(c_246,plain,
    ( l1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_243])).

tff(c_247,plain,(
    l1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_246])).

tff(c_343,plain,(
    ! [A_87,B_88] :
      ( g1_pre_topc(u1_struct_0(A_87),k5_tmap_1(A_87,B_88)) = k6_tmap_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_347,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_343])).

tff(c_352,plain,
    ( g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_347])).

tff(c_353,plain,(
    g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')) = k6_tmap_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_352])).

tff(c_215,plain,(
    ! [A_58,B_59] :
      ( v1_pre_topc(k6_tmap_1(A_58,B_59))
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0(A_58)))
      | ~ l1_pre_topc(A_58)
      | ~ v2_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_221,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_215])).

tff(c_224,plain,
    ( v1_pre_topc(k6_tmap_1('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_221])).

tff(c_225,plain,(
    v1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_224])).

tff(c_370,plain,(
    ! [C_6,D_7] :
      ( u1_struct_0('#skF_1') = C_6
      | k6_tmap_1('#skF_1','#skF_2') != g1_pre_topc(C_6,D_7)
      | ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_6])).

tff(c_379,plain,(
    ~ m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_382,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_10,c_379])).

tff(c_385,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_20,c_382])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_385])).

tff(c_389,plain,(
    m1_subset_1(k5_tmap_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_210,plain,(
    ! [D_54,B_55,C_56,A_57] :
      ( D_54 = B_55
      | g1_pre_topc(C_56,D_54) != g1_pre_topc(A_57,B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_212,plain,(
    ! [A_1,B_55,A_57] :
      ( u1_pre_topc(A_1) = B_55
      | g1_pre_topc(A_57,B_55) != A_1
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_57)))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_210])).

tff(c_251,plain,(
    ! [A_57,B_55] :
      ( u1_pre_topc(g1_pre_topc(A_57,B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_57)))
      | ~ v1_pre_topc(g1_pre_topc(A_57,B_55))
      | ~ l1_pre_topc(g1_pre_topc(A_57,B_55)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_212])).

tff(c_399,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2'))) = k5_tmap_1('#skF_1','#skF_2')
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'),k5_tmap_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_389,c_251])).

tff(c_415,plain,(
    u1_pre_topc(k6_tmap_1('#skF_1','#skF_2')) = k5_tmap_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_353,c_225,c_353,c_353,c_399])).

tff(c_417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_197,c_415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:02:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.33  
% 2.53/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.33  %$ m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k6_tmap_1 > k5_tmap_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.53/1.33  
% 2.53/1.33  %Foreground sorts:
% 2.53/1.33  
% 2.53/1.33  
% 2.53/1.33  %Background operators:
% 2.53/1.33  
% 2.53/1.33  
% 2.53/1.33  %Foreground operators:
% 2.53/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.53/1.33  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.33  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 2.53/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.53/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.33  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.53/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.33  tff(k6_tmap_1, type, k6_tmap_1: ($i * $i) > $i).
% 2.53/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.33  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.53/1.33  tff(k5_tmap_1, type, k5_tmap_1: ($i * $i) > $i).
% 2.53/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.53/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.33  
% 2.53/1.35  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((u1_struct_0(k6_tmap_1(A, B)) = u1_struct_0(A)) & (u1_pre_topc(k6_tmap_1(A, B)) = k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_tmap_1)).
% 2.53/1.35  tff(f_78, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ((v1_pre_topc(k6_tmap_1(A, B)) & v2_pre_topc(k6_tmap_1(A, B))) & l1_pre_topc(k6_tmap_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 2.53/1.35  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 2.53/1.35  tff(f_63, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k5_tmap_1(A, B), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_tmap_1)).
% 2.53/1.35  tff(f_52, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k6_tmap_1(A, B) = g1_pre_topc(u1_struct_0(A), k5_tmap_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_tmap_1)).
% 2.53/1.35  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 2.53/1.35  tff(c_18, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))!=k5_tmap_1('#skF_1', '#skF_2') | u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.35  tff(c_45, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))!=u1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_18])).
% 2.53/1.35  tff(c_26, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.35  tff(c_24, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.35  tff(c_22, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.35  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.53/1.35  tff(c_55, plain, (![A_25, B_26]: (l1_pre_topc(k6_tmap_1(A_25, B_26)) | ~m1_subset_1(B_26, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_58, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_55])).
% 2.53/1.35  tff(c_61, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_58])).
% 2.53/1.35  tff(c_62, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_61])).
% 2.53/1.35  tff(c_63, plain, (![A_27, B_28]: (v1_pre_topc(k6_tmap_1(A_27, B_28)) | ~m1_subset_1(B_28, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27) | ~v2_pre_topc(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_66, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_63])).
% 2.53/1.35  tff(c_69, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_66])).
% 2.53/1.35  tff(c_70, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_69])).
% 2.53/1.35  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.53/1.35  tff(c_10, plain, (![A_11, B_12]: (m1_subset_1(k5_tmap_1(A_11, B_12), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_11)))) | ~m1_subset_1(B_12, k1_zfmisc_1(u1_struct_0(A_11))) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.53/1.35  tff(c_107, plain, (![A_42, B_43]: (g1_pre_topc(u1_struct_0(A_42), k5_tmap_1(A_42, B_43))=k6_tmap_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(u1_struct_0(A_42))) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.35  tff(c_109, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_107])).
% 2.53/1.35  tff(c_112, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_109])).
% 2.53/1.35  tff(c_113, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_112])).
% 2.53/1.35  tff(c_6, plain, (![C_6, A_2, D_7, B_3]: (C_6=A_2 | g1_pre_topc(C_6, D_7)!=g1_pre_topc(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(k1_zfmisc_1(A_2))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.35  tff(c_128, plain, (![C_6, D_7]: (u1_struct_0('#skF_1')=C_6 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_6, D_7) | ~m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_113, c_6])).
% 2.53/1.35  tff(c_142, plain, (~m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_128])).
% 2.53/1.35  tff(c_145, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_142])).
% 2.53/1.35  tff(c_148, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_145])).
% 2.53/1.35  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_148])).
% 2.53/1.35  tff(c_178, plain, (![C_51, D_52]: (u1_struct_0('#skF_1')=C_51 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_51, D_52))), inference(splitRight, [status(thm)], [c_128])).
% 2.53/1.35  tff(c_188, plain, (![A_53]: (u1_struct_0(A_53)=u1_struct_0('#skF_1') | k6_tmap_1('#skF_1', '#skF_2')!=A_53 | ~v1_pre_topc(A_53) | ~l1_pre_topc(A_53))), inference(superposition, [status(thm), theory('equality')], [c_2, c_178])).
% 2.53/1.35  tff(c_191, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1') | ~l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_188])).
% 2.53/1.35  tff(c_194, plain, (u1_struct_0(k6_tmap_1('#skF_1', '#skF_2'))=u1_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_191])).
% 2.53/1.35  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_194])).
% 2.53/1.35  tff(c_197, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))!=k5_tmap_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 2.53/1.35  tff(c_237, plain, (![A_62, B_63]: (l1_pre_topc(k6_tmap_1(A_62, B_63)) | ~m1_subset_1(B_63, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_243, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_237])).
% 2.53/1.35  tff(c_246, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_243])).
% 2.53/1.35  tff(c_247, plain, (l1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_246])).
% 2.53/1.35  tff(c_343, plain, (![A_87, B_88]: (g1_pre_topc(u1_struct_0(A_87), k5_tmap_1(A_87, B_88))=k6_tmap_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.53/1.35  tff(c_347, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_343])).
% 2.53/1.35  tff(c_352, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_347])).
% 2.53/1.35  tff(c_353, plain, (g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))=k6_tmap_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_26, c_352])).
% 2.53/1.35  tff(c_215, plain, (![A_58, B_59]: (v1_pre_topc(k6_tmap_1(A_58, B_59)) | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0(A_58))) | ~l1_pre_topc(A_58) | ~v2_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.53/1.35  tff(c_221, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_20, c_215])).
% 2.53/1.35  tff(c_224, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_221])).
% 2.53/1.35  tff(c_225, plain, (v1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_26, c_224])).
% 2.53/1.35  tff(c_370, plain, (![C_6, D_7]: (u1_struct_0('#skF_1')=C_6 | k6_tmap_1('#skF_1', '#skF_2')!=g1_pre_topc(C_6, D_7) | ~m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1')))))), inference(superposition, [status(thm), theory('equality')], [c_353, c_6])).
% 2.53/1.35  tff(c_379, plain, (~m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitLeft, [status(thm)], [c_370])).
% 2.53/1.35  tff(c_382, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_10, c_379])).
% 2.53/1.35  tff(c_385, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_20, c_382])).
% 2.53/1.35  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_385])).
% 2.53/1.35  tff(c_389, plain, (m1_subset_1(k5_tmap_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(splitRight, [status(thm)], [c_370])).
% 2.53/1.35  tff(c_210, plain, (![D_54, B_55, C_56, A_57]: (D_54=B_55 | g1_pre_topc(C_56, D_54)!=g1_pre_topc(A_57, B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.53/1.35  tff(c_212, plain, (![A_1, B_55, A_57]: (u1_pre_topc(A_1)=B_55 | g1_pre_topc(A_57, B_55)!=A_1 | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_57))) | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_210])).
% 2.53/1.35  tff(c_251, plain, (![A_57, B_55]: (u1_pre_topc(g1_pre_topc(A_57, B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_57))) | ~v1_pre_topc(g1_pre_topc(A_57, B_55)) | ~l1_pre_topc(g1_pre_topc(A_57, B_55)))), inference(reflexivity, [status(thm), theory('equality')], [c_212])).
% 2.53/1.35  tff(c_399, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2')))=k5_tmap_1('#skF_1', '#skF_2') | ~v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_1'), k5_tmap_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_389, c_251])).
% 2.53/1.35  tff(c_415, plain, (u1_pre_topc(k6_tmap_1('#skF_1', '#skF_2'))=k5_tmap_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_353, c_225, c_353, c_353, c_399])).
% 2.53/1.35  tff(c_417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_197, c_415])).
% 2.53/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.35  
% 2.53/1.35  Inference rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Ref     : 11
% 2.53/1.35  #Sup     : 82
% 2.53/1.35  #Fact    : 0
% 2.53/1.35  #Define  : 0
% 2.53/1.35  #Split   : 6
% 2.53/1.35  #Chain   : 0
% 2.53/1.35  #Close   : 0
% 2.53/1.35  
% 2.53/1.35  Ordering : KBO
% 2.53/1.35  
% 2.53/1.35  Simplification rules
% 2.53/1.35  ----------------------
% 2.53/1.35  #Subsume      : 4
% 2.53/1.35  #Demod        : 52
% 2.53/1.35  #Tautology    : 28
% 2.53/1.35  #SimpNegUnit  : 12
% 2.53/1.35  #BackRed      : 0
% 2.53/1.35  
% 2.53/1.35  #Partial instantiations: 0
% 2.53/1.35  #Strategies tried      : 1
% 2.53/1.35  
% 2.53/1.35  Timing (in seconds)
% 2.53/1.35  ----------------------
% 2.53/1.35  Preprocessing        : 0.29
% 2.53/1.35  Parsing              : 0.16
% 2.53/1.35  CNF conversion       : 0.02
% 2.53/1.35  Main loop            : 0.29
% 2.53/1.35  Inferencing          : 0.11
% 2.53/1.35  Reduction            : 0.08
% 2.53/1.35  Demodulation         : 0.05
% 2.53/1.35  BG Simplification    : 0.02
% 2.53/1.35  Subsumption          : 0.06
% 2.53/1.35  Abstraction          : 0.01
% 2.53/1.35  MUC search           : 0.00
% 2.53/1.35  Cooper               : 0.00
% 2.53/1.35  Total                : 0.61
% 2.53/1.35  Index Insertion      : 0.00
% 2.53/1.35  Index Deletion       : 0.00
% 2.53/1.35  Index Matching       : 0.00
% 2.53/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
