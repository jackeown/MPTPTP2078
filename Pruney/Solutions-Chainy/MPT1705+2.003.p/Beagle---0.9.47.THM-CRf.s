%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:24 EST 2020

% Result     : Theorem 3.94s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 900 expanded)
%              Number of leaves         :   25 ( 294 expanded)
%              Depth                    :   16
%              Number of atoms          :  360 (3530 expanded)
%              Number of equality atoms :   49 ( 810 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ( C = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                 => ( ( v1_tsep_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_tsep_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_30,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_26,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_34,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_32,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1205,plain,(
    ! [C_208,A_209] :
      ( m1_pre_topc(C_208,A_209)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_208),u1_pre_topc(C_208)),A_209)
      | ~ l1_pre_topc(C_208)
      | ~ v2_pre_topc(C_208)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_208),u1_pre_topc(C_208)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_208),u1_pre_topc(C_208)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1214,plain,(
    ! [A_209] :
      ( m1_pre_topc('#skF_2',A_209)
      | ~ m1_pre_topc('#skF_3',A_209)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_209) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1205])).

tff(c_1218,plain,(
    ! [A_210] :
      ( m1_pre_topc('#skF_2',A_210)
      | ~ m1_pre_topc('#skF_3',A_210)
      | ~ l1_pre_topc(A_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_28,c_26,c_34,c_32,c_1214])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [B_37,A_38] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_37),u1_pre_topc(B_37)))
      | ~ m1_pre_topc(B_37,A_38)
      | ~ l1_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_93,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_91])).

tff(c_96,plain,(
    v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_93])).

tff(c_4,plain,(
    ! [A_2] :
      ( m1_subset_1(u1_pre_topc(A_2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2))))
      | ~ l1_pre_topc(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_116,plain,(
    ! [C_41,A_42,D_43,B_44] :
      ( C_41 = A_42
      | g1_pre_topc(C_41,D_43) != g1_pre_topc(A_42,B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_124,plain,(
    ! [C_41,D_43] :
      ( u1_struct_0('#skF_2') = C_41
      | g1_pre_topc(C_41,D_43) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_116])).

tff(c_142,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_145,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_149,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_145])).

tff(c_151,plain,(
    m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_171,plain,(
    ! [D_52,B_53,C_54,A_55] :
      ( D_52 = B_53
      | g1_pre_topc(C_54,D_52) != g1_pre_topc(A_55,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_179,plain,(
    ! [D_52,C_54] :
      ( u1_pre_topc('#skF_2') = D_52
      | g1_pre_topc(C_54,D_52) != '#skF_3'
      | ~ m1_subset_1(u1_pre_topc('#skF_2'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_171])).

tff(c_182,plain,(
    ! [D_56,C_57] :
      ( u1_pre_topc('#skF_2') = D_56
      | g1_pre_topc(C_57,D_56) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_179])).

tff(c_192,plain,(
    ! [A_58] :
      ( u1_pre_topc(A_58) = u1_pre_topc('#skF_2')
      | A_58 != '#skF_3'
      | ~ v1_pre_topc(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_182])).

tff(c_196,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = u1_pre_topc('#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != '#skF_3'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_96,c_192])).

tff(c_197,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_196])).

tff(c_200,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_197])).

tff(c_202,plain,(
    ~ v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_200])).

tff(c_321,plain,(
    ! [C_85,A_86] :
      ( m1_pre_topc(C_85,A_86)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_85),u1_pre_topc(C_85)),A_86)
      | ~ l1_pre_topc(C_85)
      | ~ v2_pre_topc(C_85)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_85),u1_pre_topc(C_85)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_85),u1_pre_topc(C_85)))
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_330,plain,(
    ! [A_86] :
      ( m1_pre_topc('#skF_2',A_86)
      | ~ m1_pre_topc('#skF_3',A_86)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_321])).

tff(c_334,plain,(
    ! [A_87] :
      ( m1_pre_topc('#skF_2',A_87)
      | ~ m1_pre_topc('#skF_3',A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_28,c_26,c_34,c_32,c_330])).

tff(c_12,plain,(
    ! [B_11,A_9] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_11),u1_pre_topc(B_11)))
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_341,plain,(
    ! [A_87] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc('#skF_3',A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(resolution,[status(thm)],[c_334,c_12])).

tff(c_346,plain,(
    ! [A_87] :
      ( v1_pre_topc('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_341])).

tff(c_348,plain,(
    ! [A_88] :
      ( ~ m1_pre_topc('#skF_3',A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_346])).

tff(c_351,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_348])).

tff(c_355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_351])).

tff(c_357,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_196])).

tff(c_152,plain,(
    ! [C_49,D_50] :
      ( u1_struct_0('#skF_2') = C_49
      | g1_pre_topc(C_49,D_50) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_162,plain,(
    ! [A_51] :
      ( u1_struct_0(A_51) = u1_struct_0('#skF_2')
      | A_51 != '#skF_3'
      | ~ v1_pre_topc(A_51)
      | ~ l1_pre_topc(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_152])).

tff(c_166,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = u1_struct_0('#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != '#skF_3'
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_96,c_162])).

tff(c_364,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) = u1_struct_0('#skF_2')
    | g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_166])).

tff(c_365,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_368,plain,
    ( ~ v1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_365])).

tff(c_371,plain,(
    ~ v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_368])).

tff(c_486,plain,(
    ! [C_115,A_116] :
      ( m1_pre_topc(C_115,A_116)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_115),u1_pre_topc(C_115)),A_116)
      | ~ l1_pre_topc(C_115)
      | ~ v2_pre_topc(C_115)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_115),u1_pre_topc(C_115)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_115),u1_pre_topc(C_115)))
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_495,plain,(
    ! [A_116] :
      ( m1_pre_topc('#skF_2',A_116)
      | ~ m1_pre_topc('#skF_3',A_116)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_486])).

tff(c_499,plain,(
    ! [A_117] :
      ( m1_pre_topc('#skF_2',A_117)
      | ~ m1_pre_topc('#skF_3',A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_28,c_26,c_34,c_32,c_495])).

tff(c_506,plain,(
    ! [A_117] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc('#skF_3',A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(resolution,[status(thm)],[c_499,c_12])).

tff(c_511,plain,(
    ! [A_117] :
      ( v1_pre_topc('#skF_3')
      | ~ m1_pre_topc('#skF_3',A_117)
      | ~ l1_pre_topc(A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_506])).

tff(c_513,plain,(
    ! [A_118] :
      ( ~ m1_pre_topc('#skF_3',A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(negUnitSimplification,[status(thm)],[c_371,c_511])).

tff(c_516,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_513])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_516])).

tff(c_522,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_150,plain,(
    ! [C_41,D_43] :
      ( u1_struct_0('#skF_2') = C_41
      | g1_pre_topc(C_41,D_43) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_553,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_150])).

tff(c_181,plain,(
    ! [D_52,C_54] :
      ( u1_pre_topc('#skF_2') = D_52
      | g1_pre_topc(C_54,D_52) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_179])).

tff(c_552,plain,(
    u1_pre_topc('#skF_2') = u1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_522,c_181])).

tff(c_730,plain,(
    ! [C_133,A_134] :
      ( m1_pre_topc(C_133,A_134)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_133),u1_pre_topc(C_133)),A_134)
      | ~ l1_pre_topc(C_133)
      | ~ v2_pre_topc(C_133)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_133),u1_pre_topc(C_133)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_133),u1_pre_topc(C_133)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_733,plain,(
    ! [A_134] :
      ( m1_pre_topc('#skF_2',A_134)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_2')),A_134)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_730])).

tff(c_747,plain,(
    ! [A_134] :
      ( m1_pre_topc('#skF_2',A_134)
      | ~ m1_pre_topc('#skF_3',A_134)
      | ~ l1_pre_topc(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_522,c_553,c_552,c_28,c_522,c_553,c_552,c_34,c_32,c_522,c_552,c_733])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_56,plain,
    ( v1_tsep_1('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_57,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_24,plain,(
    ! [B_28,A_26] :
      ( m1_subset_1(u1_struct_0(B_28),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_674,plain,(
    ! [B_127,A_128] :
      ( v3_pre_topc(u1_struct_0(B_127),A_128)
      | ~ v1_tsep_1(B_127,A_128)
      | ~ m1_subset_1(u1_struct_0(B_127),k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_693,plain,(
    ! [B_28,A_26] :
      ( v3_pre_topc(u1_struct_0(B_28),A_26)
      | ~ v1_tsep_1(B_28,A_26)
      | ~ v2_pre_topc(A_26)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_24,c_674])).

tff(c_627,plain,(
    ! [B_121,A_122] :
      ( v1_tsep_1(B_121,A_122)
      | ~ v3_pre_topc(u1_struct_0(B_121),A_122)
      | ~ m1_subset_1(u1_struct_0(B_121),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_770,plain,(
    ! [B_136,A_137] :
      ( v1_tsep_1(B_136,A_137)
      | ~ v3_pre_topc(u1_struct_0(B_136),A_137)
      | ~ v2_pre_topc(A_137)
      | ~ m1_pre_topc(B_136,A_137)
      | ~ l1_pre_topc(A_137) ) ),
    inference(resolution,[status(thm)],[c_24,c_627])).

tff(c_823,plain,(
    ! [A_144] :
      ( v1_tsep_1('#skF_2',A_144)
      | ~ v3_pre_topc(u1_struct_0('#skF_3'),A_144)
      | ~ v2_pre_topc(A_144)
      | ~ m1_pre_topc('#skF_2',A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_770])).

tff(c_948,plain,(
    ! [A_156] :
      ( v1_tsep_1('#skF_2',A_156)
      | ~ m1_pre_topc('#skF_2',A_156)
      | ~ v1_tsep_1('#skF_3',A_156)
      | ~ v2_pre_topc(A_156)
      | ~ m1_pre_topc('#skF_3',A_156)
      | ~ l1_pre_topc(A_156) ) ),
    inference(resolution,[status(thm)],[c_693,c_823])).

tff(c_40,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_88,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_58,c_40])).

tff(c_89,plain,(
    ~ v1_tsep_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_954,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_948,c_89])).

tff(c_958,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58,c_38,c_57,c_954])).

tff(c_961,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_747,c_958])).

tff(c_965,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58,c_961])).

tff(c_966,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1228,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1218,c_966])).

tff(c_1238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58,c_1228])).

tff(c_1240,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1239,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1277,plain,(
    ! [B_217,A_218] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_217),u1_pre_topc(B_217)),A_218)
      | ~ m1_pre_topc(B_217,A_218)
      | ~ l1_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1287,plain,(
    ! [A_219] :
      ( m1_pre_topc('#skF_3',A_219)
      | ~ m1_pre_topc('#skF_2',A_219)
      | ~ l1_pre_topc(A_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1277])).

tff(c_1290,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1239,c_1287])).

tff(c_1293,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1290])).

tff(c_1295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1240,c_1293])).

tff(c_1297,plain,(
    ~ v1_tsep_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1299,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1297,c_54])).

tff(c_1298,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1296,plain,(
    v1_tsep_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1326,plain,(
    ! [B_222,A_223] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_222),u1_pre_topc(B_222)))
      | ~ m1_pre_topc(B_222,A_223)
      | ~ l1_pre_topc(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1328,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1299,c_1326])).

tff(c_1333,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_1328])).

tff(c_1366,plain,(
    ! [C_229,A_230,D_231,B_232] :
      ( C_229 = A_230
      | g1_pre_topc(C_229,D_231) != g1_pre_topc(A_230,B_232)
      | ~ m1_subset_1(B_232,k1_zfmisc_1(k1_zfmisc_1(A_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1375,plain,(
    ! [A_233,B_234] :
      ( u1_struct_0('#skF_2') = A_233
      | g1_pre_topc(A_233,B_234) != '#skF_3'
      | ~ m1_subset_1(B_234,k1_zfmisc_1(k1_zfmisc_1(A_233))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1366])).

tff(c_1380,plain,(
    ! [A_235] :
      ( u1_struct_0(A_235) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_235),u1_pre_topc(A_235)) != '#skF_3'
      | ~ l1_pre_topc(A_235) ) ),
    inference(resolution,[status(thm)],[c_4,c_1375])).

tff(c_1421,plain,(
    ! [A_243] :
      ( u1_struct_0(A_243) = u1_struct_0('#skF_2')
      | A_243 != '#skF_3'
      | ~ l1_pre_topc(A_243)
      | ~ v1_pre_topc(A_243)
      | ~ l1_pre_topc(A_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1380])).

tff(c_1427,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1333,c_1421])).

tff(c_1431,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1427])).

tff(c_1599,plain,(
    ! [B_252,A_253] :
      ( v3_pre_topc(u1_struct_0(B_252),A_253)
      | ~ v1_tsep_1(B_252,A_253)
      | ~ m1_subset_1(u1_struct_0(B_252),k1_zfmisc_1(u1_struct_0(A_253)))
      | ~ m1_pre_topc(B_252,A_253)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1785,plain,(
    ! [B_266,A_267] :
      ( v3_pre_topc(u1_struct_0(B_266),A_267)
      | ~ v1_tsep_1(B_266,A_267)
      | ~ v2_pre_topc(A_267)
      | ~ m1_pre_topc(B_266,A_267)
      | ~ l1_pre_topc(A_267) ) ),
    inference(resolution,[status(thm)],[c_24,c_1599])).

tff(c_1815,plain,(
    ! [A_269] :
      ( v3_pre_topc(u1_struct_0('#skF_3'),A_269)
      | ~ v1_tsep_1('#skF_2',A_269)
      | ~ v2_pre_topc(A_269)
      | ~ m1_pre_topc('#skF_2',A_269)
      | ~ l1_pre_topc(A_269) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1431,c_1785])).

tff(c_1519,plain,(
    ! [B_244,A_245] :
      ( v1_tsep_1(B_244,A_245)
      | ~ v3_pre_topc(u1_struct_0(B_244),A_245)
      | ~ m1_subset_1(u1_struct_0(B_244),k1_zfmisc_1(u1_struct_0(A_245)))
      | ~ m1_pre_topc(B_244,A_245)
      | ~ l1_pre_topc(A_245)
      | ~ v2_pre_topc(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1532,plain,(
    ! [B_28,A_26] :
      ( v1_tsep_1(B_28,A_26)
      | ~ v3_pre_topc(u1_struct_0(B_28),A_26)
      | ~ v2_pre_topc(A_26)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_24,c_1519])).

tff(c_1957,plain,(
    ! [A_283] :
      ( v1_tsep_1('#skF_3',A_283)
      | ~ m1_pre_topc('#skF_3',A_283)
      | ~ v1_tsep_1('#skF_2',A_283)
      | ~ v2_pre_topc(A_283)
      | ~ m1_pre_topc('#skF_2',A_283)
      | ~ l1_pre_topc(A_283) ) ),
    inference(resolution,[status(thm)],[c_1815,c_1532])).

tff(c_1960,plain,
    ( v1_tsep_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1296,c_1957])).

tff(c_1963,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1299,c_38,c_1298,c_1960])).

tff(c_1965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1297,c_1963])).

tff(c_1967,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1966,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2006,plain,(
    ! [B_290,A_291] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_290),u1_pre_topc(B_290)),A_291)
      | ~ m1_pre_topc(B_290,A_291)
      | ~ l1_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2016,plain,(
    ! [A_292] :
      ( m1_pre_topc('#skF_3',A_292)
      | ~ m1_pre_topc('#skF_2',A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2006])).

tff(c_2019,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1966,c_2016])).

tff(c_2022,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2019])).

tff(c_2024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1967,c_2022])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.94/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.64  
% 3.94/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.65  %$ v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.94/1.65  
% 3.94/1.65  %Foreground sorts:
% 3.94/1.65  
% 3.94/1.65  
% 3.94/1.65  %Background operators:
% 3.94/1.65  
% 3.94/1.65  
% 3.94/1.65  %Foreground operators:
% 3.94/1.65  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.94/1.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.94/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.94/1.65  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.94/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.94/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.94/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.94/1.65  tff('#skF_1', type, '#skF_1': $i).
% 3.94/1.65  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.94/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.94/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.94/1.65  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.94/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.94/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.94/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.94/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.94/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.94/1.65  
% 3.94/1.67  tff(f_121, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> (v1_tsep_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_tmap_1)).
% 3.94/1.67  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 3.94/1.67  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.94/1.67  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 3.94/1.67  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.94/1.67  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.94/1.67  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.94/1.67  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.94/1.67  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_48, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 3.94/1.67  tff(c_30, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_26, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_28, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_1205, plain, (![C_208, A_209]: (m1_pre_topc(C_208, A_209) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_208), u1_pre_topc(C_208)), A_209) | ~l1_pre_topc(C_208) | ~v2_pre_topc(C_208) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_208), u1_pre_topc(C_208))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_208), u1_pre_topc(C_208))) | ~l1_pre_topc(A_209))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.94/1.67  tff(c_1214, plain, (![A_209]: (m1_pre_topc('#skF_2', A_209) | ~m1_pre_topc('#skF_3', A_209) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_209))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1205])).
% 3.94/1.67  tff(c_1218, plain, (![A_210]: (m1_pre_topc('#skF_2', A_210) | ~m1_pre_topc('#skF_3', A_210) | ~l1_pre_topc(A_210))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_28, c_26, c_34, c_32, c_1214])).
% 3.94/1.67  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.94/1.67  tff(c_91, plain, (![B_37, A_38]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_37), u1_pre_topc(B_37))) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.67  tff(c_93, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_91])).
% 3.94/1.67  tff(c_96, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_93])).
% 3.94/1.67  tff(c_4, plain, (![A_2]: (m1_subset_1(u1_pre_topc(A_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2)))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.94/1.67  tff(c_116, plain, (![C_41, A_42, D_43, B_44]: (C_41=A_42 | g1_pre_topc(C_41, D_43)!=g1_pre_topc(A_42, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.94/1.67  tff(c_124, plain, (![C_41, D_43]: (u1_struct_0('#skF_2')=C_41 | g1_pre_topc(C_41, D_43)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_116])).
% 3.94/1.67  tff(c_142, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_124])).
% 3.94/1.67  tff(c_145, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_142])).
% 3.94/1.67  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_145])).
% 3.94/1.67  tff(c_151, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_124])).
% 3.94/1.67  tff(c_171, plain, (![D_52, B_53, C_54, A_55]: (D_52=B_53 | g1_pre_topc(C_54, D_52)!=g1_pre_topc(A_55, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.94/1.67  tff(c_179, plain, (![D_52, C_54]: (u1_pre_topc('#skF_2')=D_52 | g1_pre_topc(C_54, D_52)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_171])).
% 3.94/1.67  tff(c_182, plain, (![D_56, C_57]: (u1_pre_topc('#skF_2')=D_56 | g1_pre_topc(C_57, D_56)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_179])).
% 3.94/1.67  tff(c_192, plain, (![A_58]: (u1_pre_topc(A_58)=u1_pre_topc('#skF_2') | A_58!='#skF_3' | ~v1_pre_topc(A_58) | ~l1_pre_topc(A_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_182])).
% 3.94/1.67  tff(c_196, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_3' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_96, c_192])).
% 3.94/1.67  tff(c_197, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_196])).
% 3.94/1.67  tff(c_200, plain, (~l1_pre_topc('#skF_3') | ~v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_197])).
% 3.94/1.67  tff(c_202, plain, (~v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_200])).
% 3.94/1.67  tff(c_321, plain, (![C_85, A_86]: (m1_pre_topc(C_85, A_86) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_85), u1_pre_topc(C_85)), A_86) | ~l1_pre_topc(C_85) | ~v2_pre_topc(C_85) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_85), u1_pre_topc(C_85))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_85), u1_pre_topc(C_85))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.94/1.67  tff(c_330, plain, (![A_86]: (m1_pre_topc('#skF_2', A_86) | ~m1_pre_topc('#skF_3', A_86) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_86))), inference(superposition, [status(thm), theory('equality')], [c_26, c_321])).
% 3.94/1.67  tff(c_334, plain, (![A_87]: (m1_pre_topc('#skF_2', A_87) | ~m1_pre_topc('#skF_3', A_87) | ~l1_pre_topc(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_28, c_26, c_34, c_32, c_330])).
% 3.94/1.67  tff(c_12, plain, (![B_11, A_9]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_11), u1_pre_topc(B_11))) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.67  tff(c_341, plain, (![A_87]: (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc('#skF_3', A_87) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_334, c_12])).
% 3.94/1.67  tff(c_346, plain, (![A_87]: (v1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', A_87) | ~l1_pre_topc(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_341])).
% 3.94/1.67  tff(c_348, plain, (![A_88]: (~m1_pre_topc('#skF_3', A_88) | ~l1_pre_topc(A_88))), inference(negUnitSimplification, [status(thm)], [c_202, c_346])).
% 3.94/1.67  tff(c_351, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_348])).
% 3.94/1.67  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_351])).
% 3.94/1.67  tff(c_357, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_196])).
% 3.94/1.67  tff(c_152, plain, (![C_49, D_50]: (u1_struct_0('#skF_2')=C_49 | g1_pre_topc(C_49, D_50)!='#skF_3')), inference(splitRight, [status(thm)], [c_124])).
% 3.94/1.67  tff(c_162, plain, (![A_51]: (u1_struct_0(A_51)=u1_struct_0('#skF_2') | A_51!='#skF_3' | ~v1_pre_topc(A_51) | ~l1_pre_topc(A_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_152])).
% 3.94/1.67  tff(c_166, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_3' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_96, c_162])).
% 3.94/1.67  tff(c_364, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_357, c_166])).
% 3.94/1.67  tff(c_365, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_364])).
% 3.94/1.67  tff(c_368, plain, (~v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_365])).
% 3.94/1.67  tff(c_371, plain, (~v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_368])).
% 3.94/1.67  tff(c_486, plain, (![C_115, A_116]: (m1_pre_topc(C_115, A_116) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_115), u1_pre_topc(C_115)), A_116) | ~l1_pre_topc(C_115) | ~v2_pre_topc(C_115) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_115), u1_pre_topc(C_115))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_115), u1_pre_topc(C_115))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.94/1.67  tff(c_495, plain, (![A_116]: (m1_pre_topc('#skF_2', A_116) | ~m1_pre_topc('#skF_3', A_116) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_116))), inference(superposition, [status(thm), theory('equality')], [c_26, c_486])).
% 3.94/1.67  tff(c_499, plain, (![A_117]: (m1_pre_topc('#skF_2', A_117) | ~m1_pre_topc('#skF_3', A_117) | ~l1_pre_topc(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_28, c_26, c_34, c_32, c_495])).
% 3.94/1.67  tff(c_506, plain, (![A_117]: (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc('#skF_3', A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_499, c_12])).
% 3.94/1.67  tff(c_511, plain, (![A_117]: (v1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', A_117) | ~l1_pre_topc(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_506])).
% 3.94/1.67  tff(c_513, plain, (![A_118]: (~m1_pre_topc('#skF_3', A_118) | ~l1_pre_topc(A_118))), inference(negUnitSimplification, [status(thm)], [c_371, c_511])).
% 3.94/1.67  tff(c_516, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_513])).
% 3.94/1.67  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_516])).
% 3.94/1.67  tff(c_522, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_364])).
% 3.94/1.67  tff(c_150, plain, (![C_41, D_43]: (u1_struct_0('#skF_2')=C_41 | g1_pre_topc(C_41, D_43)!='#skF_3')), inference(splitRight, [status(thm)], [c_124])).
% 3.94/1.67  tff(c_553, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_522, c_150])).
% 3.94/1.67  tff(c_181, plain, (![D_52, C_54]: (u1_pre_topc('#skF_2')=D_52 | g1_pre_topc(C_54, D_52)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_179])).
% 3.94/1.67  tff(c_552, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_522, c_181])).
% 3.94/1.67  tff(c_730, plain, (![C_133, A_134]: (m1_pre_topc(C_133, A_134) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_133), u1_pre_topc(C_133)), A_134) | ~l1_pre_topc(C_133) | ~v2_pre_topc(C_133) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_133), u1_pre_topc(C_133))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_133), u1_pre_topc(C_133))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.94/1.67  tff(c_733, plain, (![A_134]: (m1_pre_topc('#skF_2', A_134) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_134) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_134))), inference(superposition, [status(thm), theory('equality')], [c_553, c_730])).
% 3.94/1.67  tff(c_747, plain, (![A_134]: (m1_pre_topc('#skF_2', A_134) | ~m1_pre_topc('#skF_3', A_134) | ~l1_pre_topc(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_522, c_553, c_552, c_28, c_522, c_553, c_552, c_34, c_32, c_522, c_552, c_733])).
% 3.94/1.67  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_56, plain, (v1_tsep_1('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_57, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 3.94/1.67  tff(c_24, plain, (![B_28, A_26]: (m1_subset_1(u1_struct_0(B_28), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.94/1.67  tff(c_674, plain, (![B_127, A_128]: (v3_pre_topc(u1_struct_0(B_127), A_128) | ~v1_tsep_1(B_127, A_128) | ~m1_subset_1(u1_struct_0(B_127), k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.94/1.67  tff(c_693, plain, (![B_28, A_26]: (v3_pre_topc(u1_struct_0(B_28), A_26) | ~v1_tsep_1(B_28, A_26) | ~v2_pre_topc(A_26) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_24, c_674])).
% 3.94/1.67  tff(c_627, plain, (![B_121, A_122]: (v1_tsep_1(B_121, A_122) | ~v3_pre_topc(u1_struct_0(B_121), A_122) | ~m1_subset_1(u1_struct_0(B_121), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.94/1.67  tff(c_770, plain, (![B_136, A_137]: (v1_tsep_1(B_136, A_137) | ~v3_pre_topc(u1_struct_0(B_136), A_137) | ~v2_pre_topc(A_137) | ~m1_pre_topc(B_136, A_137) | ~l1_pre_topc(A_137))), inference(resolution, [status(thm)], [c_24, c_627])).
% 3.94/1.67  tff(c_823, plain, (![A_144]: (v1_tsep_1('#skF_2', A_144) | ~v3_pre_topc(u1_struct_0('#skF_3'), A_144) | ~v2_pre_topc(A_144) | ~m1_pre_topc('#skF_2', A_144) | ~l1_pre_topc(A_144))), inference(superposition, [status(thm), theory('equality')], [c_553, c_770])).
% 3.94/1.67  tff(c_948, plain, (![A_156]: (v1_tsep_1('#skF_2', A_156) | ~m1_pre_topc('#skF_2', A_156) | ~v1_tsep_1('#skF_3', A_156) | ~v2_pre_topc(A_156) | ~m1_pre_topc('#skF_3', A_156) | ~l1_pre_topc(A_156))), inference(resolution, [status(thm)], [c_693, c_823])).
% 3.94/1.67  tff(c_40, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_88, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_58, c_40])).
% 3.94/1.67  tff(c_89, plain, (~v1_tsep_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_88])).
% 3.94/1.67  tff(c_954, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_948, c_89])).
% 3.94/1.67  tff(c_958, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_58, c_38, c_57, c_954])).
% 3.94/1.67  tff(c_961, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_747, c_958])).
% 3.94/1.67  tff(c_965, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_58, c_961])).
% 3.94/1.67  tff(c_966, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_88])).
% 3.94/1.67  tff(c_1228, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1218, c_966])).
% 3.94/1.67  tff(c_1238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_58, c_1228])).
% 3.94/1.67  tff(c_1240, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.94/1.67  tff(c_1239, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.94/1.67  tff(c_1277, plain, (![B_217, A_218]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_217), u1_pre_topc(B_217)), A_218) | ~m1_pre_topc(B_217, A_218) | ~l1_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.67  tff(c_1287, plain, (![A_219]: (m1_pre_topc('#skF_3', A_219) | ~m1_pre_topc('#skF_2', A_219) | ~l1_pre_topc(A_219))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1277])).
% 3.94/1.67  tff(c_1290, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1239, c_1287])).
% 3.94/1.67  tff(c_1293, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1290])).
% 3.94/1.67  tff(c_1295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1240, c_1293])).
% 3.94/1.67  tff(c_1297, plain, (~v1_tsep_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 3.94/1.67  tff(c_54, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.94/1.67  tff(c_1299, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1297, c_54])).
% 3.94/1.67  tff(c_1298, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 3.94/1.67  tff(c_1296, plain, (v1_tsep_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 3.94/1.67  tff(c_1326, plain, (![B_222, A_223]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_222), u1_pre_topc(B_222))) | ~m1_pre_topc(B_222, A_223) | ~l1_pre_topc(A_223))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.67  tff(c_1328, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1299, c_1326])).
% 3.94/1.67  tff(c_1333, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_1328])).
% 3.94/1.67  tff(c_1366, plain, (![C_229, A_230, D_231, B_232]: (C_229=A_230 | g1_pre_topc(C_229, D_231)!=g1_pre_topc(A_230, B_232) | ~m1_subset_1(B_232, k1_zfmisc_1(k1_zfmisc_1(A_230))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.94/1.67  tff(c_1375, plain, (![A_233, B_234]: (u1_struct_0('#skF_2')=A_233 | g1_pre_topc(A_233, B_234)!='#skF_3' | ~m1_subset_1(B_234, k1_zfmisc_1(k1_zfmisc_1(A_233))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1366])).
% 3.94/1.67  tff(c_1380, plain, (![A_235]: (u1_struct_0(A_235)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_235), u1_pre_topc(A_235))!='#skF_3' | ~l1_pre_topc(A_235))), inference(resolution, [status(thm)], [c_4, c_1375])).
% 3.94/1.67  tff(c_1421, plain, (![A_243]: (u1_struct_0(A_243)=u1_struct_0('#skF_2') | A_243!='#skF_3' | ~l1_pre_topc(A_243) | ~v1_pre_topc(A_243) | ~l1_pre_topc(A_243))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1380])).
% 3.94/1.67  tff(c_1427, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1333, c_1421])).
% 3.94/1.67  tff(c_1431, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1427])).
% 3.94/1.67  tff(c_1599, plain, (![B_252, A_253]: (v3_pre_topc(u1_struct_0(B_252), A_253) | ~v1_tsep_1(B_252, A_253) | ~m1_subset_1(u1_struct_0(B_252), k1_zfmisc_1(u1_struct_0(A_253))) | ~m1_pre_topc(B_252, A_253) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.94/1.67  tff(c_1785, plain, (![B_266, A_267]: (v3_pre_topc(u1_struct_0(B_266), A_267) | ~v1_tsep_1(B_266, A_267) | ~v2_pre_topc(A_267) | ~m1_pre_topc(B_266, A_267) | ~l1_pre_topc(A_267))), inference(resolution, [status(thm)], [c_24, c_1599])).
% 3.94/1.67  tff(c_1815, plain, (![A_269]: (v3_pre_topc(u1_struct_0('#skF_3'), A_269) | ~v1_tsep_1('#skF_2', A_269) | ~v2_pre_topc(A_269) | ~m1_pre_topc('#skF_2', A_269) | ~l1_pre_topc(A_269))), inference(superposition, [status(thm), theory('equality')], [c_1431, c_1785])).
% 3.94/1.67  tff(c_1519, plain, (![B_244, A_245]: (v1_tsep_1(B_244, A_245) | ~v3_pre_topc(u1_struct_0(B_244), A_245) | ~m1_subset_1(u1_struct_0(B_244), k1_zfmisc_1(u1_struct_0(A_245))) | ~m1_pre_topc(B_244, A_245) | ~l1_pre_topc(A_245) | ~v2_pre_topc(A_245))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.94/1.67  tff(c_1532, plain, (![B_28, A_26]: (v1_tsep_1(B_28, A_26) | ~v3_pre_topc(u1_struct_0(B_28), A_26) | ~v2_pre_topc(A_26) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_24, c_1519])).
% 3.94/1.67  tff(c_1957, plain, (![A_283]: (v1_tsep_1('#skF_3', A_283) | ~m1_pre_topc('#skF_3', A_283) | ~v1_tsep_1('#skF_2', A_283) | ~v2_pre_topc(A_283) | ~m1_pre_topc('#skF_2', A_283) | ~l1_pre_topc(A_283))), inference(resolution, [status(thm)], [c_1815, c_1532])).
% 3.94/1.67  tff(c_1960, plain, (v1_tsep_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1296, c_1957])).
% 3.94/1.67  tff(c_1963, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1299, c_38, c_1298, c_1960])).
% 3.94/1.67  tff(c_1965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1297, c_1963])).
% 3.94/1.67  tff(c_1967, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.94/1.67  tff(c_1966, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.94/1.67  tff(c_2006, plain, (![B_290, A_291]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_290), u1_pre_topc(B_290)), A_291) | ~m1_pre_topc(B_290, A_291) | ~l1_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.94/1.67  tff(c_2016, plain, (![A_292]: (m1_pre_topc('#skF_3', A_292) | ~m1_pre_topc('#skF_2', A_292) | ~l1_pre_topc(A_292))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2006])).
% 3.94/1.67  tff(c_2019, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1966, c_2016])).
% 3.94/1.67  tff(c_2022, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2019])).
% 3.94/1.67  tff(c_2024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1967, c_2022])).
% 3.94/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.67  
% 3.94/1.67  Inference rules
% 3.94/1.67  ----------------------
% 3.94/1.67  #Ref     : 24
% 3.94/1.67  #Sup     : 392
% 3.94/1.67  #Fact    : 0
% 3.94/1.67  #Define  : 0
% 3.94/1.67  #Split   : 17
% 3.94/1.67  #Chain   : 0
% 3.94/1.67  #Close   : 0
% 3.94/1.67  
% 3.94/1.67  Ordering : KBO
% 3.94/1.67  
% 3.94/1.67  Simplification rules
% 3.94/1.67  ----------------------
% 3.94/1.67  #Subsume      : 131
% 3.94/1.67  #Demod        : 388
% 3.94/1.67  #Tautology    : 160
% 3.94/1.67  #SimpNegUnit  : 11
% 3.94/1.67  #BackRed      : 21
% 3.94/1.67  
% 3.94/1.67  #Partial instantiations: 0
% 3.94/1.67  #Strategies tried      : 1
% 3.94/1.67  
% 3.94/1.67  Timing (in seconds)
% 3.94/1.67  ----------------------
% 3.94/1.67  Preprocessing        : 0.30
% 3.94/1.67  Parsing              : 0.16
% 3.94/1.67  CNF conversion       : 0.02
% 3.94/1.67  Main loop            : 0.59
% 3.94/1.67  Inferencing          : 0.21
% 3.94/1.67  Reduction            : 0.18
% 3.94/1.67  Demodulation         : 0.12
% 3.94/1.67  BG Simplification    : 0.03
% 3.94/1.67  Subsumption          : 0.12
% 3.94/1.67  Abstraction          : 0.03
% 3.94/1.67  MUC search           : 0.00
% 3.94/1.67  Cooper               : 0.00
% 3.94/1.67  Total                : 0.94
% 3.94/1.67  Index Insertion      : 0.00
% 3.94/1.67  Index Deletion       : 0.00
% 3.94/1.67  Index Matching       : 0.00
% 3.94/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
