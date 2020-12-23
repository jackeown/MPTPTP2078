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
% DateTime   : Thu Dec  3 10:26:23 EST 2020

% Result     : Theorem 3.87s
% Output     : CNFRefutation 3.87s
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
%$ v4_pre_topc > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

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
                 => ( ( v1_borsuk_1(B,A)
                      & m1_pre_topc(B,A) )
                  <=> ( v1_borsuk_1(C,A)
                      & m1_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_tmap_1)).

tff(f_89,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_borsuk_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v4_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tsep_1)).

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

tff(c_1224,plain,(
    ! [C_210,A_211] :
      ( m1_pre_topc(C_210,A_211)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_210),u1_pre_topc(C_210)),A_211)
      | ~ l1_pre_topc(C_210)
      | ~ v2_pre_topc(C_210)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_210),u1_pre_topc(C_210)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_210),u1_pre_topc(C_210)))
      | ~ l1_pre_topc(A_211) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1233,plain,(
    ! [A_211] :
      ( m1_pre_topc('#skF_2',A_211)
      | ~ m1_pre_topc('#skF_3',A_211)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_211) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1224])).

tff(c_1237,plain,(
    ! [A_212] :
      ( m1_pre_topc('#skF_2',A_212)
      | ~ m1_pre_topc('#skF_3',A_212)
      | ~ l1_pre_topc(A_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26,c_28,c_26,c_34,c_32,c_1233])).

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
    inference(cnfTransformation,[status(thm)],[f_89])).

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
    inference(cnfTransformation,[status(thm)],[f_89])).

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
    inference(cnfTransformation,[status(thm)],[f_89])).

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
    ( v1_borsuk_1('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_57,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_24,plain,(
    ! [B_28,A_26] :
      ( m1_subset_1(u1_struct_0(B_28),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_627,plain,(
    ! [B_121,A_122] :
      ( v4_pre_topc(u1_struct_0(B_121),A_122)
      | ~ v1_borsuk_1(B_121,A_122)
      | ~ m1_subset_1(u1_struct_0(B_121),k1_zfmisc_1(u1_struct_0(A_122)))
      | ~ m1_pre_topc(B_121,A_122)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_640,plain,(
    ! [B_28,A_26] :
      ( v4_pre_topc(u1_struct_0(B_28),A_26)
      | ~ v1_borsuk_1(B_28,A_26)
      | ~ v2_pre_topc(A_26)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_24,c_627])).

tff(c_674,plain,(
    ! [B_127,A_128] :
      ( v1_borsuk_1(B_127,A_128)
      | ~ v4_pre_topc(u1_struct_0(B_127),A_128)
      | ~ m1_subset_1(u1_struct_0(B_127),k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_781,plain,(
    ! [B_138,A_139] :
      ( v1_borsuk_1(B_138,A_139)
      | ~ v4_pre_topc(u1_struct_0(B_138),A_139)
      | ~ v2_pre_topc(A_139)
      | ~ m1_pre_topc(B_138,A_139)
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_24,c_674])).

tff(c_799,plain,(
    ! [A_140] :
      ( v1_borsuk_1('#skF_2',A_140)
      | ~ v4_pre_topc(u1_struct_0('#skF_3'),A_140)
      | ~ v2_pre_topc(A_140)
      | ~ m1_pre_topc('#skF_2',A_140)
      | ~ l1_pre_topc(A_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_553,c_781])).

tff(c_937,plain,(
    ! [A_152] :
      ( v1_borsuk_1('#skF_2',A_152)
      | ~ m1_pre_topc('#skF_2',A_152)
      | ~ v1_borsuk_1('#skF_3',A_152)
      | ~ v2_pre_topc(A_152)
      | ~ m1_pre_topc('#skF_3',A_152)
      | ~ l1_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_640,c_799])).

tff(c_40,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_88,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_58,c_40])).

tff(c_89,plain,(
    ~ v1_borsuk_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_940,plain,
    ( ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_937,c_89])).

tff(c_943,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58,c_38,c_57,c_940])).

tff(c_956,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_747,c_943])).

tff(c_960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58,c_956])).

tff(c_961,plain,(
    ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1247,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1237,c_961])).

tff(c_1257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_58,c_1247])).

tff(c_1259,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1258,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1296,plain,(
    ! [B_219,A_220] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_219),u1_pre_topc(B_219)),A_220)
      | ~ m1_pre_topc(B_219,A_220)
      | ~ l1_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1306,plain,(
    ! [A_221] :
      ( m1_pre_topc('#skF_3',A_221)
      | ~ m1_pre_topc('#skF_2',A_221)
      | ~ l1_pre_topc(A_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1296])).

tff(c_1309,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1258,c_1306])).

tff(c_1312,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1309])).

tff(c_1314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1259,c_1312])).

tff(c_1316,plain,(
    ~ v1_borsuk_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( m1_pre_topc('#skF_2','#skF_1')
    | v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1318,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_1316,c_54])).

tff(c_1317,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_1315,plain,(
    v1_borsuk_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_1345,plain,(
    ! [B_224,A_225] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_224),u1_pre_topc(B_224)))
      | ~ m1_pre_topc(B_224,A_225)
      | ~ l1_pre_topc(A_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1347,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1318,c_1345])).

tff(c_1352,plain,(
    v1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26,c_1347])).

tff(c_1385,plain,(
    ! [C_231,A_232,D_233,B_234] :
      ( C_231 = A_232
      | g1_pre_topc(C_231,D_233) != g1_pre_topc(A_232,B_234)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(k1_zfmisc_1(A_232))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1394,plain,(
    ! [A_235,B_236] :
      ( u1_struct_0('#skF_2') = A_235
      | g1_pre_topc(A_235,B_236) != '#skF_3'
      | ~ m1_subset_1(B_236,k1_zfmisc_1(k1_zfmisc_1(A_235))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1385])).

tff(c_1399,plain,(
    ! [A_237] :
      ( u1_struct_0(A_237) = u1_struct_0('#skF_2')
      | g1_pre_topc(u1_struct_0(A_237),u1_pre_topc(A_237)) != '#skF_3'
      | ~ l1_pre_topc(A_237) ) ),
    inference(resolution,[status(thm)],[c_4,c_1394])).

tff(c_1440,plain,(
    ! [A_245] :
      ( u1_struct_0(A_245) = u1_struct_0('#skF_2')
      | A_245 != '#skF_3'
      | ~ l1_pre_topc(A_245)
      | ~ v1_pre_topc(A_245)
      | ~ l1_pre_topc(A_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1399])).

tff(c_1446,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_1352,c_1440])).

tff(c_1450,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1446])).

tff(c_1538,plain,(
    ! [B_246,A_247] :
      ( v4_pre_topc(u1_struct_0(B_246),A_247)
      | ~ v1_borsuk_1(B_246,A_247)
      | ~ m1_subset_1(u1_struct_0(B_246),k1_zfmisc_1(u1_struct_0(A_247)))
      | ~ m1_pre_topc(B_246,A_247)
      | ~ l1_pre_topc(A_247)
      | ~ v2_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1779,plain,(
    ! [B_264,A_265] :
      ( v4_pre_topc(u1_struct_0(B_264),A_265)
      | ~ v1_borsuk_1(B_264,A_265)
      | ~ v2_pre_topc(A_265)
      | ~ m1_pre_topc(B_264,A_265)
      | ~ l1_pre_topc(A_265) ) ),
    inference(resolution,[status(thm)],[c_24,c_1538])).

tff(c_1819,plain,(
    ! [A_270] :
      ( v4_pre_topc(u1_struct_0('#skF_3'),A_270)
      | ~ v1_borsuk_1('#skF_2',A_270)
      | ~ v2_pre_topc(A_270)
      | ~ m1_pre_topc('#skF_2',A_270)
      | ~ l1_pre_topc(A_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1450,c_1779])).

tff(c_1618,plain,(
    ! [B_254,A_255] :
      ( v1_borsuk_1(B_254,A_255)
      | ~ v4_pre_topc(u1_struct_0(B_254),A_255)
      | ~ m1_subset_1(u1_struct_0(B_254),k1_zfmisc_1(u1_struct_0(A_255)))
      | ~ m1_pre_topc(B_254,A_255)
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1637,plain,(
    ! [B_28,A_26] :
      ( v1_borsuk_1(B_28,A_26)
      | ~ v4_pre_topc(u1_struct_0(B_28),A_26)
      | ~ v2_pre_topc(A_26)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(resolution,[status(thm)],[c_24,c_1618])).

tff(c_1977,plain,(
    ! [A_286] :
      ( v1_borsuk_1('#skF_3',A_286)
      | ~ m1_pre_topc('#skF_3',A_286)
      | ~ v1_borsuk_1('#skF_2',A_286)
      | ~ v2_pre_topc(A_286)
      | ~ m1_pre_topc('#skF_2',A_286)
      | ~ l1_pre_topc(A_286) ) ),
    inference(resolution,[status(thm)],[c_1819,c_1637])).

tff(c_1983,plain,
    ( v1_borsuk_1('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1315,c_1977])).

tff(c_1987,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1318,c_38,c_1317,c_1983])).

tff(c_1989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1316,c_1987])).

tff(c_1991,plain,(
    ~ m1_pre_topc('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1990,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2030,plain,(
    ! [B_293,A_294] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_293),u1_pre_topc(B_293)),A_294)
      | ~ m1_pre_topc(B_293,A_294)
      | ~ l1_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2040,plain,(
    ! [A_295] :
      ( m1_pre_topc('#skF_3',A_295)
      | ~ m1_pre_topc('#skF_2',A_295)
      | ~ l1_pre_topc(A_295) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2030])).

tff(c_2043,plain,
    ( m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_1990,c_2040])).

tff(c_2046,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2043])).

tff(c_2048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1991,c_2046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:20:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.87/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.71  
% 3.87/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.71  %$ v4_pre_topc > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_pre_topc > v1_pre_topc > l1_pre_topc > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.87/1.71  
% 3.87/1.71  %Foreground sorts:
% 3.87/1.71  
% 3.87/1.71  
% 3.87/1.71  %Background operators:
% 3.87/1.71  
% 3.87/1.71  
% 3.87/1.71  %Foreground operators:
% 3.87/1.71  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.87/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.71  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.87/1.71  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.87/1.71  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.71  tff('#skF_3', type, '#skF_3': $i).
% 3.87/1.71  tff('#skF_1', type, '#skF_1': $i).
% 3.87/1.71  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.87/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.71  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.87/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.71  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.87/1.71  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.87/1.71  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.87/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.71  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 3.87/1.71  
% 3.87/1.73  tff(f_121, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((C = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> (v1_borsuk_1(C, A) & m1_pre_topc(C, A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_tmap_1)).
% 3.87/1.73  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 3.87/1.73  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.87/1.73  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 3.87/1.73  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.87/1.73  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.87/1.73  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.87/1.73  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) <=> v4_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tsep_1)).
% 3.87/1.73  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_48, plain, (m1_pre_topc('#skF_2', '#skF_1') | m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 3.87/1.73  tff(c_30, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_26, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_28, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_34, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_32, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_1224, plain, (![C_210, A_211]: (m1_pre_topc(C_210, A_211) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_210), u1_pre_topc(C_210)), A_211) | ~l1_pre_topc(C_210) | ~v2_pre_topc(C_210) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_210), u1_pre_topc(C_210))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_210), u1_pre_topc(C_210))) | ~l1_pre_topc(A_211))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.73  tff(c_1233, plain, (![A_211]: (m1_pre_topc('#skF_2', A_211) | ~m1_pre_topc('#skF_3', A_211) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_211))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1224])).
% 3.87/1.73  tff(c_1237, plain, (![A_212]: (m1_pre_topc('#skF_2', A_212) | ~m1_pre_topc('#skF_3', A_212) | ~l1_pre_topc(A_212))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_28, c_26, c_34, c_32, c_1233])).
% 3.87/1.73  tff(c_2, plain, (![A_1]: (g1_pre_topc(u1_struct_0(A_1), u1_pre_topc(A_1))=A_1 | ~v1_pre_topc(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.73  tff(c_91, plain, (![B_37, A_38]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_37), u1_pre_topc(B_37))) | ~m1_pre_topc(B_37, A_38) | ~l1_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.73  tff(c_93, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_91])).
% 3.87/1.73  tff(c_96, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_93])).
% 3.87/1.73  tff(c_4, plain, (![A_2]: (m1_subset_1(u1_pre_topc(A_2), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_2)))) | ~l1_pre_topc(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.73  tff(c_116, plain, (![C_41, A_42, D_43, B_44]: (C_41=A_42 | g1_pre_topc(C_41, D_43)!=g1_pre_topc(A_42, B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.87/1.73  tff(c_124, plain, (![C_41, D_43]: (u1_struct_0('#skF_2')=C_41 | g1_pre_topc(C_41, D_43)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_116])).
% 3.87/1.73  tff(c_142, plain, (~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_124])).
% 3.87/1.73  tff(c_145, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_4, c_142])).
% 3.87/1.73  tff(c_149, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_145])).
% 3.87/1.73  tff(c_151, plain, (m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_124])).
% 3.87/1.73  tff(c_171, plain, (![D_52, B_53, C_54, A_55]: (D_52=B_53 | g1_pre_topc(C_54, D_52)!=g1_pre_topc(A_55, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.87/1.73  tff(c_179, plain, (![D_52, C_54]: (u1_pre_topc('#skF_2')=D_52 | g1_pre_topc(C_54, D_52)!='#skF_3' | ~m1_subset_1(u1_pre_topc('#skF_2'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_2')))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_171])).
% 3.87/1.73  tff(c_182, plain, (![D_56, C_57]: (u1_pre_topc('#skF_2')=D_56 | g1_pre_topc(C_57, D_56)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_179])).
% 3.87/1.73  tff(c_192, plain, (![A_58]: (u1_pre_topc(A_58)=u1_pre_topc('#skF_2') | A_58!='#skF_3' | ~v1_pre_topc(A_58) | ~l1_pre_topc(A_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_182])).
% 3.87/1.73  tff(c_196, plain, (u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=u1_pre_topc('#skF_2') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_3' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_96, c_192])).
% 3.87/1.73  tff(c_197, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitLeft, [status(thm)], [c_196])).
% 3.87/1.73  tff(c_200, plain, (~l1_pre_topc('#skF_3') | ~v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_197])).
% 3.87/1.73  tff(c_202, plain, (~v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_200])).
% 3.87/1.73  tff(c_321, plain, (![C_85, A_86]: (m1_pre_topc(C_85, A_86) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_85), u1_pre_topc(C_85)), A_86) | ~l1_pre_topc(C_85) | ~v2_pre_topc(C_85) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_85), u1_pre_topc(C_85))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_85), u1_pre_topc(C_85))) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.73  tff(c_330, plain, (![A_86]: (m1_pre_topc('#skF_2', A_86) | ~m1_pre_topc('#skF_3', A_86) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_86))), inference(superposition, [status(thm), theory('equality')], [c_26, c_321])).
% 3.87/1.73  tff(c_334, plain, (![A_87]: (m1_pre_topc('#skF_2', A_87) | ~m1_pre_topc('#skF_3', A_87) | ~l1_pre_topc(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_28, c_26, c_34, c_32, c_330])).
% 3.87/1.73  tff(c_12, plain, (![B_11, A_9]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_11), u1_pre_topc(B_11))) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.73  tff(c_341, plain, (![A_87]: (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc('#skF_3', A_87) | ~l1_pre_topc(A_87))), inference(resolution, [status(thm)], [c_334, c_12])).
% 3.87/1.73  tff(c_346, plain, (![A_87]: (v1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', A_87) | ~l1_pre_topc(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_341])).
% 3.87/1.73  tff(c_348, plain, (![A_88]: (~m1_pre_topc('#skF_3', A_88) | ~l1_pre_topc(A_88))), inference(negUnitSimplification, [status(thm)], [c_202, c_346])).
% 3.87/1.73  tff(c_351, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_348])).
% 3.87/1.73  tff(c_355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_351])).
% 3.87/1.73  tff(c_357, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(splitRight, [status(thm)], [c_196])).
% 3.87/1.73  tff(c_152, plain, (![C_49, D_50]: (u1_struct_0('#skF_2')=C_49 | g1_pre_topc(C_49, D_50)!='#skF_3')), inference(splitRight, [status(thm)], [c_124])).
% 3.87/1.73  tff(c_162, plain, (![A_51]: (u1_struct_0(A_51)=u1_struct_0('#skF_2') | A_51!='#skF_3' | ~v1_pre_topc(A_51) | ~l1_pre_topc(A_51))), inference(superposition, [status(thm), theory('equality')], [c_2, c_152])).
% 3.87/1.73  tff(c_166, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_3' | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_96, c_162])).
% 3.87/1.73  tff(c_364, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_357, c_166])).
% 3.87/1.73  tff(c_365, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_364])).
% 3.87/1.73  tff(c_368, plain, (~v1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_365])).
% 3.87/1.73  tff(c_371, plain, (~v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_368])).
% 3.87/1.73  tff(c_486, plain, (![C_115, A_116]: (m1_pre_topc(C_115, A_116) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_115), u1_pre_topc(C_115)), A_116) | ~l1_pre_topc(C_115) | ~v2_pre_topc(C_115) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_115), u1_pre_topc(C_115))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_115), u1_pre_topc(C_115))) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.73  tff(c_495, plain, (![A_116]: (m1_pre_topc('#skF_2', A_116) | ~m1_pre_topc('#skF_3', A_116) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_116))), inference(superposition, [status(thm), theory('equality')], [c_26, c_486])).
% 3.87/1.73  tff(c_499, plain, (![A_117]: (m1_pre_topc('#skF_2', A_117) | ~m1_pre_topc('#skF_3', A_117) | ~l1_pre_topc(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26, c_28, c_26, c_34, c_32, c_495])).
% 3.87/1.73  tff(c_506, plain, (![A_117]: (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc('#skF_3', A_117) | ~l1_pre_topc(A_117))), inference(resolution, [status(thm)], [c_499, c_12])).
% 3.87/1.73  tff(c_511, plain, (![A_117]: (v1_pre_topc('#skF_3') | ~m1_pre_topc('#skF_3', A_117) | ~l1_pre_topc(A_117))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_506])).
% 3.87/1.73  tff(c_513, plain, (![A_118]: (~m1_pre_topc('#skF_3', A_118) | ~l1_pre_topc(A_118))), inference(negUnitSimplification, [status(thm)], [c_371, c_511])).
% 3.87/1.73  tff(c_516, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_513])).
% 3.87/1.73  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_516])).
% 3.87/1.73  tff(c_522, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_364])).
% 3.87/1.73  tff(c_150, plain, (![C_41, D_43]: (u1_struct_0('#skF_2')=C_41 | g1_pre_topc(C_41, D_43)!='#skF_3')), inference(splitRight, [status(thm)], [c_124])).
% 3.87/1.73  tff(c_553, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_522, c_150])).
% 3.87/1.73  tff(c_181, plain, (![D_52, C_54]: (u1_pre_topc('#skF_2')=D_52 | g1_pre_topc(C_54, D_52)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_151, c_179])).
% 3.87/1.73  tff(c_552, plain, (u1_pre_topc('#skF_2')=u1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_522, c_181])).
% 3.87/1.73  tff(c_730, plain, (![C_133, A_134]: (m1_pre_topc(C_133, A_134) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_133), u1_pre_topc(C_133)), A_134) | ~l1_pre_topc(C_133) | ~v2_pre_topc(C_133) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_133), u1_pre_topc(C_133))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_133), u1_pre_topc(C_133))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.73  tff(c_733, plain, (![A_134]: (m1_pre_topc('#skF_2', A_134) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_2')), A_134) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_134))), inference(superposition, [status(thm), theory('equality')], [c_553, c_730])).
% 3.87/1.73  tff(c_747, plain, (![A_134]: (m1_pre_topc('#skF_2', A_134) | ~m1_pre_topc('#skF_3', A_134) | ~l1_pre_topc(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_522, c_553, c_552, c_28, c_522, c_553, c_552, c_34, c_32, c_522, c_552, c_733])).
% 3.87/1.73  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_56, plain, (v1_borsuk_1('#skF_2', '#skF_1') | v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_57, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_56])).
% 3.87/1.73  tff(c_24, plain, (![B_28, A_26]: (m1_subset_1(u1_struct_0(B_28), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.87/1.73  tff(c_627, plain, (![B_121, A_122]: (v4_pre_topc(u1_struct_0(B_121), A_122) | ~v1_borsuk_1(B_121, A_122) | ~m1_subset_1(u1_struct_0(B_121), k1_zfmisc_1(u1_struct_0(A_122))) | ~m1_pre_topc(B_121, A_122) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.87/1.73  tff(c_640, plain, (![B_28, A_26]: (v4_pre_topc(u1_struct_0(B_28), A_26) | ~v1_borsuk_1(B_28, A_26) | ~v2_pre_topc(A_26) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_24, c_627])).
% 3.87/1.73  tff(c_674, plain, (![B_127, A_128]: (v1_borsuk_1(B_127, A_128) | ~v4_pre_topc(u1_struct_0(B_127), A_128) | ~m1_subset_1(u1_struct_0(B_127), k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.87/1.73  tff(c_781, plain, (![B_138, A_139]: (v1_borsuk_1(B_138, A_139) | ~v4_pre_topc(u1_struct_0(B_138), A_139) | ~v2_pre_topc(A_139) | ~m1_pre_topc(B_138, A_139) | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_24, c_674])).
% 3.87/1.73  tff(c_799, plain, (![A_140]: (v1_borsuk_1('#skF_2', A_140) | ~v4_pre_topc(u1_struct_0('#skF_3'), A_140) | ~v2_pre_topc(A_140) | ~m1_pre_topc('#skF_2', A_140) | ~l1_pre_topc(A_140))), inference(superposition, [status(thm), theory('equality')], [c_553, c_781])).
% 3.87/1.73  tff(c_937, plain, (![A_152]: (v1_borsuk_1('#skF_2', A_152) | ~m1_pre_topc('#skF_2', A_152) | ~v1_borsuk_1('#skF_3', A_152) | ~v2_pre_topc(A_152) | ~m1_pre_topc('#skF_3', A_152) | ~l1_pre_topc(A_152))), inference(resolution, [status(thm)], [c_640, c_799])).
% 3.87/1.73  tff(c_40, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_88, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_58, c_40])).
% 3.87/1.73  tff(c_89, plain, (~v1_borsuk_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_88])).
% 3.87/1.73  tff(c_940, plain, (~m1_pre_topc('#skF_2', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_937, c_89])).
% 3.87/1.73  tff(c_943, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_58, c_38, c_57, c_940])).
% 3.87/1.73  tff(c_956, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_747, c_943])).
% 3.87/1.73  tff(c_960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_58, c_956])).
% 3.87/1.73  tff(c_961, plain, (~m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_88])).
% 3.87/1.73  tff(c_1247, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1237, c_961])).
% 3.87/1.73  tff(c_1257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_58, c_1247])).
% 3.87/1.73  tff(c_1259, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.87/1.73  tff(c_1258, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.87/1.73  tff(c_1296, plain, (![B_219, A_220]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_219), u1_pre_topc(B_219)), A_220) | ~m1_pre_topc(B_219, A_220) | ~l1_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.73  tff(c_1306, plain, (![A_221]: (m1_pre_topc('#skF_3', A_221) | ~m1_pre_topc('#skF_2', A_221) | ~l1_pre_topc(A_221))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1296])).
% 3.87/1.73  tff(c_1309, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1258, c_1306])).
% 3.87/1.73  tff(c_1312, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1309])).
% 3.87/1.73  tff(c_1314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1259, c_1312])).
% 3.87/1.73  tff(c_1316, plain, (~v1_borsuk_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 3.87/1.73  tff(c_54, plain, (m1_pre_topc('#skF_2', '#skF_1') | v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.73  tff(c_1318, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_1316, c_54])).
% 3.87/1.73  tff(c_1317, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_48])).
% 3.87/1.73  tff(c_1315, plain, (v1_borsuk_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 3.87/1.73  tff(c_1345, plain, (![B_224, A_225]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_224), u1_pre_topc(B_224))) | ~m1_pre_topc(B_224, A_225) | ~l1_pre_topc(A_225))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.73  tff(c_1347, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1318, c_1345])).
% 3.87/1.73  tff(c_1352, plain, (v1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26, c_1347])).
% 3.87/1.73  tff(c_1385, plain, (![C_231, A_232, D_233, B_234]: (C_231=A_232 | g1_pre_topc(C_231, D_233)!=g1_pre_topc(A_232, B_234) | ~m1_subset_1(B_234, k1_zfmisc_1(k1_zfmisc_1(A_232))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.87/1.73  tff(c_1394, plain, (![A_235, B_236]: (u1_struct_0('#skF_2')=A_235 | g1_pre_topc(A_235, B_236)!='#skF_3' | ~m1_subset_1(B_236, k1_zfmisc_1(k1_zfmisc_1(A_235))))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1385])).
% 3.87/1.73  tff(c_1399, plain, (![A_237]: (u1_struct_0(A_237)=u1_struct_0('#skF_2') | g1_pre_topc(u1_struct_0(A_237), u1_pre_topc(A_237))!='#skF_3' | ~l1_pre_topc(A_237))), inference(resolution, [status(thm)], [c_4, c_1394])).
% 3.87/1.73  tff(c_1440, plain, (![A_245]: (u1_struct_0(A_245)=u1_struct_0('#skF_2') | A_245!='#skF_3' | ~l1_pre_topc(A_245) | ~v1_pre_topc(A_245) | ~l1_pre_topc(A_245))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1399])).
% 3.87/1.73  tff(c_1446, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_1352, c_1440])).
% 3.87/1.73  tff(c_1450, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1446])).
% 3.87/1.73  tff(c_1538, plain, (![B_246, A_247]: (v4_pre_topc(u1_struct_0(B_246), A_247) | ~v1_borsuk_1(B_246, A_247) | ~m1_subset_1(u1_struct_0(B_246), k1_zfmisc_1(u1_struct_0(A_247))) | ~m1_pre_topc(B_246, A_247) | ~l1_pre_topc(A_247) | ~v2_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.87/1.73  tff(c_1779, plain, (![B_264, A_265]: (v4_pre_topc(u1_struct_0(B_264), A_265) | ~v1_borsuk_1(B_264, A_265) | ~v2_pre_topc(A_265) | ~m1_pre_topc(B_264, A_265) | ~l1_pre_topc(A_265))), inference(resolution, [status(thm)], [c_24, c_1538])).
% 3.87/1.73  tff(c_1819, plain, (![A_270]: (v4_pre_topc(u1_struct_0('#skF_3'), A_270) | ~v1_borsuk_1('#skF_2', A_270) | ~v2_pre_topc(A_270) | ~m1_pre_topc('#skF_2', A_270) | ~l1_pre_topc(A_270))), inference(superposition, [status(thm), theory('equality')], [c_1450, c_1779])).
% 3.87/1.73  tff(c_1618, plain, (![B_254, A_255]: (v1_borsuk_1(B_254, A_255) | ~v4_pre_topc(u1_struct_0(B_254), A_255) | ~m1_subset_1(u1_struct_0(B_254), k1_zfmisc_1(u1_struct_0(A_255))) | ~m1_pre_topc(B_254, A_255) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.87/1.73  tff(c_1637, plain, (![B_28, A_26]: (v1_borsuk_1(B_28, A_26) | ~v4_pre_topc(u1_struct_0(B_28), A_26) | ~v2_pre_topc(A_26) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(resolution, [status(thm)], [c_24, c_1618])).
% 3.87/1.73  tff(c_1977, plain, (![A_286]: (v1_borsuk_1('#skF_3', A_286) | ~m1_pre_topc('#skF_3', A_286) | ~v1_borsuk_1('#skF_2', A_286) | ~v2_pre_topc(A_286) | ~m1_pre_topc('#skF_2', A_286) | ~l1_pre_topc(A_286))), inference(resolution, [status(thm)], [c_1819, c_1637])).
% 3.87/1.73  tff(c_1983, plain, (v1_borsuk_1('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1315, c_1977])).
% 3.87/1.73  tff(c_1987, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1318, c_38, c_1317, c_1983])).
% 3.87/1.73  tff(c_1989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1316, c_1987])).
% 3.87/1.73  tff(c_1991, plain, (~m1_pre_topc('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.87/1.73  tff(c_1990, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_48])).
% 3.87/1.73  tff(c_2030, plain, (![B_293, A_294]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_293), u1_pre_topc(B_293)), A_294) | ~m1_pre_topc(B_293, A_294) | ~l1_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.73  tff(c_2040, plain, (![A_295]: (m1_pre_topc('#skF_3', A_295) | ~m1_pre_topc('#skF_2', A_295) | ~l1_pre_topc(A_295))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2030])).
% 3.87/1.73  tff(c_2043, plain, (m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_1990, c_2040])).
% 3.87/1.73  tff(c_2046, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2043])).
% 3.87/1.73  tff(c_2048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1991, c_2046])).
% 3.87/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.73  
% 3.87/1.73  Inference rules
% 3.87/1.73  ----------------------
% 3.87/1.73  #Ref     : 24
% 3.87/1.73  #Sup     : 396
% 3.87/1.73  #Fact    : 0
% 3.87/1.73  #Define  : 0
% 3.87/1.73  #Split   : 18
% 3.87/1.73  #Chain   : 0
% 3.87/1.73  #Close   : 0
% 3.87/1.73  
% 3.87/1.73  Ordering : KBO
% 3.87/1.73  
% 3.87/1.73  Simplification rules
% 3.87/1.73  ----------------------
% 3.87/1.73  #Subsume      : 131
% 3.87/1.73  #Demod        : 390
% 3.87/1.73  #Tautology    : 162
% 3.87/1.73  #SimpNegUnit  : 11
% 3.87/1.73  #BackRed      : 21
% 3.87/1.73  
% 3.87/1.73  #Partial instantiations: 0
% 3.87/1.73  #Strategies tried      : 1
% 3.87/1.73  
% 3.87/1.73  Timing (in seconds)
% 3.87/1.73  ----------------------
% 3.87/1.74  Preprocessing        : 0.32
% 3.87/1.74  Parsing              : 0.18
% 3.87/1.74  CNF conversion       : 0.02
% 3.87/1.74  Main loop            : 0.58
% 3.87/1.74  Inferencing          : 0.21
% 3.87/1.74  Reduction            : 0.18
% 3.87/1.74  Demodulation         : 0.13
% 3.87/1.74  BG Simplification    : 0.03
% 3.87/1.74  Subsumption          : 0.12
% 3.87/1.74  Abstraction          : 0.03
% 3.87/1.74  MUC search           : 0.00
% 3.87/1.74  Cooper               : 0.00
% 3.87/1.74  Total                : 0.95
% 3.87/1.74  Index Insertion      : 0.00
% 3.87/1.74  Index Deletion       : 0.00
% 3.87/1.74  Index Matching       : 0.00
% 3.87/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
