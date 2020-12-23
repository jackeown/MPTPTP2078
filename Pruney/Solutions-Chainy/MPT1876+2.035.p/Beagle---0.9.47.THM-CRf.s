%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:55 EST 2020

% Result     : Theorem 9.93s
% Output     : CNFRefutation 10.15s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 904 expanded)
%              Number of leaves         :   44 ( 327 expanded)
%              Depth                    :   30
%              Number of atoms          :  397 (2799 expanded)
%              Number of equality atoms :   17 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_198,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v2_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
           => ( v2_tex_2(B,A)
            <=> v1_zfmisc_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_137,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_178,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_166,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ~ ( v2_tex_2(B,A)
              & ! [C] :
                  ( ( ~ v2_struct_0(C)
                    & v1_pre_topc(C)
                    & v1_tdlat_3(C)
                    & m1_pre_topc(C,A) )
                 => B != u1_struct_0(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_124,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_tdlat_3(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v2_tdlat_3(A)
       => v2_pre_topc(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & v2_tdlat_3(A) )
       => ( ~ v2_struct_0(A)
          & v7_struct_0(A)
          & v2_pre_topc(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_68,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_78,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_81,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_72,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_83,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_72])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_tarski(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_154,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k1_tarski(A_64),k1_zfmisc_1(B_65))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_161,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k1_tarski(A_64),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_154,c_24])).

tff(c_305,plain,(
    ! [B_95,A_96] :
      ( B_95 = A_96
      | ~ r1_tarski(A_96,B_95)
      | ~ v1_zfmisc_1(B_95)
      | v1_xboole_0(B_95)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_314,plain,(
    ! [A_64,B_65] :
      ( k1_tarski(A_64) = B_65
      | ~ v1_zfmisc_1(B_65)
      | v1_xboole_0(B_65)
      | v1_xboole_0(k1_tarski(A_64))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_161,c_305])).

tff(c_337,plain,(
    ! [A_97,B_98] :
      ( k1_tarski(A_97) = B_98
      | ~ v1_zfmisc_1(B_98)
      | v1_xboole_0(B_98)
      | ~ r2_hidden(A_97,B_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_314])).

tff(c_353,plain,(
    ! [A_1] :
      ( k1_tarski('#skF_1'(A_1)) = A_1
      | ~ v1_zfmisc_1(A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_337])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_116,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(A_57,B_58)
      | ~ m1_subset_1(A_57,k1_zfmisc_1(B_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_129,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_191,plain,(
    ! [C_80,B_81,A_82] :
      ( r2_hidden(C_80,B_81)
      | ~ r2_hidden(C_80,A_82)
      | ~ r1_tarski(A_82,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_201,plain,(
    ! [A_83,B_84] :
      ( r2_hidden('#skF_1'(A_83),B_84)
      | ~ r1_tarski(A_83,B_84)
      | v1_xboole_0(A_83) ) ),
    inference(resolution,[status(thm)],[c_4,c_191])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_213,plain,(
    ! [B_85,A_86] :
      ( ~ v1_xboole_0(B_85)
      | ~ r1_tarski(A_86,B_85)
      | v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_201,c_2])).

tff(c_228,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_129,c_213])).

tff(c_236,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_228])).

tff(c_130,plain,(
    ! [B_59,A_60] :
      ( m1_subset_1(B_59,A_60)
      | ~ r2_hidden(B_59,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_134,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_407,plain,(
    ! [B_103,B_104,A_105] :
      ( r2_hidden(B_103,B_104)
      | ~ r1_tarski(A_105,B_104)
      | ~ m1_subset_1(B_103,A_105)
      | v1_xboole_0(A_105) ) ),
    inference(resolution,[status(thm)],[c_16,c_191])).

tff(c_413,plain,(
    ! [B_103,B_65,A_64] :
      ( r2_hidden(B_103,B_65)
      | ~ m1_subset_1(B_103,k1_tarski(A_64))
      | v1_xboole_0(k1_tarski(A_64))
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_161,c_407])).

tff(c_495,plain,(
    ! [B_109,B_110,A_111] :
      ( r2_hidden(B_109,B_110)
      | ~ m1_subset_1(B_109,k1_tarski(A_111))
      | ~ r2_hidden(A_111,B_110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_413])).

tff(c_503,plain,(
    ! [A_111,B_110] :
      ( r2_hidden('#skF_1'(k1_tarski(A_111)),B_110)
      | ~ r2_hidden(A_111,B_110)
      | v1_xboole_0(k1_tarski(A_111)) ) ),
    inference(resolution,[status(thm)],[c_134,c_495])).

tff(c_514,plain,(
    ! [A_112,B_113] :
      ( r2_hidden('#skF_1'(k1_tarski(A_112)),B_113)
      | ~ r2_hidden(A_112,B_113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_503])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_669,plain,(
    ! [A_133,B_134,B_135] :
      ( r2_hidden('#skF_1'(k1_tarski(A_133)),B_134)
      | ~ r1_tarski(B_135,B_134)
      | ~ r2_hidden(A_133,B_135) ) ),
    inference(resolution,[status(thm)],[c_514,c_6])).

tff(c_1608,plain,(
    ! [A_180,B_181,A_182] :
      ( r2_hidden('#skF_1'(k1_tarski(A_180)),B_181)
      | ~ r2_hidden(A_180,k1_tarski(A_182))
      | ~ r2_hidden(A_182,B_181) ) ),
    inference(resolution,[status(thm)],[c_161,c_669])).

tff(c_1626,plain,(
    ! [B_12,B_181,A_182] :
      ( r2_hidden('#skF_1'(k1_tarski(B_12)),B_181)
      | ~ r2_hidden(A_182,B_181)
      | ~ m1_subset_1(B_12,k1_tarski(A_182))
      | v1_xboole_0(k1_tarski(A_182)) ) ),
    inference(resolution,[status(thm)],[c_16,c_1608])).

tff(c_1893,plain,(
    ! [B_194,B_195,A_196] :
      ( r2_hidden('#skF_1'(k1_tarski(B_194)),B_195)
      | ~ r2_hidden(A_196,B_195)
      | ~ m1_subset_1(B_194,k1_tarski(A_196)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_1626])).

tff(c_2052,plain,(
    ! [B_200,A_201] :
      ( r2_hidden('#skF_1'(k1_tarski(B_200)),A_201)
      | ~ m1_subset_1(B_200,k1_tarski('#skF_1'(A_201)))
      | v1_xboole_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_4,c_1893])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ r2_hidden(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2102,plain,(
    ! [B_200,A_201] :
      ( m1_subset_1('#skF_1'(k1_tarski(B_200)),A_201)
      | ~ m1_subset_1(B_200,k1_tarski('#skF_1'(A_201)))
      | v1_xboole_0(A_201) ) ),
    inference(resolution,[status(thm)],[c_2052,c_14])).

tff(c_417,plain,(
    ! [B_103] :
      ( r2_hidden(B_103,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_103,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_129,c_407])).

tff(c_426,plain,(
    ! [B_103] :
      ( r2_hidden(B_103,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_103,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_417])).

tff(c_326,plain,(
    ! [A_64,B_65] :
      ( k1_tarski(A_64) = B_65
      | ~ v1_zfmisc_1(B_65)
      | v1_xboole_0(B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_314])).

tff(c_1418,plain,(
    ! [A_173,B_174] :
      ( k1_tarski('#skF_1'(k1_tarski(A_173))) = B_174
      | ~ v1_zfmisc_1(B_174)
      | v1_xboole_0(B_174)
      | ~ r2_hidden(A_173,B_174) ) ),
    inference(resolution,[status(thm)],[c_514,c_326])).

tff(c_1453,plain,(
    ! [A_176] :
      ( k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_176)))) = A_176
      | ~ v1_zfmisc_1(A_176)
      | v1_xboole_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_4,c_1418])).

tff(c_4566,plain,(
    ! [A_289,B_290] :
      ( r1_tarski(A_289,B_290)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_289))),B_290)
      | ~ v1_zfmisc_1(A_289)
      | v1_xboole_0(A_289) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1453,c_161])).

tff(c_12943,plain,(
    ! [A_485] :
      ( r1_tarski(A_485,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_485)
      | v1_xboole_0(A_485)
      | ~ m1_subset_1('#skF_1'(k1_tarski('#skF_1'(A_485))),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_426,c_4566])).

tff(c_12955,plain,(
    ! [A_485] :
      ( r1_tarski(A_485,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_485)
      | v1_xboole_0(A_485)
      | ~ m1_subset_1('#skF_1'(A_485),k1_tarski('#skF_1'('#skF_5')))
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2102,c_12943])).

tff(c_13064,plain,(
    ! [A_487] :
      ( r1_tarski(A_487,u1_struct_0('#skF_4'))
      | ~ v1_zfmisc_1(A_487)
      | v1_xboole_0(A_487)
      | ~ m1_subset_1('#skF_1'(A_487),k1_tarski('#skF_1'('#skF_5'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_12955])).

tff(c_13098,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))
    | v1_xboole_0(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_134,c_13064])).

tff(c_13129,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_12,c_13098])).

tff(c_13131,plain,(
    ~ v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_13129])).

tff(c_13134,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_13131])).

tff(c_13136,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_81,c_13134])).

tff(c_13138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_13136])).

tff(c_13139,plain,(
    r1_tarski(k1_tarski('#skF_1'('#skF_5')),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_13129])).

tff(c_200,plain,(
    ! [A_1,B_81] :
      ( r2_hidden('#skF_1'(A_1),B_81)
      | ~ r1_tarski(A_1,B_81)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_191])).

tff(c_512,plain,(
    ! [A_111,B_110] :
      ( r2_hidden('#skF_1'(k1_tarski(A_111)),B_110)
      | ~ r2_hidden(A_111,B_110) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_503])).

tff(c_10158,plain,(
    ! [A_415,B_416] :
      ( r2_hidden('#skF_1'(A_415),B_416)
      | ~ r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_415))),B_416)
      | ~ v1_zfmisc_1(A_415)
      | v1_xboole_0(A_415) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1453,c_512])).

tff(c_10252,plain,(
    ! [A_415,B_81] :
      ( r2_hidden('#skF_1'(A_415),B_81)
      | ~ v1_zfmisc_1(A_415)
      | v1_xboole_0(A_415)
      | ~ r1_tarski(k1_tarski('#skF_1'(A_415)),B_81)
      | v1_xboole_0(k1_tarski('#skF_1'(A_415))) ) ),
    inference(resolution,[status(thm)],[c_200,c_10158])).

tff(c_10301,plain,(
    ! [A_415,B_81] :
      ( r2_hidden('#skF_1'(A_415),B_81)
      | ~ v1_zfmisc_1(A_415)
      | v1_xboole_0(A_415)
      | ~ r1_tarski(k1_tarski('#skF_1'(A_415)),B_81) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_10252])).

tff(c_13154,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_13139,c_10301])).

tff(c_13209,plain,
    ( r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_13154])).

tff(c_13210,plain,(
    r2_hidden('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_13209])).

tff(c_13287,plain,
    ( m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_13210,c_14])).

tff(c_13314,plain,(
    m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_13287])).

tff(c_34,plain,(
    ! [A_22,B_23] :
      ( k6_domain_1(A_22,B_23) = k1_tarski(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_13337,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_13314,c_34])).

tff(c_13365,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_1'('#skF_5')) = k1_tarski('#skF_1'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_13337])).

tff(c_58,plain,(
    ! [A_38,B_40] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_38),B_40),A_38)
      | ~ m1_subset_1(B_40,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_13560,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_13365,c_58])).

tff(c_13584,plain,
    ( v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_13314,c_13560])).

tff(c_13585,plain,(
    v2_tex_2(k1_tarski('#skF_1'('#skF_5')),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_13584])).

tff(c_13599,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_13585])).

tff(c_13601,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_13599])).

tff(c_13603,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_83,c_13601])).

tff(c_13604,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_14905,plain,(
    ! [A_619,B_620] :
      ( m1_pre_topc('#skF_3'(A_619,B_620),A_619)
      | ~ v2_tex_2(B_620,A_619)
      | ~ m1_subset_1(B_620,k1_zfmisc_1(u1_struct_0(A_619)))
      | v1_xboole_0(B_620)
      | ~ l1_pre_topc(A_619)
      | ~ v2_pre_topc(A_619)
      | v2_struct_0(A_619) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_14928,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_14905])).

tff(c_14940,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_13604,c_14928])).

tff(c_14941,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_14940])).

tff(c_30,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14947,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14941,c_30])).

tff(c_14954,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_14947])).

tff(c_28,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14122,plain,(
    ! [A_571,B_572] :
      ( ~ v2_struct_0('#skF_3'(A_571,B_572))
      | ~ v2_tex_2(B_572,A_571)
      | ~ m1_subset_1(B_572,k1_zfmisc_1(u1_struct_0(A_571)))
      | v1_xboole_0(B_572)
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_14149,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_14122])).

tff(c_14160,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_13604,c_14149])).

tff(c_14161,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_14160])).

tff(c_66,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_44,plain,(
    ! [B_28,A_26] :
      ( v2_tdlat_3(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_14944,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_14941,c_44])).

tff(c_14950,plain,
    ( v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_14944])).

tff(c_14951,plain,(
    v2_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_14950])).

tff(c_36,plain,(
    ! [A_24] :
      ( v2_pre_topc(A_24)
      | ~ v2_tdlat_3(A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_14958,plain,
    ( v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_14951,c_36])).

tff(c_14960,plain,(
    v2_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14954,c_14958])).

tff(c_14569,plain,(
    ! [A_601,B_602] :
      ( v1_tdlat_3('#skF_3'(A_601,B_602))
      | ~ v2_tex_2(B_602,A_601)
      | ~ m1_subset_1(B_602,k1_zfmisc_1(u1_struct_0(A_601)))
      | v1_xboole_0(B_602)
      | ~ l1_pre_topc(A_601)
      | ~ v2_pre_topc(A_601)
      | v2_struct_0(A_601) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_14600,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_14569])).

tff(c_14612,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_13604,c_14600])).

tff(c_14613,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_14612])).

tff(c_40,plain,(
    ! [A_25] :
      ( v7_struct_0(A_25)
      | ~ v2_tdlat_3(A_25)
      | ~ v1_tdlat_3(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_13605,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_15124,plain,(
    ! [A_627,B_628] :
      ( u1_struct_0('#skF_3'(A_627,B_628)) = B_628
      | ~ v2_tex_2(B_628,A_627)
      | ~ m1_subset_1(B_628,k1_zfmisc_1(u1_struct_0(A_627)))
      | v1_xboole_0(B_628)
      | ~ l1_pre_topc(A_627)
      | ~ v2_pre_topc(A_627)
      | v2_struct_0(A_627) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_15159,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | ~ v2_tex_2('#skF_5','#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_15124])).

tff(c_15172,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_13604,c_15159])).

tff(c_15173,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_62,c_15172])).

tff(c_32,plain,(
    ! [A_21] :
      ( v1_zfmisc_1(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | ~ v7_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_15194,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15173,c_32])).

tff(c_15215,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_13605,c_15194])).

tff(c_15222,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_15215])).

tff(c_15231,plain,
    ( ~ v2_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_40,c_15222])).

tff(c_15234,plain,(
    v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14954,c_14960,c_14613,c_14951,c_15231])).

tff(c_15236,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14161,c_15234])).

tff(c_15237,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_15215])).

tff(c_15241,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_28,c_15237])).

tff(c_15245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14954,c_15241])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:18:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.93/3.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.93/3.79  
% 9.93/3.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.93/3.79  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 9.93/3.79  
% 9.93/3.79  %Foreground sorts:
% 9.93/3.79  
% 9.93/3.79  
% 9.93/3.79  %Background operators:
% 9.93/3.79  
% 9.93/3.79  
% 9.93/3.79  %Foreground operators:
% 9.93/3.79  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.93/3.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.93/3.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.93/3.79  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.93/3.79  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.93/3.79  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 9.93/3.79  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.93/3.79  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 9.93/3.79  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.93/3.79  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 9.93/3.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.93/3.79  tff('#skF_5', type, '#skF_5': $i).
% 9.93/3.79  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 9.93/3.79  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 9.93/3.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.93/3.79  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.93/3.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.93/3.79  tff('#skF_4', type, '#skF_4': $i).
% 9.93/3.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.93/3.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.93/3.79  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 9.93/3.79  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 9.93/3.79  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.93/3.79  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.93/3.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.93/3.79  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 9.93/3.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.93/3.79  
% 10.15/3.81  tff(f_198, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 10.15/3.81  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 10.15/3.81  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 10.15/3.81  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 10.15/3.81  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 10.15/3.81  tff(f_137, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 10.15/3.81  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 10.15/3.81  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 10.15/3.81  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 10.15/3.81  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 10.15/3.81  tff(f_166, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 10.15/3.81  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 10.15/3.81  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 10.15/3.81  tff(f_124, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_tdlat_3(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_tdlat_3)).
% 10.15/3.81  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (v2_tdlat_3(A) => v2_pre_topc(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tdlat_3)).
% 10.15/3.81  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & v2_tdlat_3(A)) => ((~v2_struct_0(A) & v7_struct_0(A)) & v2_pre_topc(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_1)).
% 10.15/3.81  tff(f_79, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 10.15/3.81  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.15/3.81  tff(c_70, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.15/3.81  tff(c_62, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.15/3.81  tff(c_68, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.15/3.81  tff(c_78, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.15/3.81  tff(c_81, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 10.15/3.81  tff(c_72, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.15/3.81  tff(c_83, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_72])).
% 10.15/3.81  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.15/3.81  tff(c_12, plain, (![A_10]: (~v1_xboole_0(k1_tarski(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.15/3.81  tff(c_154, plain, (![A_64, B_65]: (m1_subset_1(k1_tarski(A_64), k1_zfmisc_1(B_65)) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.15/3.81  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.15/3.81  tff(c_161, plain, (![A_64, B_65]: (r1_tarski(k1_tarski(A_64), B_65) | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_154, c_24])).
% 10.15/3.81  tff(c_305, plain, (![B_95, A_96]: (B_95=A_96 | ~r1_tarski(A_96, B_95) | ~v1_zfmisc_1(B_95) | v1_xboole_0(B_95) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_137])).
% 10.15/3.81  tff(c_314, plain, (![A_64, B_65]: (k1_tarski(A_64)=B_65 | ~v1_zfmisc_1(B_65) | v1_xboole_0(B_65) | v1_xboole_0(k1_tarski(A_64)) | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_161, c_305])).
% 10.15/3.81  tff(c_337, plain, (![A_97, B_98]: (k1_tarski(A_97)=B_98 | ~v1_zfmisc_1(B_98) | v1_xboole_0(B_98) | ~r2_hidden(A_97, B_98))), inference(negUnitSimplification, [status(thm)], [c_12, c_314])).
% 10.15/3.81  tff(c_353, plain, (![A_1]: (k1_tarski('#skF_1'(A_1))=A_1 | ~v1_zfmisc_1(A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_337])).
% 10.15/3.81  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.15/3.81  tff(c_116, plain, (![A_57, B_58]: (r1_tarski(A_57, B_58) | ~m1_subset_1(A_57, k1_zfmisc_1(B_58)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.15/3.81  tff(c_129, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_116])).
% 10.15/3.81  tff(c_191, plain, (![C_80, B_81, A_82]: (r2_hidden(C_80, B_81) | ~r2_hidden(C_80, A_82) | ~r1_tarski(A_82, B_81))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.15/3.81  tff(c_201, plain, (![A_83, B_84]: (r2_hidden('#skF_1'(A_83), B_84) | ~r1_tarski(A_83, B_84) | v1_xboole_0(A_83))), inference(resolution, [status(thm)], [c_4, c_191])).
% 10.15/3.81  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.15/3.81  tff(c_213, plain, (![B_85, A_86]: (~v1_xboole_0(B_85) | ~r1_tarski(A_86, B_85) | v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_201, c_2])).
% 10.15/3.81  tff(c_228, plain, (~v1_xboole_0(u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_129, c_213])).
% 10.15/3.81  tff(c_236, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_228])).
% 10.15/3.81  tff(c_130, plain, (![B_59, A_60]: (m1_subset_1(B_59, A_60) | ~r2_hidden(B_59, A_60) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.15/3.81  tff(c_134, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_130])).
% 10.15/3.81  tff(c_16, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.15/3.81  tff(c_407, plain, (![B_103, B_104, A_105]: (r2_hidden(B_103, B_104) | ~r1_tarski(A_105, B_104) | ~m1_subset_1(B_103, A_105) | v1_xboole_0(A_105))), inference(resolution, [status(thm)], [c_16, c_191])).
% 10.15/3.81  tff(c_413, plain, (![B_103, B_65, A_64]: (r2_hidden(B_103, B_65) | ~m1_subset_1(B_103, k1_tarski(A_64)) | v1_xboole_0(k1_tarski(A_64)) | ~r2_hidden(A_64, B_65))), inference(resolution, [status(thm)], [c_161, c_407])).
% 10.15/3.81  tff(c_495, plain, (![B_109, B_110, A_111]: (r2_hidden(B_109, B_110) | ~m1_subset_1(B_109, k1_tarski(A_111)) | ~r2_hidden(A_111, B_110))), inference(negUnitSimplification, [status(thm)], [c_12, c_413])).
% 10.15/3.81  tff(c_503, plain, (![A_111, B_110]: (r2_hidden('#skF_1'(k1_tarski(A_111)), B_110) | ~r2_hidden(A_111, B_110) | v1_xboole_0(k1_tarski(A_111)))), inference(resolution, [status(thm)], [c_134, c_495])).
% 10.15/3.81  tff(c_514, plain, (![A_112, B_113]: (r2_hidden('#skF_1'(k1_tarski(A_112)), B_113) | ~r2_hidden(A_112, B_113))), inference(negUnitSimplification, [status(thm)], [c_12, c_503])).
% 10.15/3.81  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.15/3.81  tff(c_669, plain, (![A_133, B_134, B_135]: (r2_hidden('#skF_1'(k1_tarski(A_133)), B_134) | ~r1_tarski(B_135, B_134) | ~r2_hidden(A_133, B_135))), inference(resolution, [status(thm)], [c_514, c_6])).
% 10.15/3.81  tff(c_1608, plain, (![A_180, B_181, A_182]: (r2_hidden('#skF_1'(k1_tarski(A_180)), B_181) | ~r2_hidden(A_180, k1_tarski(A_182)) | ~r2_hidden(A_182, B_181))), inference(resolution, [status(thm)], [c_161, c_669])).
% 10.15/3.81  tff(c_1626, plain, (![B_12, B_181, A_182]: (r2_hidden('#skF_1'(k1_tarski(B_12)), B_181) | ~r2_hidden(A_182, B_181) | ~m1_subset_1(B_12, k1_tarski(A_182)) | v1_xboole_0(k1_tarski(A_182)))), inference(resolution, [status(thm)], [c_16, c_1608])).
% 10.15/3.81  tff(c_1893, plain, (![B_194, B_195, A_196]: (r2_hidden('#skF_1'(k1_tarski(B_194)), B_195) | ~r2_hidden(A_196, B_195) | ~m1_subset_1(B_194, k1_tarski(A_196)))), inference(negUnitSimplification, [status(thm)], [c_12, c_1626])).
% 10.15/3.81  tff(c_2052, plain, (![B_200, A_201]: (r2_hidden('#skF_1'(k1_tarski(B_200)), A_201) | ~m1_subset_1(B_200, k1_tarski('#skF_1'(A_201))) | v1_xboole_0(A_201))), inference(resolution, [status(thm)], [c_4, c_1893])).
% 10.15/3.81  tff(c_14, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~r2_hidden(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.15/3.81  tff(c_2102, plain, (![B_200, A_201]: (m1_subset_1('#skF_1'(k1_tarski(B_200)), A_201) | ~m1_subset_1(B_200, k1_tarski('#skF_1'(A_201))) | v1_xboole_0(A_201))), inference(resolution, [status(thm)], [c_2052, c_14])).
% 10.15/3.81  tff(c_417, plain, (![B_103]: (r2_hidden(B_103, u1_struct_0('#skF_4')) | ~m1_subset_1(B_103, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_129, c_407])).
% 10.15/3.81  tff(c_426, plain, (![B_103]: (r2_hidden(B_103, u1_struct_0('#skF_4')) | ~m1_subset_1(B_103, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_62, c_417])).
% 10.15/3.81  tff(c_326, plain, (![A_64, B_65]: (k1_tarski(A_64)=B_65 | ~v1_zfmisc_1(B_65) | v1_xboole_0(B_65) | ~r2_hidden(A_64, B_65))), inference(negUnitSimplification, [status(thm)], [c_12, c_314])).
% 10.15/3.81  tff(c_1418, plain, (![A_173, B_174]: (k1_tarski('#skF_1'(k1_tarski(A_173)))=B_174 | ~v1_zfmisc_1(B_174) | v1_xboole_0(B_174) | ~r2_hidden(A_173, B_174))), inference(resolution, [status(thm)], [c_514, c_326])).
% 10.15/3.81  tff(c_1453, plain, (![A_176]: (k1_tarski('#skF_1'(k1_tarski('#skF_1'(A_176))))=A_176 | ~v1_zfmisc_1(A_176) | v1_xboole_0(A_176))), inference(resolution, [status(thm)], [c_4, c_1418])).
% 10.15/3.81  tff(c_4566, plain, (![A_289, B_290]: (r1_tarski(A_289, B_290) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_289))), B_290) | ~v1_zfmisc_1(A_289) | v1_xboole_0(A_289))), inference(superposition, [status(thm), theory('equality')], [c_1453, c_161])).
% 10.15/3.81  tff(c_12943, plain, (![A_485]: (r1_tarski(A_485, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_485) | v1_xboole_0(A_485) | ~m1_subset_1('#skF_1'(k1_tarski('#skF_1'(A_485))), '#skF_5'))), inference(resolution, [status(thm)], [c_426, c_4566])).
% 10.15/3.81  tff(c_12955, plain, (![A_485]: (r1_tarski(A_485, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_485) | v1_xboole_0(A_485) | ~m1_subset_1('#skF_1'(A_485), k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_2102, c_12943])).
% 10.15/3.81  tff(c_13064, plain, (![A_487]: (r1_tarski(A_487, u1_struct_0('#skF_4')) | ~v1_zfmisc_1(A_487) | v1_xboole_0(A_487) | ~m1_subset_1('#skF_1'(A_487), k1_tarski('#skF_1'('#skF_5'))))), inference(negUnitSimplification, [status(thm)], [c_62, c_12955])).
% 10.15/3.81  tff(c_13098, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5'))) | v1_xboole_0(k1_tarski('#skF_1'('#skF_5')))), inference(resolution, [status(thm)], [c_134, c_13064])).
% 10.15/3.81  tff(c_13129, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4')) | ~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_12, c_12, c_13098])).
% 10.15/3.81  tff(c_13131, plain, (~v1_zfmisc_1(k1_tarski('#skF_1'('#skF_5')))), inference(splitLeft, [status(thm)], [c_13129])).
% 10.15/3.81  tff(c_13134, plain, (~v1_zfmisc_1('#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_353, c_13131])).
% 10.15/3.81  tff(c_13136, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_81, c_13134])).
% 10.15/3.81  tff(c_13138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_13136])).
% 10.15/3.81  tff(c_13139, plain, (r1_tarski(k1_tarski('#skF_1'('#skF_5')), u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_13129])).
% 10.15/3.81  tff(c_200, plain, (![A_1, B_81]: (r2_hidden('#skF_1'(A_1), B_81) | ~r1_tarski(A_1, B_81) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_191])).
% 10.15/3.81  tff(c_512, plain, (![A_111, B_110]: (r2_hidden('#skF_1'(k1_tarski(A_111)), B_110) | ~r2_hidden(A_111, B_110))), inference(negUnitSimplification, [status(thm)], [c_12, c_503])).
% 10.15/3.81  tff(c_10158, plain, (![A_415, B_416]: (r2_hidden('#skF_1'(A_415), B_416) | ~r2_hidden('#skF_1'(k1_tarski('#skF_1'(A_415))), B_416) | ~v1_zfmisc_1(A_415) | v1_xboole_0(A_415))), inference(superposition, [status(thm), theory('equality')], [c_1453, c_512])).
% 10.15/3.81  tff(c_10252, plain, (![A_415, B_81]: (r2_hidden('#skF_1'(A_415), B_81) | ~v1_zfmisc_1(A_415) | v1_xboole_0(A_415) | ~r1_tarski(k1_tarski('#skF_1'(A_415)), B_81) | v1_xboole_0(k1_tarski('#skF_1'(A_415))))), inference(resolution, [status(thm)], [c_200, c_10158])).
% 10.15/3.81  tff(c_10301, plain, (![A_415, B_81]: (r2_hidden('#skF_1'(A_415), B_81) | ~v1_zfmisc_1(A_415) | v1_xboole_0(A_415) | ~r1_tarski(k1_tarski('#skF_1'(A_415)), B_81))), inference(negUnitSimplification, [status(thm)], [c_12, c_10252])).
% 10.15/3.81  tff(c_13154, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_13139, c_10301])).
% 10.15/3.81  tff(c_13209, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_13154])).
% 10.15/3.81  tff(c_13210, plain, (r2_hidden('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_13209])).
% 10.15/3.81  tff(c_13287, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_13210, c_14])).
% 10.15/3.81  tff(c_13314, plain, (m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_236, c_13287])).
% 10.15/3.81  tff(c_34, plain, (![A_22, B_23]: (k6_domain_1(A_22, B_23)=k1_tarski(B_23) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.15/3.81  tff(c_13337, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_13314, c_34])).
% 10.15/3.81  tff(c_13365, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_1'('#skF_5'))=k1_tarski('#skF_1'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_236, c_13337])).
% 10.15/3.81  tff(c_58, plain, (![A_38, B_40]: (v2_tex_2(k6_domain_1(u1_struct_0(A_38), B_40), A_38) | ~m1_subset_1(B_40, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_178])).
% 10.15/3.81  tff(c_13560, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_5'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_13365, c_58])).
% 10.15/3.81  tff(c_13584, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_13314, c_13560])).
% 10.15/3.81  tff(c_13585, plain, (v2_tex_2(k1_tarski('#skF_1'('#skF_5')), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_13584])).
% 10.15/3.81  tff(c_13599, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_353, c_13585])).
% 10.15/3.81  tff(c_13601, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_13599])).
% 10.15/3.81  tff(c_13603, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_83, c_13601])).
% 10.15/3.81  tff(c_13604, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_78])).
% 10.15/3.81  tff(c_14905, plain, (![A_619, B_620]: (m1_pre_topc('#skF_3'(A_619, B_620), A_619) | ~v2_tex_2(B_620, A_619) | ~m1_subset_1(B_620, k1_zfmisc_1(u1_struct_0(A_619))) | v1_xboole_0(B_620) | ~l1_pre_topc(A_619) | ~v2_pre_topc(A_619) | v2_struct_0(A_619))), inference(cnfTransformation, [status(thm)], [f_166])).
% 10.15/3.81  tff(c_14928, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_14905])).
% 10.15/3.81  tff(c_14940, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_13604, c_14928])).
% 10.15/3.81  tff(c_14941, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_14940])).
% 10.15/3.81  tff(c_30, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.15/3.81  tff(c_14947, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14941, c_30])).
% 10.15/3.81  tff(c_14954, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_14947])).
% 10.15/3.81  tff(c_28, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 10.15/3.81  tff(c_14122, plain, (![A_571, B_572]: (~v2_struct_0('#skF_3'(A_571, B_572)) | ~v2_tex_2(B_572, A_571) | ~m1_subset_1(B_572, k1_zfmisc_1(u1_struct_0(A_571))) | v1_xboole_0(B_572) | ~l1_pre_topc(A_571) | ~v2_pre_topc(A_571) | v2_struct_0(A_571))), inference(cnfTransformation, [status(thm)], [f_166])).
% 10.15/3.81  tff(c_14149, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_14122])).
% 10.15/3.81  tff(c_14160, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_13604, c_14149])).
% 10.15/3.81  tff(c_14161, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_14160])).
% 10.15/3.81  tff(c_66, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.15/3.81  tff(c_44, plain, (![B_28, A_26]: (v2_tdlat_3(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.15/3.81  tff(c_14944, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_14941, c_44])).
% 10.15/3.81  tff(c_14950, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_14944])).
% 10.15/3.81  tff(c_14951, plain, (v2_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_14950])).
% 10.15/3.81  tff(c_36, plain, (![A_24]: (v2_pre_topc(A_24) | ~v2_tdlat_3(A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.15/3.81  tff(c_14958, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_14951, c_36])).
% 10.15/3.81  tff(c_14960, plain, (v2_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14954, c_14958])).
% 10.15/3.81  tff(c_14569, plain, (![A_601, B_602]: (v1_tdlat_3('#skF_3'(A_601, B_602)) | ~v2_tex_2(B_602, A_601) | ~m1_subset_1(B_602, k1_zfmisc_1(u1_struct_0(A_601))) | v1_xboole_0(B_602) | ~l1_pre_topc(A_601) | ~v2_pre_topc(A_601) | v2_struct_0(A_601))), inference(cnfTransformation, [status(thm)], [f_166])).
% 10.15/3.81  tff(c_14600, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_14569])).
% 10.15/3.81  tff(c_14612, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_13604, c_14600])).
% 10.15/3.81  tff(c_14613, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_14612])).
% 10.15/3.81  tff(c_40, plain, (![A_25]: (v7_struct_0(A_25) | ~v2_tdlat_3(A_25) | ~v1_tdlat_3(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.15/3.81  tff(c_13605, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 10.15/3.81  tff(c_15124, plain, (![A_627, B_628]: (u1_struct_0('#skF_3'(A_627, B_628))=B_628 | ~v2_tex_2(B_628, A_627) | ~m1_subset_1(B_628, k1_zfmisc_1(u1_struct_0(A_627))) | v1_xboole_0(B_628) | ~l1_pre_topc(A_627) | ~v2_pre_topc(A_627) | v2_struct_0(A_627))), inference(cnfTransformation, [status(thm)], [f_166])).
% 10.15/3.81  tff(c_15159, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | ~v2_tex_2('#skF_5', '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_15124])).
% 10.15/3.81  tff(c_15172, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_13604, c_15159])).
% 10.15/3.81  tff(c_15173, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_70, c_62, c_15172])).
% 10.15/3.81  tff(c_32, plain, (![A_21]: (v1_zfmisc_1(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | ~v7_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.15/3.81  tff(c_15194, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15173, c_32])).
% 10.15/3.81  tff(c_15215, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_13605, c_15194])).
% 10.15/3.81  tff(c_15222, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_15215])).
% 10.15/3.81  tff(c_15231, plain, (~v2_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_15222])).
% 10.15/3.81  tff(c_15234, plain, (v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14954, c_14960, c_14613, c_14951, c_15231])).
% 10.15/3.81  tff(c_15236, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14161, c_15234])).
% 10.15/3.81  tff(c_15237, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_15215])).
% 10.15/3.81  tff(c_15241, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_28, c_15237])).
% 10.15/3.81  tff(c_15245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14954, c_15241])).
% 10.15/3.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.15/3.81  
% 10.15/3.81  Inference rules
% 10.15/3.81  ----------------------
% 10.15/3.81  #Ref     : 0
% 10.15/3.81  #Sup     : 3441
% 10.15/3.81  #Fact    : 0
% 10.15/3.81  #Define  : 0
% 10.15/3.81  #Split   : 19
% 10.15/3.81  #Chain   : 0
% 10.15/3.81  #Close   : 0
% 10.15/3.81  
% 10.15/3.81  Ordering : KBO
% 10.15/3.81  
% 10.15/3.81  Simplification rules
% 10.15/3.82  ----------------------
% 10.15/3.82  #Subsume      : 1117
% 10.15/3.82  #Demod        : 413
% 10.15/3.82  #Tautology    : 478
% 10.15/3.82  #SimpNegUnit  : 1184
% 10.15/3.82  #BackRed      : 0
% 10.15/3.82  
% 10.15/3.82  #Partial instantiations: 0
% 10.15/3.82  #Strategies tried      : 1
% 10.15/3.82  
% 10.15/3.82  Timing (in seconds)
% 10.15/3.82  ----------------------
% 10.15/3.82  Preprocessing        : 0.37
% 10.15/3.82  Parsing              : 0.19
% 10.15/3.82  CNF conversion       : 0.03
% 10.15/3.82  Main loop            : 2.61
% 10.15/3.82  Inferencing          : 0.76
% 10.15/3.82  Reduction            : 0.69
% 10.15/3.82  Demodulation         : 0.40
% 10.15/3.82  BG Simplification    : 0.08
% 10.15/3.82  Subsumption          : 0.89
% 10.15/3.82  Abstraction          : 0.13
% 10.15/3.82  MUC search           : 0.00
% 10.15/3.82  Cooper               : 0.00
% 10.15/3.82  Total                : 3.03
% 10.15/3.82  Index Insertion      : 0.00
% 10.15/3.82  Index Deletion       : 0.00
% 10.15/3.82  Index Matching       : 0.00
% 10.15/3.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
