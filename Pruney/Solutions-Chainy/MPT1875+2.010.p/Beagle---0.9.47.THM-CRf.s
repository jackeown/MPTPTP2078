%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:47 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 210 expanded)
%              Number of leaves         :   34 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :  205 ( 659 expanded)
%              Number of equality atoms :    9 (  20 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => ? [C] :
              ( ~ v2_struct_0(C)
              & v1_pre_topc(C)
              & m1_pre_topc(C,A)
              & B = u1_struct_0(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ~ ( v3_pre_topc(D,A)
                            & k9_subset_1(u1_struct_0(A),B,D) = k6_domain_1(u1_struct_0(A),C) ) ) ) )
           => v2_tex_2(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_tex_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_borsuk_1(B,A)
            & v1_tsep_1(B,A)
            & v1_tdlat_3(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( v2_tex_2(C,A)
                <=> v1_tdlat_3(B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_36,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_40,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_95,plain,(
    ! [A_63,B_64] :
      ( v1_pre_topc('#skF_1'(A_63,B_64))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(u1_struct_0(A_63)))
      | v1_xboole_0(B_64)
      | ~ l1_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_101,plain,
    ( v1_pre_topc('#skF_1'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_109,plain,
    ( v1_pre_topc('#skF_1'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_101])).

tff(c_110,plain,
    ( v1_pre_topc('#skF_1'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_109])).

tff(c_112,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_110])).

tff(c_44,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_283,plain,(
    ! [A_81,B_82] :
      ( r2_hidden('#skF_2'(A_81,B_82),B_82)
      | v2_tex_2(B_82,A_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(u1_struct_0(A_81)))
      | ~ l1_pre_topc(A_81)
      | ~ v2_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_291,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_283])).

tff(c_298,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_291])).

tff(c_299,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_36,c_298])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_59,plain,(
    ! [C_44,B_45,A_46] :
      ( ~ v1_xboole_0(C_44)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(C_44))
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_65,plain,(
    ! [A_2,A_46] :
      ( ~ v1_xboole_0(A_2)
      | ~ r2_hidden(A_46,A_2) ) ),
    inference(resolution,[status(thm)],[c_47,c_59])).

tff(c_303,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_299,c_65])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_303])).

tff(c_309,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_110])).

tff(c_389,plain,(
    ! [A_87,B_88] :
      ( m1_pre_topc('#skF_1'(A_87,B_88),A_87)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(u1_struct_0(A_87)))
      | v1_xboole_0(B_88)
      | ~ l1_pre_topc(A_87)
      | v2_struct_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_397,plain,
    ( m1_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_389])).

tff(c_408,plain,
    ( m1_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_397])).

tff(c_409,plain,(
    m1_pre_topc('#skF_1'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_309,c_408])).

tff(c_76,plain,(
    ! [A_60,B_61] :
      ( ~ v2_struct_0('#skF_1'(A_60,B_61))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | v1_xboole_0(B_61)
      | ~ l1_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_82,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_76])).

tff(c_90,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_82])).

tff(c_91,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_90])).

tff(c_93,plain,(
    ~ v2_struct_0('#skF_1'('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_42,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_12,plain,(
    ! [B_12,A_10] :
      ( v1_tdlat_3(B_12)
      | ~ m1_pre_topc(B_12,A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v1_tdlat_3(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_413,plain,
    ( v1_tdlat_3('#skF_1'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_409,c_12])).

tff(c_416,plain,
    ( v1_tdlat_3('#skF_1'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_40,c_413])).

tff(c_417,plain,(
    v1_tdlat_3('#skF_1'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_416])).

tff(c_310,plain,(
    ! [A_83,B_84] :
      ( u1_struct_0('#skF_1'(A_83,B_84)) = B_84
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | v1_xboole_0(B_84)
      | ~ l1_pre_topc(A_83)
      | v2_struct_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_316,plain,
    ( u1_struct_0('#skF_1'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_310])).

tff(c_324,plain,
    ( u1_struct_0('#skF_1'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_316])).

tff(c_325,plain,(
    u1_struct_0('#skF_1'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_309,c_324])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( m1_subset_1(u1_struct_0(B_8),k1_zfmisc_1(u1_struct_0(A_6)))
      | ~ m1_pre_topc(B_8,A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_777,plain,(
    ! [B_119,A_120] :
      ( v2_tex_2(u1_struct_0(B_119),A_120)
      | ~ v1_tdlat_3(B_119)
      | ~ m1_subset_1(u1_struct_0(B_119),k1_zfmisc_1(u1_struct_0(A_120)))
      | ~ m1_pre_topc(B_119,A_120)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_822,plain,(
    ! [B_122,A_123] :
      ( v2_tex_2(u1_struct_0(B_122),A_123)
      | ~ v1_tdlat_3(B_122)
      | v2_struct_0(B_122)
      | v2_struct_0(A_123)
      | ~ m1_pre_topc(B_122,A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(resolution,[status(thm)],[c_8,c_777])).

tff(c_831,plain,(
    ! [A_123] :
      ( v2_tex_2('#skF_4',A_123)
      | ~ v1_tdlat_3('#skF_1'('#skF_3','#skF_4'))
      | v2_struct_0('#skF_1'('#skF_3','#skF_4'))
      | v2_struct_0(A_123)
      | ~ m1_pre_topc('#skF_1'('#skF_3','#skF_4'),A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_822])).

tff(c_833,plain,(
    ! [A_123] :
      ( v2_tex_2('#skF_4',A_123)
      | v2_struct_0('#skF_1'('#skF_3','#skF_4'))
      | v2_struct_0(A_123)
      | ~ m1_pre_topc('#skF_1'('#skF_3','#skF_4'),A_123)
      | ~ l1_pre_topc(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_417,c_831])).

tff(c_835,plain,(
    ! [A_124] :
      ( v2_tex_2('#skF_4',A_124)
      | v2_struct_0(A_124)
      | ~ m1_pre_topc('#skF_1'('#skF_3','#skF_4'),A_124)
      | ~ l1_pre_topc(A_124) ) ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_833])).

tff(c_838,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_409,c_835])).

tff(c_841,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_838])).

tff(c_843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_36,c_841])).

tff(c_844,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_903,plain,(
    ! [A_138,B_139] :
      ( r2_hidden('#skF_2'(A_138,B_139),B_139)
      | v2_tex_2(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(u1_struct_0(A_138)))
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_907,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_903])).

tff(c_914,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4')
    | v2_tex_2('#skF_4','#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_907])).

tff(c_915,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_36,c_914])).

tff(c_919,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_915,c_65])).

tff(c_923,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_844,c_919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.49  
% 3.24/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.50  %$ v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.24/1.50  
% 3.24/1.50  %Foreground sorts:
% 3.24/1.50  
% 3.24/1.50  
% 3.24/1.50  %Background operators:
% 3.24/1.50  
% 3.24/1.50  
% 3.24/1.50  %Foreground operators:
% 3.24/1.50  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.24/1.50  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.24/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.50  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.24/1.50  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.24/1.50  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.24/1.50  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.24/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.50  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.24/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.50  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.24/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.24/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.24/1.50  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.24/1.50  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.24/1.50  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.24/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.24/1.50  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.24/1.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.50  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.24/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.50  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 3.24/1.50  
% 3.47/1.51  tff(f_149, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 3.47/1.51  tff(f_88, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 3.47/1.51  tff(f_134, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tex_2)).
% 3.47/1.51  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.47/1.51  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.47/1.51  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.47/1.51  tff(f_67, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 3.47/1.51  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.47/1.51  tff(f_108, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 3.47/1.51  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.47/1.51  tff(c_36, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.47/1.51  tff(c_40, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.47/1.51  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.47/1.51  tff(c_95, plain, (![A_63, B_64]: (v1_pre_topc('#skF_1'(A_63, B_64)) | ~m1_subset_1(B_64, k1_zfmisc_1(u1_struct_0(A_63))) | v1_xboole_0(B_64) | ~l1_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.47/1.51  tff(c_101, plain, (v1_pre_topc('#skF_1'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_95])).
% 3.47/1.51  tff(c_109, plain, (v1_pre_topc('#skF_1'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_101])).
% 3.47/1.51  tff(c_110, plain, (v1_pre_topc('#skF_1'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_109])).
% 3.47/1.51  tff(c_112, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_110])).
% 3.47/1.51  tff(c_44, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.47/1.51  tff(c_283, plain, (![A_81, B_82]: (r2_hidden('#skF_2'(A_81, B_82), B_82) | v2_tex_2(B_82, A_81) | ~m1_subset_1(B_82, k1_zfmisc_1(u1_struct_0(A_81))) | ~l1_pre_topc(A_81) | ~v2_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.47/1.51  tff(c_291, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_283])).
% 3.47/1.51  tff(c_298, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_291])).
% 3.47/1.51  tff(c_299, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_36, c_298])).
% 3.47/1.51  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.47/1.51  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.47/1.51  tff(c_47, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.47/1.51  tff(c_59, plain, (![C_44, B_45, A_46]: (~v1_xboole_0(C_44) | ~m1_subset_1(B_45, k1_zfmisc_1(C_44)) | ~r2_hidden(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.47/1.51  tff(c_65, plain, (![A_2, A_46]: (~v1_xboole_0(A_2) | ~r2_hidden(A_46, A_2))), inference(resolution, [status(thm)], [c_47, c_59])).
% 3.47/1.51  tff(c_303, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_299, c_65])).
% 3.47/1.51  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_303])).
% 3.47/1.51  tff(c_309, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_110])).
% 3.47/1.51  tff(c_389, plain, (![A_87, B_88]: (m1_pre_topc('#skF_1'(A_87, B_88), A_87) | ~m1_subset_1(B_88, k1_zfmisc_1(u1_struct_0(A_87))) | v1_xboole_0(B_88) | ~l1_pre_topc(A_87) | v2_struct_0(A_87))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.47/1.51  tff(c_397, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_389])).
% 3.47/1.51  tff(c_408, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_397])).
% 3.47/1.51  tff(c_409, plain, (m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_46, c_309, c_408])).
% 3.47/1.51  tff(c_76, plain, (![A_60, B_61]: (~v2_struct_0('#skF_1'(A_60, B_61)) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | v1_xboole_0(B_61) | ~l1_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.47/1.51  tff(c_82, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_76])).
% 3.47/1.51  tff(c_90, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_82])).
% 3.47/1.51  tff(c_91, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_90])).
% 3.47/1.51  tff(c_93, plain, (~v2_struct_0('#skF_1'('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_91])).
% 3.47/1.51  tff(c_42, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.47/1.51  tff(c_12, plain, (![B_12, A_10]: (v1_tdlat_3(B_12) | ~m1_pre_topc(B_12, A_10) | ~l1_pre_topc(A_10) | ~v1_tdlat_3(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.47/1.51  tff(c_413, plain, (v1_tdlat_3('#skF_1'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_409, c_12])).
% 3.47/1.51  tff(c_416, plain, (v1_tdlat_3('#skF_1'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_40, c_413])).
% 3.47/1.51  tff(c_417, plain, (v1_tdlat_3('#skF_1'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_416])).
% 3.47/1.51  tff(c_310, plain, (![A_83, B_84]: (u1_struct_0('#skF_1'(A_83, B_84))=B_84 | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | v1_xboole_0(B_84) | ~l1_pre_topc(A_83) | v2_struct_0(A_83))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.47/1.51  tff(c_316, plain, (u1_struct_0('#skF_1'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_310])).
% 3.47/1.51  tff(c_324, plain, (u1_struct_0('#skF_1'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_316])).
% 3.47/1.51  tff(c_325, plain, (u1_struct_0('#skF_1'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_309, c_324])).
% 3.47/1.51  tff(c_8, plain, (![B_8, A_6]: (m1_subset_1(u1_struct_0(B_8), k1_zfmisc_1(u1_struct_0(A_6))) | ~m1_pre_topc(B_8, A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.47/1.51  tff(c_777, plain, (![B_119, A_120]: (v2_tex_2(u1_struct_0(B_119), A_120) | ~v1_tdlat_3(B_119) | ~m1_subset_1(u1_struct_0(B_119), k1_zfmisc_1(u1_struct_0(A_120))) | ~m1_pre_topc(B_119, A_120) | v2_struct_0(B_119) | ~l1_pre_topc(A_120) | v2_struct_0(A_120))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.47/1.51  tff(c_822, plain, (![B_122, A_123]: (v2_tex_2(u1_struct_0(B_122), A_123) | ~v1_tdlat_3(B_122) | v2_struct_0(B_122) | v2_struct_0(A_123) | ~m1_pre_topc(B_122, A_123) | ~l1_pre_topc(A_123))), inference(resolution, [status(thm)], [c_8, c_777])).
% 3.47/1.51  tff(c_831, plain, (![A_123]: (v2_tex_2('#skF_4', A_123) | ~v1_tdlat_3('#skF_1'('#skF_3', '#skF_4')) | v2_struct_0('#skF_1'('#skF_3', '#skF_4')) | v2_struct_0(A_123) | ~m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_123) | ~l1_pre_topc(A_123))), inference(superposition, [status(thm), theory('equality')], [c_325, c_822])).
% 3.47/1.51  tff(c_833, plain, (![A_123]: (v2_tex_2('#skF_4', A_123) | v2_struct_0('#skF_1'('#skF_3', '#skF_4')) | v2_struct_0(A_123) | ~m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_123) | ~l1_pre_topc(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_417, c_831])).
% 3.47/1.51  tff(c_835, plain, (![A_124]: (v2_tex_2('#skF_4', A_124) | v2_struct_0(A_124) | ~m1_pre_topc('#skF_1'('#skF_3', '#skF_4'), A_124) | ~l1_pre_topc(A_124))), inference(negUnitSimplification, [status(thm)], [c_93, c_833])).
% 3.47/1.51  tff(c_838, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_409, c_835])).
% 3.47/1.51  tff(c_841, plain, (v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_838])).
% 3.47/1.51  tff(c_843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_36, c_841])).
% 3.47/1.51  tff(c_844, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_91])).
% 3.47/1.51  tff(c_903, plain, (![A_138, B_139]: (r2_hidden('#skF_2'(A_138, B_139), B_139) | v2_tex_2(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(u1_struct_0(A_138))) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.47/1.51  tff(c_907, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_903])).
% 3.47/1.51  tff(c_914, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4') | v2_tex_2('#skF_4', '#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_907])).
% 3.47/1.51  tff(c_915, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_46, c_36, c_914])).
% 3.47/1.51  tff(c_919, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_915, c_65])).
% 3.47/1.51  tff(c_923, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_844, c_919])).
% 3.47/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.51  
% 3.47/1.51  Inference rules
% 3.47/1.51  ----------------------
% 3.47/1.51  #Ref     : 0
% 3.47/1.51  #Sup     : 210
% 3.47/1.51  #Fact    : 0
% 3.47/1.51  #Define  : 0
% 3.47/1.51  #Split   : 5
% 3.47/1.51  #Chain   : 0
% 3.47/1.51  #Close   : 0
% 3.47/1.51  
% 3.47/1.51  Ordering : KBO
% 3.47/1.51  
% 3.47/1.51  Simplification rules
% 3.47/1.51  ----------------------
% 3.47/1.51  #Subsume      : 31
% 3.47/1.51  #Demod        : 68
% 3.47/1.51  #Tautology    : 29
% 3.47/1.51  #SimpNegUnit  : 46
% 3.47/1.51  #BackRed      : 0
% 3.47/1.51  
% 3.47/1.51  #Partial instantiations: 0
% 3.47/1.51  #Strategies tried      : 1
% 3.47/1.51  
% 3.47/1.51  Timing (in seconds)
% 3.47/1.51  ----------------------
% 3.47/1.52  Preprocessing        : 0.31
% 3.47/1.52  Parsing              : 0.17
% 3.47/1.52  CNF conversion       : 0.02
% 3.47/1.52  Main loop            : 0.44
% 3.47/1.52  Inferencing          : 0.16
% 3.47/1.52  Reduction            : 0.12
% 3.47/1.52  Demodulation         : 0.08
% 3.47/1.52  BG Simplification    : 0.02
% 3.47/1.52  Subsumption          : 0.10
% 3.47/1.52  Abstraction          : 0.02
% 3.47/1.52  MUC search           : 0.00
% 3.47/1.52  Cooper               : 0.00
% 3.47/1.52  Total                : 0.79
% 3.47/1.52  Index Insertion      : 0.00
% 3.47/1.52  Index Deletion       : 0.00
% 3.47/1.52  Index Matching       : 0.00
% 3.47/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
