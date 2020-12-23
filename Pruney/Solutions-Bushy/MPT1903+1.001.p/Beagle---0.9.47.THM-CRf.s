%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1903+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:40 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 910 expanded)
%              Number of leaves         :   48 ( 339 expanded)
%              Depth                    :   20
%              Number of atoms          :  279 (2368 expanded)
%              Number of equality atoms :   41 ( 490 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v4_pre_topc > v1_partfun1 > m1_subset_1 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k8_relset_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k6_relat_1 > k6_partfun1 > k2_tex_1 > k1_zfmisc_1 > k1_tex_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_tex_1,type,(
    k2_tex_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(k1_tex_1,type,(
    k1_tex_1: $i > $i )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

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

tff(f_161,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( ! [B] :
              ( ( ~ v2_struct_0(B)
                & v2_pre_topc(B)
                & l1_pre_topc(B) )
             => ! [C] :
                  ( ( v1_funct_1(C)
                    & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                    & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                 => v5_pre_topc(C,B,A) ) )
         => v2_tdlat_3(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_tex_2)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v2_tdlat_3(A)
      <=> ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ~ ( v4_pre_topc(B,A)
                & B != k1_xboole_0
                & B != u1_struct_0(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tdlat_3)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_112,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_95,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_91,axiom,(
    ! [A] :
      ( v1_pre_topc(k2_tex_1(A))
      & v2_pre_topc(k2_tex_1(A))
      & v2_tdlat_3(k2_tex_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_1)).

tff(f_65,axiom,(
    ! [A] : l1_pre_topc(k2_tex_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tex_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_30,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_63,axiom,(
    ! [A] : k2_tex_1(A) = g1_pre_topc(A,k1_tex_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_101,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ~ v2_struct_0(k2_tex_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_tex_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_116,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_relset_1(A,A,k6_partfun1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ( v5_pre_topc(C,A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                   => ( v4_pre_topc(D,B)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(A),u1_struct_0(B),C,D),A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_pre_topc)).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_109,plain,(
    ! [A_70] :
      ( '#skF_2'(A_70) != k1_xboole_0
      | v2_tdlat_3(A_70)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_60,plain,(
    ~ v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_112,plain,
    ( '#skF_2'('#skF_3') != k1_xboole_0
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_109,c_60])).

tff(c_115,plain,(
    '#skF_2'('#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_112])).

tff(c_205,plain,(
    ! [A_101] :
      ( u1_struct_0(A_101) != '#skF_2'(A_101)
      | v2_tdlat_3(A_101)
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_208,plain,
    ( u1_struct_0('#skF_3') != '#skF_2'('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_205,c_60])).

tff(c_211,plain,(
    u1_struct_0('#skF_3') != '#skF_2'('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_208])).

tff(c_58,plain,(
    ! [A_45] :
      ( m1_subset_1('#skF_2'(A_45),k1_zfmisc_1(u1_struct_0(A_45)))
      | v2_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_24,plain,(
    ! [A_30] :
      ( l1_struct_0(A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_46,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    ! [A_34] : v1_funct_1(k6_relat_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_69,plain,(
    ! [A_34] : v1_funct_1(k6_partfun1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_38])).

tff(c_20,plain,(
    ! [A_29] : v1_partfun1(k6_partfun1(A_29),A_29) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [A_29] : m1_subset_1(k6_partfun1(A_29),k1_zfmisc_1(k2_zfmisc_1(A_29,A_29))) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_289,plain,(
    ! [C_131,A_132,B_133] :
      ( v1_funct_2(C_131,A_132,B_133)
      | ~ v1_partfun1(C_131,A_132)
      | ~ v1_funct_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_292,plain,(
    ! [A_29] :
      ( v1_funct_2(k6_partfun1(A_29),A_29,A_29)
      | ~ v1_partfun1(k6_partfun1(A_29),A_29)
      | ~ v1_funct_1(k6_partfun1(A_29)) ) ),
    inference(resolution,[status(thm)],[c_22,c_289])).

tff(c_295,plain,(
    ! [A_29] : v1_funct_2(k6_partfun1(A_29),A_29,A_29) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_20,c_292])).

tff(c_32,plain,(
    ! [A_33] : v2_pre_topc(k2_tex_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_18,plain,(
    ! [A_28] : l1_pre_topc(k2_tex_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_31] :
      ( m1_subset_1(u1_pre_topc(A_31),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_31))))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [A_33] : v1_pre_topc(k2_tex_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [A_1] :
      ( g1_pre_topc(u1_struct_0(A_1),u1_pre_topc(A_1)) = A_1
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_16,plain,(
    ! [A_27] : g1_pre_topc(A_27,k1_tex_1(A_27)) = k2_tex_1(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_237,plain,(
    ! [C_107,A_108,D_109,B_110] :
      ( C_107 = A_108
      | g1_pre_topc(C_107,D_109) != g1_pre_topc(A_108,B_110)
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_246,plain,(
    ! [A_112,A_111,B_113] :
      ( A_112 = A_111
      | k2_tex_1(A_111) != g1_pre_topc(A_112,B_113)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(A_112))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_237])).

tff(c_248,plain,(
    ! [A_1,A_111] :
      ( u1_struct_0(A_1) = A_111
      | k2_tex_1(A_111) != A_1
      | ~ m1_subset_1(u1_pre_topc(A_1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_1))))
      | ~ v1_pre_topc(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_246])).

tff(c_377,plain,(
    ! [A_111] :
      ( u1_struct_0(k2_tex_1(A_111)) = A_111
      | ~ m1_subset_1(u1_pre_topc(k2_tex_1(A_111)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k2_tex_1(A_111)))))
      | ~ v1_pre_topc(k2_tex_1(A_111))
      | ~ l1_pre_topc(k2_tex_1(A_111)) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_248])).

tff(c_381,plain,(
    ! [A_160] :
      ( u1_struct_0(k2_tex_1(A_160)) = A_160
      | ~ m1_subset_1(u1_pre_topc(k2_tex_1(A_160)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k2_tex_1(A_160))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30,c_377])).

tff(c_384,plain,(
    ! [A_160] :
      ( u1_struct_0(k2_tex_1(A_160)) = A_160
      | ~ l1_pre_topc(k2_tex_1(A_160)) ) ),
    inference(resolution,[status(thm)],[c_26,c_381])).

tff(c_387,plain,(
    ! [A_160] : u1_struct_0(k2_tex_1(A_160)) = A_160 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_384])).

tff(c_390,plain,(
    ! [A_161] : u1_struct_0(k2_tex_1(A_161)) = A_161 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_384])).

tff(c_62,plain,(
    ! [C_54,B_52] :
      ( v5_pre_topc(C_54,B_52,'#skF_3')
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_52),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_54,u1_struct_0(B_52),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_54)
      | ~ l1_pre_topc(B_52)
      | ~ v2_pre_topc(B_52)
      | v2_struct_0(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_431,plain,(
    ! [C_54,A_161] :
      ( v5_pre_topc(C_54,k2_tex_1(A_161),'#skF_3')
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_161,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_54,u1_struct_0(k2_tex_1(A_161)),u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_54)
      | ~ l1_pre_topc(k2_tex_1(A_161))
      | ~ v2_pre_topc(k2_tex_1(A_161))
      | v2_struct_0(k2_tex_1(A_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_62])).

tff(c_527,plain,(
    ! [C_170,A_171] :
      ( v5_pre_topc(C_170,k2_tex_1(A_171),'#skF_3')
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_171,u1_struct_0('#skF_3'))))
      | ~ v1_funct_2(C_170,A_171,u1_struct_0('#skF_3'))
      | ~ v1_funct_1(C_170)
      | v2_struct_0(k2_tex_1(A_171)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18,c_387,c_431])).

tff(c_531,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),k2_tex_1(u1_struct_0('#skF_3')),'#skF_3')
    | ~ v1_funct_2(k6_partfun1(u1_struct_0('#skF_3')),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1(k6_partfun1(u1_struct_0('#skF_3')))
    | v2_struct_0(k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_22,c_527])).

tff(c_534,plain,
    ( v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),k2_tex_1(u1_struct_0('#skF_3')),'#skF_3')
    | v2_struct_0(k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_295,c_531])).

tff(c_535,plain,(
    v2_struct_0(k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_534])).

tff(c_40,plain,(
    ! [A_35] :
      ( ~ v2_struct_0(k2_tex_1(A_35))
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_539,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_535,c_40])).

tff(c_28,plain,(
    ! [A_32] :
      ( ~ v1_xboole_0(u1_struct_0(A_32))
      | ~ l1_struct_0(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_542,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_539,c_28])).

tff(c_545,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_542])).

tff(c_548,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_545])).

tff(c_552,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_548])).

tff(c_553,plain,(
    v5_pre_topc(k6_partfun1(u1_struct_0('#skF_3')),k2_tex_1(u1_struct_0('#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_534])).

tff(c_229,plain,(
    ! [A_106] :
      ( m1_subset_1('#skF_2'(A_106),k1_zfmisc_1(u1_struct_0(A_106)))
      | v2_tdlat_3(A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_48,plain,(
    ! [A_43,B_44] :
      ( k8_relset_1(A_43,A_43,k6_partfun1(A_43),B_44) = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_232,plain,(
    ! [A_106] :
      ( k8_relset_1(u1_struct_0(A_106),u1_struct_0(A_106),k6_partfun1(u1_struct_0(A_106)),'#skF_2'(A_106)) = '#skF_2'(A_106)
      | v2_tdlat_3(A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_229,c_48])).

tff(c_559,plain,(
    ! [A_172,B_173,C_174,D_175] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(A_172),u1_struct_0(B_173),C_174,D_175),A_172)
      | ~ v4_pre_topc(D_175,B_173)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(u1_struct_0(B_173)))
      | ~ v5_pre_topc(C_174,A_172,B_173)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_172),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0(A_172),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_173)
      | ~ l1_pre_topc(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_561,plain,(
    ! [A_160,B_173,C_174,D_175] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(k2_tex_1(A_160)),u1_struct_0(B_173),C_174,D_175),k2_tex_1(A_160))
      | ~ v4_pre_topc(D_175,B_173)
      | ~ m1_subset_1(D_175,k1_zfmisc_1(u1_struct_0(B_173)))
      | ~ v5_pre_topc(C_174,k2_tex_1(A_160),B_173)
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_160,u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0(k2_tex_1(A_160)),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_173)
      | ~ l1_pre_topc(k2_tex_1(A_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_559])).

tff(c_3991,plain,(
    ! [A_433,B_434,C_435,D_436] :
      ( v4_pre_topc(k8_relset_1(A_433,u1_struct_0(B_434),C_435,D_436),k2_tex_1(A_433))
      | ~ v4_pre_topc(D_436,B_434)
      | ~ m1_subset_1(D_436,k1_zfmisc_1(u1_struct_0(B_434)))
      | ~ v5_pre_topc(C_435,k2_tex_1(A_433),B_434)
      | ~ m1_subset_1(C_435,k1_zfmisc_1(k2_zfmisc_1(A_433,u1_struct_0(B_434))))
      | ~ v1_funct_2(C_435,A_433,u1_struct_0(B_434))
      | ~ v1_funct_1(C_435)
      | ~ l1_pre_topc(B_434) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_387,c_387,c_561])).

tff(c_4018,plain,(
    ! [A_106] :
      ( v4_pre_topc('#skF_2'(A_106),k2_tex_1(u1_struct_0(A_106)))
      | ~ v4_pre_topc('#skF_2'(A_106),A_106)
      | ~ m1_subset_1('#skF_2'(A_106),k1_zfmisc_1(u1_struct_0(A_106)))
      | ~ v5_pre_topc(k6_partfun1(u1_struct_0(A_106)),k2_tex_1(u1_struct_0(A_106)),A_106)
      | ~ m1_subset_1(k6_partfun1(u1_struct_0(A_106)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_106),u1_struct_0(A_106))))
      | ~ v1_funct_2(k6_partfun1(u1_struct_0(A_106)),u1_struct_0(A_106),u1_struct_0(A_106))
      | ~ v1_funct_1(k6_partfun1(u1_struct_0(A_106)))
      | ~ l1_pre_topc(A_106)
      | v2_tdlat_3(A_106)
      | ~ l1_pre_topc(A_106)
      | ~ v2_pre_topc(A_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_3991])).

tff(c_4329,plain,(
    ! [A_451] :
      ( v4_pre_topc('#skF_2'(A_451),k2_tex_1(u1_struct_0(A_451)))
      | ~ v4_pre_topc('#skF_2'(A_451),A_451)
      | ~ m1_subset_1('#skF_2'(A_451),k1_zfmisc_1(u1_struct_0(A_451)))
      | ~ v5_pre_topc(k6_partfun1(u1_struct_0(A_451)),k2_tex_1(u1_struct_0(A_451)),A_451)
      | v2_tdlat_3(A_451)
      | ~ l1_pre_topc(A_451)
      | ~ v2_pre_topc(A_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_295,c_22,c_4018])).

tff(c_4347,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_553,c_4329])).

tff(c_4356,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3')))
    | v2_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4347])).

tff(c_4357,plain,
    ( v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3')))
    | ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4356])).

tff(c_4362,plain,(
    ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_4357])).

tff(c_4365,plain,
    ( v2_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_4362])).

tff(c_4368,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4365])).

tff(c_4370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4368])).

tff(c_4372,plain,(
    m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4357])).

tff(c_56,plain,(
    ! [A_45] :
      ( v4_pre_topc('#skF_2'(A_45),A_45)
      | v2_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4371,plain,
    ( ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3')
    | v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4357])).

tff(c_4383,plain,(
    ~ v4_pre_topc('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4371])).

tff(c_4386,plain,
    ( v2_tdlat_3('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_4383])).

tff(c_4389,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_4386])).

tff(c_4391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_4389])).

tff(c_4392,plain,(
    v4_pre_topc('#skF_2'('#skF_3'),k2_tex_1(u1_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_4371])).

tff(c_34,plain,(
    ! [A_33] : v2_tdlat_3(k2_tex_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    ! [A_45,B_48] :
      ( u1_struct_0(A_45) = B_48
      | k1_xboole_0 = B_48
      | ~ v4_pre_topc(B_48,A_45)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_45)))
      | ~ v2_tdlat_3(A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_416,plain,(
    ! [A_161,B_48] :
      ( u1_struct_0(k2_tex_1(A_161)) = B_48
      | k1_xboole_0 = B_48
      | ~ v4_pre_topc(B_48,k2_tex_1(A_161))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_161))
      | ~ v2_tdlat_3(k2_tex_1(A_161))
      | ~ l1_pre_topc(k2_tex_1(A_161))
      | ~ v2_pre_topc(k2_tex_1(A_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_390,c_50])).

tff(c_453,plain,(
    ! [B_48,A_161] :
      ( B_48 = A_161
      | k1_xboole_0 = B_48
      | ~ v4_pre_topc(B_48,k2_tex_1(A_161))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_161)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_18,c_34,c_387,c_416])).

tff(c_4396,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0
    | ~ m1_subset_1('#skF_2'('#skF_3'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_4392,c_453])).

tff(c_4399,plain,
    ( u1_struct_0('#skF_3') = '#skF_2'('#skF_3')
    | '#skF_2'('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4372,c_4396])).

tff(c_4401,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_211,c_4399])).

%------------------------------------------------------------------------------
