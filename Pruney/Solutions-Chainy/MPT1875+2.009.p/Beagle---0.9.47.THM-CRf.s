%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:47 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 304 expanded)
%              Number of leaves         :   39 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  213 ( 752 expanded)
%              Number of equality atoms :   12 (  74 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_pre_topc,type,(
    k1_pre_topc: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => u1_struct_0(k1_pre_topc(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => ( v1_pre_topc(k1_pre_topc(A,B))
        & m1_pre_topc(k1_pre_topc(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(f_99,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_119,axiom,(
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

tff(f_36,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_145,axiom,(
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

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_40,plain,(
    ~ v2_tex_2('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_101,plain,(
    ! [A_64,B_65] :
      ( u1_struct_0(k1_pre_topc(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_107,plain,
    ( u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3'
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_101])).

tff(c_115,plain,(
    u1_struct_0(k1_pre_topc('#skF_2','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_107])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_51,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_75,plain,(
    ! [A_57,B_58] :
      ( v1_pre_topc(k1_pre_topc(A_57,B_58))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    ! [A_57] :
      ( v1_pre_topc(k1_pre_topc(A_57,u1_struct_0(A_57)))
      | ~ l1_pre_topc(A_57) ) ),
    inference(resolution,[status(thm)],[c_51,c_75])).

tff(c_132,plain,
    ( v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_86])).

tff(c_182,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_132])).

tff(c_183,plain,(
    ! [A_67,B_68] :
      ( m1_pre_topc(k1_pre_topc(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_191,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_183])).

tff(c_198,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_191])).

tff(c_14,plain,(
    ! [B_11,A_9] :
      ( l1_pre_topc(B_11)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_202,plain,
    ( l1_pre_topc(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_198,c_14])).

tff(c_205,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_202])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_205])).

tff(c_209,plain,(
    l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_132])).

tff(c_1251,plain,(
    ! [A_134,B_135] :
      ( m1_pre_topc(k1_pre_topc(A_134,B_135),A_134)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1284,plain,(
    ! [A_136] :
      ( m1_pre_topc(k1_pre_topc(A_136,u1_struct_0(A_136)),A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_51,c_1251])).

tff(c_1296,plain,
    ( m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3'),k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1284])).

tff(c_1299,plain,(
    m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3'),k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_1296])).

tff(c_142,plain,(
    ! [A_66] :
      ( u1_struct_0(k1_pre_topc(A_66,u1_struct_0(A_66))) = u1_struct_0(A_66)
      | ~ l1_pre_topc(A_66) ) ),
    inference(resolution,[status(thm)],[c_51,c_101])).

tff(c_178,plain,
    ( u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3')) = u1_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_142])).

tff(c_181,plain,
    ( u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3')) = '#skF_3'
    | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_178])).

tff(c_1220,plain,(
    u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_181])).

tff(c_12,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_243,plain,(
    ! [A_70,B_71] :
      ( m1_pre_topc(k1_pre_topc(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | ~ l1_pre_topc(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_253,plain,
    ( m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_243])).

tff(c_262,plain,(
    m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_253])).

tff(c_16,plain,(
    ! [A_12] :
      ( v1_xboole_0(u1_struct_0(A_12))
      | ~ l1_struct_0(A_12)
      | ~ v2_struct_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_138,plain,
    ( v1_xboole_0('#skF_3')
    | ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_16])).

tff(c_210,plain,(
    ~ v2_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_46,plain,(
    v1_tdlat_3('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_24,plain,(
    ! [B_22,A_20] :
      ( v1_tdlat_3(B_22)
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v1_tdlat_3(A_20)
      | ~ v2_pre_topc(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_267,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v1_tdlat_3('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_262,c_24])).

tff(c_276,plain,
    ( v1_tdlat_3(k1_pre_topc('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_267])).

tff(c_277,plain,(
    v1_tdlat_3(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_276])).

tff(c_20,plain,(
    ! [B_18,A_16] :
      ( m1_subset_1(u1_struct_0(B_18),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1044,plain,(
    ! [B_124,A_125] :
      ( v2_tex_2(u1_struct_0(B_124),A_125)
      | ~ v1_tdlat_3(B_124)
      | ~ m1_subset_1(u1_struct_0(B_124),k1_zfmisc_1(u1_struct_0(A_125)))
      | ~ m1_pre_topc(B_124,A_125)
      | v2_struct_0(B_124)
      | ~ l1_pre_topc(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1147,plain,(
    ! [B_128,A_129] :
      ( v2_tex_2(u1_struct_0(B_128),A_129)
      | ~ v1_tdlat_3(B_128)
      | v2_struct_0(B_128)
      | v2_struct_0(A_129)
      | ~ m1_pre_topc(B_128,A_129)
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_20,c_1044])).

tff(c_1169,plain,(
    ! [A_129] :
      ( v2_tex_2('#skF_3',A_129)
      | ~ v1_tdlat_3(k1_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0(A_129)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_129)
      | ~ l1_pre_topc(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1147])).

tff(c_1176,plain,(
    ! [A_129] :
      ( v2_tex_2('#skF_3',A_129)
      | v2_struct_0(k1_pre_topc('#skF_2','#skF_3'))
      | v2_struct_0(A_129)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_129)
      | ~ l1_pre_topc(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_1169])).

tff(c_1178,plain,(
    ! [A_130] :
      ( v2_tex_2('#skF_3',A_130)
      | v2_struct_0(A_130)
      | ~ m1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_1176])).

tff(c_1181,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_262,c_1178])).

tff(c_1184,plain,
    ( v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1181])).

tff(c_1186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_1184])).

tff(c_1187,plain,
    ( ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1189,plain,(
    ~ l1_struct_0(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1187])).

tff(c_1211,plain,(
    ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_1189])).

tff(c_1215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_1211])).

tff(c_1216,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_92,plain,(
    ! [B_60,A_61] :
      ( m1_subset_1(u1_struct_0(B_60),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_pre_topc(B_60,A_61)
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1475,plain,(
    ! [A_148,A_149,B_150] :
      ( ~ v1_xboole_0(u1_struct_0(A_148))
      | ~ r2_hidden(A_149,u1_struct_0(B_150))
      | ~ m1_pre_topc(B_150,A_148)
      | ~ l1_pre_topc(A_148) ) ),
    inference(resolution,[status(thm)],[c_92,c_6])).

tff(c_1483,plain,(
    ! [A_149,B_150] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_149,u1_struct_0(B_150))
      | ~ m1_pre_topc(B_150,k1_pre_topc('#skF_2','#skF_3'))
      | ~ l1_pre_topc(k1_pre_topc('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_1475])).

tff(c_1492,plain,(
    ! [A_153,B_154] :
      ( ~ r2_hidden(A_153,u1_struct_0(B_154))
      | ~ m1_pre_topc(B_154,k1_pre_topc('#skF_2','#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_1216,c_1483])).

tff(c_1498,plain,(
    ! [A_153] :
      ( ~ r2_hidden(A_153,'#skF_3')
      | ~ m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2','#skF_3'),'#skF_3'),k1_pre_topc('#skF_2','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1220,c_1492])).

tff(c_1506,plain,(
    ! [A_153] : ~ r2_hidden(A_153,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_1498])).

tff(c_1656,plain,(
    ! [A_173,B_174] :
      ( r2_hidden('#skF_1'(A_173,B_174),B_174)
      | v2_tex_2(B_174,A_173)
      | ~ m1_subset_1(B_174,k1_zfmisc_1(u1_struct_0(A_173)))
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1672,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1656])).

tff(c_1689,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3'),'#skF_3')
    | v2_tex_2('#skF_3','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_1672])).

tff(c_1691,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_1506,c_1689])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:46:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.65  
% 3.64/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.65  %$ v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k9_subset_1 > k6_domain_1 > k1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.99/1.65  
% 3.99/1.65  %Foreground sorts:
% 3.99/1.65  
% 3.99/1.65  
% 3.99/1.65  %Background operators:
% 3.99/1.65  
% 3.99/1.65  
% 3.99/1.65  %Foreground operators:
% 3.99/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.99/1.65  tff(k1_pre_topc, type, k1_pre_topc: ($i * $i) > $i).
% 3.99/1.65  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.99/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.99/1.65  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.99/1.65  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.99/1.65  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.99/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.99/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.99/1.65  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.99/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.99/1.65  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.99/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.65  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.99/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.99/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.99/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.99/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.99/1.65  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.99/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.99/1.65  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.99/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.99/1.65  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 3.99/1.65  
% 3.99/1.67  tff(f_160, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 3.99/1.67  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (u1_struct_0(k1_pre_topc(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 3.99/1.67  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.99/1.67  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.99/1.67  tff(f_44, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v1_pre_topc(k1_pre_topc(A, B)) & m1_pre_topc(k1_pre_topc(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 3.99/1.67  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.99/1.67  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.99/1.67  tff(f_61, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 3.99/1.67  tff(f_99, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 3.99/1.67  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.99/1.67  tff(f_119, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 3.99/1.67  tff(f_36, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.99/1.67  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tex_2)).
% 3.99/1.67  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.99/1.67  tff(c_40, plain, (~v2_tex_2('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.99/1.67  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.99/1.67  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.99/1.67  tff(c_101, plain, (![A_64, B_65]: (u1_struct_0(k1_pre_topc(A_64, B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.99/1.67  tff(c_107, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3' | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_101])).
% 3.99/1.67  tff(c_115, plain, (u1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_107])).
% 3.99/1.67  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.99/1.67  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.99/1.67  tff(c_51, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.99/1.67  tff(c_75, plain, (![A_57, B_58]: (v1_pre_topc(k1_pre_topc(A_57, B_58)) | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.99/1.67  tff(c_86, plain, (![A_57]: (v1_pre_topc(k1_pre_topc(A_57, u1_struct_0(A_57))) | ~l1_pre_topc(A_57))), inference(resolution, [status(thm)], [c_51, c_75])).
% 3.99/1.67  tff(c_132, plain, (v1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_86])).
% 3.99/1.67  tff(c_182, plain, (~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_132])).
% 3.99/1.67  tff(c_183, plain, (![A_67, B_68]: (m1_pre_topc(k1_pre_topc(A_67, B_68), A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.99/1.67  tff(c_191, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_183])).
% 3.99/1.67  tff(c_198, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_191])).
% 3.99/1.67  tff(c_14, plain, (![B_11, A_9]: (l1_pre_topc(B_11) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.99/1.67  tff(c_202, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_198, c_14])).
% 3.99/1.67  tff(c_205, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_202])).
% 3.99/1.67  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_205])).
% 3.99/1.67  tff(c_209, plain, (l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_132])).
% 3.99/1.67  tff(c_1251, plain, (![A_134, B_135]: (m1_pre_topc(k1_pre_topc(A_134, B_135), A_134) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.99/1.67  tff(c_1284, plain, (![A_136]: (m1_pre_topc(k1_pre_topc(A_136, u1_struct_0(A_136)), A_136) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_51, c_1251])).
% 3.99/1.67  tff(c_1296, plain, (m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3'), k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_1284])).
% 3.99/1.67  tff(c_1299, plain, (m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3'), k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_1296])).
% 3.99/1.67  tff(c_142, plain, (![A_66]: (u1_struct_0(k1_pre_topc(A_66, u1_struct_0(A_66)))=u1_struct_0(A_66) | ~l1_pre_topc(A_66))), inference(resolution, [status(thm)], [c_51, c_101])).
% 3.99/1.67  tff(c_178, plain, (u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3'))=u1_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_142])).
% 3.99/1.67  tff(c_181, plain, (u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3'))='#skF_3' | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_115, c_178])).
% 3.99/1.67  tff(c_1220, plain, (u1_struct_0(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_181])).
% 3.99/1.67  tff(c_12, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.99/1.67  tff(c_243, plain, (![A_70, B_71]: (m1_pre_topc(k1_pre_topc(A_70, B_71), A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | ~l1_pre_topc(A_70))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.99/1.67  tff(c_253, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_42, c_243])).
% 3.99/1.67  tff(c_262, plain, (m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_253])).
% 3.99/1.67  tff(c_16, plain, (![A_12]: (v1_xboole_0(u1_struct_0(A_12)) | ~l1_struct_0(A_12) | ~v2_struct_0(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.99/1.67  tff(c_138, plain, (v1_xboole_0('#skF_3') | ~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | ~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_16])).
% 3.99/1.67  tff(c_210, plain, (~v2_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_138])).
% 3.99/1.67  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.99/1.67  tff(c_46, plain, (v1_tdlat_3('#skF_2')), inference(cnfTransformation, [status(thm)], [f_160])).
% 3.99/1.67  tff(c_24, plain, (![B_22, A_20]: (v1_tdlat_3(B_22) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20) | ~v1_tdlat_3(A_20) | ~v2_pre_topc(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.99/1.67  tff(c_267, plain, (v1_tdlat_3(k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v1_tdlat_3('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_262, c_24])).
% 3.99/1.67  tff(c_276, plain, (v1_tdlat_3(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_267])).
% 3.99/1.67  tff(c_277, plain, (v1_tdlat_3(k1_pre_topc('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_276])).
% 3.99/1.67  tff(c_20, plain, (![B_18, A_16]: (m1_subset_1(u1_struct_0(B_18), k1_zfmisc_1(u1_struct_0(A_16))) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.99/1.67  tff(c_1044, plain, (![B_124, A_125]: (v2_tex_2(u1_struct_0(B_124), A_125) | ~v1_tdlat_3(B_124) | ~m1_subset_1(u1_struct_0(B_124), k1_zfmisc_1(u1_struct_0(A_125))) | ~m1_pre_topc(B_124, A_125) | v2_struct_0(B_124) | ~l1_pre_topc(A_125) | v2_struct_0(A_125))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.99/1.67  tff(c_1147, plain, (![B_128, A_129]: (v2_tex_2(u1_struct_0(B_128), A_129) | ~v1_tdlat_3(B_128) | v2_struct_0(B_128) | v2_struct_0(A_129) | ~m1_pre_topc(B_128, A_129) | ~l1_pre_topc(A_129))), inference(resolution, [status(thm)], [c_20, c_1044])).
% 3.99/1.67  tff(c_1169, plain, (![A_129]: (v2_tex_2('#skF_3', A_129) | ~v1_tdlat_3(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(A_129) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_129) | ~l1_pre_topc(A_129))), inference(superposition, [status(thm), theory('equality')], [c_115, c_1147])).
% 3.99/1.67  tff(c_1176, plain, (![A_129]: (v2_tex_2('#skF_3', A_129) | v2_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v2_struct_0(A_129) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_129) | ~l1_pre_topc(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_277, c_1169])).
% 3.99/1.67  tff(c_1178, plain, (![A_130]: (v2_tex_2('#skF_3', A_130) | v2_struct_0(A_130) | ~m1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), A_130) | ~l1_pre_topc(A_130))), inference(negUnitSimplification, [status(thm)], [c_210, c_1176])).
% 3.99/1.67  tff(c_1181, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_262, c_1178])).
% 3.99/1.67  tff(c_1184, plain, (v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1181])).
% 3.99/1.67  tff(c_1186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_1184])).
% 3.99/1.67  tff(c_1187, plain, (~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3')) | v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_138])).
% 3.99/1.67  tff(c_1189, plain, (~l1_struct_0(k1_pre_topc('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1187])).
% 3.99/1.67  tff(c_1211, plain, (~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_1189])).
% 3.99/1.67  tff(c_1215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_209, c_1211])).
% 3.99/1.67  tff(c_1216, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_1187])).
% 3.99/1.67  tff(c_92, plain, (![B_60, A_61]: (m1_subset_1(u1_struct_0(B_60), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_pre_topc(B_60, A_61) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.99/1.67  tff(c_6, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.99/1.67  tff(c_1475, plain, (![A_148, A_149, B_150]: (~v1_xboole_0(u1_struct_0(A_148)) | ~r2_hidden(A_149, u1_struct_0(B_150)) | ~m1_pre_topc(B_150, A_148) | ~l1_pre_topc(A_148))), inference(resolution, [status(thm)], [c_92, c_6])).
% 3.99/1.67  tff(c_1483, plain, (![A_149, B_150]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_149, u1_struct_0(B_150)) | ~m1_pre_topc(B_150, k1_pre_topc('#skF_2', '#skF_3')) | ~l1_pre_topc(k1_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_115, c_1475])).
% 3.99/1.67  tff(c_1492, plain, (![A_153, B_154]: (~r2_hidden(A_153, u1_struct_0(B_154)) | ~m1_pre_topc(B_154, k1_pre_topc('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_209, c_1216, c_1483])).
% 3.99/1.67  tff(c_1498, plain, (![A_153]: (~r2_hidden(A_153, '#skF_3') | ~m1_pre_topc(k1_pre_topc(k1_pre_topc('#skF_2', '#skF_3'), '#skF_3'), k1_pre_topc('#skF_2', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1220, c_1492])).
% 3.99/1.67  tff(c_1506, plain, (![A_153]: (~r2_hidden(A_153, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_1498])).
% 3.99/1.67  tff(c_1656, plain, (![A_173, B_174]: (r2_hidden('#skF_1'(A_173, B_174), B_174) | v2_tex_2(B_174, A_173) | ~m1_subset_1(B_174, k1_zfmisc_1(u1_struct_0(A_173))) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.99/1.67  tff(c_1672, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_1656])).
% 3.99/1.67  tff(c_1689, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3'), '#skF_3') | v2_tex_2('#skF_3', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_1672])).
% 3.99/1.67  tff(c_1691, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_1506, c_1689])).
% 3.99/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.67  
% 3.99/1.67  Inference rules
% 3.99/1.67  ----------------------
% 3.99/1.67  #Ref     : 0
% 3.99/1.67  #Sup     : 395
% 3.99/1.67  #Fact    : 0
% 3.99/1.67  #Define  : 0
% 3.99/1.67  #Split   : 10
% 3.99/1.67  #Chain   : 0
% 3.99/1.67  #Close   : 0
% 3.99/1.67  
% 3.99/1.67  Ordering : KBO
% 3.99/1.67  
% 3.99/1.67  Simplification rules
% 3.99/1.67  ----------------------
% 3.99/1.67  #Subsume      : 35
% 3.99/1.67  #Demod        : 249
% 3.99/1.67  #Tautology    : 85
% 3.99/1.67  #SimpNegUnit  : 32
% 3.99/1.67  #BackRed      : 0
% 3.99/1.67  
% 3.99/1.67  #Partial instantiations: 0
% 3.99/1.67  #Strategies tried      : 1
% 3.99/1.67  
% 3.99/1.67  Timing (in seconds)
% 3.99/1.67  ----------------------
% 3.99/1.67  Preprocessing        : 0.33
% 3.99/1.67  Parsing              : 0.18
% 3.99/1.67  CNF conversion       : 0.02
% 3.99/1.67  Main loop            : 0.57
% 3.99/1.67  Inferencing          : 0.20
% 3.99/1.67  Reduction            : 0.18
% 3.99/1.67  Demodulation         : 0.12
% 3.99/1.67  BG Simplification    : 0.03
% 3.99/1.67  Subsumption          : 0.13
% 3.99/1.67  Abstraction          : 0.02
% 3.99/1.67  MUC search           : 0.00
% 3.99/1.67  Cooper               : 0.00
% 3.99/1.67  Total                : 0.94
% 3.99/1.67  Index Insertion      : 0.00
% 3.99/1.67  Index Deletion       : 0.00
% 3.99/1.67  Index Matching       : 0.00
% 3.99/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
