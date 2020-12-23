%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:47 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 198 expanded)
%              Number of leaves         :   32 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  196 ( 641 expanded)
%              Number of equality atoms :    7 (  16 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_83,axiom,(
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

tff(f_129,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
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

tff(f_38,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_103,axiom,(
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

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_34,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_38,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_69,plain,(
    ! [A_54,B_55] :
      ( v1_pre_topc('#skF_2'(A_54,B_55))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(u1_struct_0(A_54)))
      | v1_xboole_0(B_55)
      | ~ l1_pre_topc(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_75,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_69])).

tff(c_79,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_75])).

tff(c_80,plain,
    ( v1_pre_topc('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_79])).

tff(c_81,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_42,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_152,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_3'(A_68,B_69),B_69)
      | v2_tex_2(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(u1_struct_0(A_68)))
      | ~ l1_pre_topc(A_68)
      | ~ v2_pre_topc(A_68)
      | v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_158,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_152])).

tff(c_162,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_158])).

tff(c_163,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_34,c_162])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_163,c_2])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_166])).

tff(c_172,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_173,plain,(
    ! [A_70,B_71] :
      ( m1_pre_topc('#skF_2'(A_70,B_71),A_70)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0(A_70)))
      | v1_xboole_0(B_71)
      | ~ l1_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_177,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_173])).

tff(c_181,plain,
    ( m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_177])).

tff(c_182,plain,(
    m1_pre_topc('#skF_2'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_172,c_181])).

tff(c_56,plain,(
    ! [A_52,B_53] :
      ( ~ v2_struct_0('#skF_2'(A_52,B_53))
      | ~ m1_subset_1(B_53,k1_zfmisc_1(u1_struct_0(A_52)))
      | v1_xboole_0(B_53)
      | ~ l1_pre_topc(A_52)
      | v2_struct_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_62,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_56])).

tff(c_66,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_62])).

tff(c_67,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_66])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_40,plain,(
    v1_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_10,plain,(
    ! [B_11,A_9] :
      ( v1_tdlat_3(B_11)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9)
      | ~ v1_tdlat_3(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_185,plain,
    ( v1_tdlat_3('#skF_2'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_10])).

tff(c_188,plain,
    ( v1_tdlat_3('#skF_2'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_185])).

tff(c_189,plain,(
    v1_tdlat_3('#skF_2'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_188])).

tff(c_192,plain,(
    ! [A_76,B_77] :
      ( u1_struct_0('#skF_2'(A_76,B_77)) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | v1_xboole_0(B_77)
      | ~ l1_pre_topc(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_198,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_192])).

tff(c_202,plain,
    ( u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_198])).

tff(c_203,plain,(
    u1_struct_0('#skF_2'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_172,c_202])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( m1_subset_1(u1_struct_0(B_7),k1_zfmisc_1(u1_struct_0(A_5)))
      | ~ m1_pre_topc(B_7,A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_397,plain,(
    ! [B_93,A_94] :
      ( v2_tex_2(u1_struct_0(B_93),A_94)
      | ~ v1_tdlat_3(B_93)
      | ~ m1_subset_1(u1_struct_0(B_93),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ m1_pre_topc(B_93,A_94)
      | v2_struct_0(B_93)
      | ~ l1_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_418,plain,(
    ! [B_95,A_96] :
      ( v2_tex_2(u1_struct_0(B_95),A_96)
      | ~ v1_tdlat_3(B_95)
      | v2_struct_0(B_95)
      | v2_struct_0(A_96)
      | ~ m1_pre_topc(B_95,A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(resolution,[status(thm)],[c_6,c_397])).

tff(c_424,plain,(
    ! [A_96] :
      ( v2_tex_2('#skF_5',A_96)
      | ~ v1_tdlat_3('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(A_96)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_418])).

tff(c_426,plain,(
    ! [A_96] :
      ( v2_tex_2('#skF_5',A_96)
      | v2_struct_0('#skF_2'('#skF_4','#skF_5'))
      | v2_struct_0(A_96)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_96)
      | ~ l1_pre_topc(A_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_424])).

tff(c_428,plain,(
    ! [A_97] :
      ( v2_tex_2('#skF_5',A_97)
      | v2_struct_0(A_97)
      | ~ m1_pre_topc('#skF_2'('#skF_4','#skF_5'),A_97)
      | ~ l1_pre_topc(A_97) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_426])).

tff(c_431,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_428])).

tff(c_434,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_431])).

tff(c_436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_34,c_434])).

tff(c_437,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_475,plain,(
    ! [A_108,B_109] :
      ( r2_hidden('#skF_3'(A_108,B_109),B_109)
      | v2_tex_2(B_109,A_108)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_479,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_475])).

tff(c_483,plain,
    ( r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5')
    | v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_479])).

tff(c_484,plain,(
    r2_hidden('#skF_3'('#skF_4','#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_34,c_483])).

tff(c_487,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_484,c_2])).

tff(c_491,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:43:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.41  
% 2.66/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.41  %$ v3_pre_topc > v2_tex_2 > v1_tsep_1 > v1_borsuk_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k9_subset_1 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 2.66/1.41  
% 2.66/1.41  %Foreground sorts:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Background operators:
% 2.66/1.41  
% 2.66/1.41  
% 2.66/1.41  %Foreground operators:
% 2.66/1.41  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.41  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.66/1.41  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.66/1.41  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.66/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.66/1.41  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.66/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.41  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.66/1.41  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.66/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.41  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 2.66/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.66/1.41  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.66/1.41  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.66/1.41  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.41  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.66/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.41  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 2.66/1.41  
% 2.66/1.43  tff(f_144, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_tex_2)).
% 2.66/1.43  tff(f_83, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_tsep_1)).
% 2.66/1.43  tff(f_129, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_hidden(C, B) & (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => ~(v3_pre_topc(D, A) & (k9_subset_1(u1_struct_0(A), B, D) = k6_domain_1(u1_struct_0(A), C)))))))) => v2_tex_2(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_tex_2)).
% 2.66/1.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.66/1.43  tff(f_62, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((v1_borsuk_1(B, A) & v1_tsep_1(B, A)) & v1_tdlat_3(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_tdlat_3)).
% 2.66/1.43  tff(f_38, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 2.66/1.43  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_tex_2)).
% 2.66/1.43  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.66/1.43  tff(c_34, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.66/1.43  tff(c_38, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.66/1.43  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.66/1.43  tff(c_69, plain, (![A_54, B_55]: (v1_pre_topc('#skF_2'(A_54, B_55)) | ~m1_subset_1(B_55, k1_zfmisc_1(u1_struct_0(A_54))) | v1_xboole_0(B_55) | ~l1_pre_topc(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.43  tff(c_75, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_69])).
% 2.66/1.43  tff(c_79, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_75])).
% 2.66/1.43  tff(c_80, plain, (v1_pre_topc('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_79])).
% 2.66/1.43  tff(c_81, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_80])).
% 2.66/1.43  tff(c_42, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.66/1.43  tff(c_152, plain, (![A_68, B_69]: (r2_hidden('#skF_3'(A_68, B_69), B_69) | v2_tex_2(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(u1_struct_0(A_68))) | ~l1_pre_topc(A_68) | ~v2_pre_topc(A_68) | v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.66/1.43  tff(c_158, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_152])).
% 2.66/1.43  tff(c_162, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_158])).
% 2.66/1.43  tff(c_163, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_34, c_162])).
% 2.66/1.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.43  tff(c_166, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_163, c_2])).
% 2.66/1.43  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_166])).
% 2.66/1.43  tff(c_172, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_80])).
% 2.66/1.43  tff(c_173, plain, (![A_70, B_71]: (m1_pre_topc('#skF_2'(A_70, B_71), A_70) | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0(A_70))) | v1_xboole_0(B_71) | ~l1_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.43  tff(c_177, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_173])).
% 2.66/1.43  tff(c_181, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_177])).
% 2.66/1.43  tff(c_182, plain, (m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_172, c_181])).
% 2.66/1.43  tff(c_56, plain, (![A_52, B_53]: (~v2_struct_0('#skF_2'(A_52, B_53)) | ~m1_subset_1(B_53, k1_zfmisc_1(u1_struct_0(A_52))) | v1_xboole_0(B_53) | ~l1_pre_topc(A_52) | v2_struct_0(A_52))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.43  tff(c_62, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_56])).
% 2.66/1.43  tff(c_66, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_62])).
% 2.66/1.43  tff(c_67, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_66])).
% 2.66/1.43  tff(c_68, plain, (~v2_struct_0('#skF_2'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_67])).
% 2.66/1.43  tff(c_40, plain, (v1_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.66/1.43  tff(c_10, plain, (![B_11, A_9]: (v1_tdlat_3(B_11) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9) | ~v1_tdlat_3(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.66/1.43  tff(c_185, plain, (v1_tdlat_3('#skF_2'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_182, c_10])).
% 2.66/1.43  tff(c_188, plain, (v1_tdlat_3('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_185])).
% 2.66/1.43  tff(c_189, plain, (v1_tdlat_3('#skF_2'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_44, c_188])).
% 2.66/1.43  tff(c_192, plain, (![A_76, B_77]: (u1_struct_0('#skF_2'(A_76, B_77))=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | v1_xboole_0(B_77) | ~l1_pre_topc(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.66/1.43  tff(c_198, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_192])).
% 2.66/1.43  tff(c_202, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_198])).
% 2.66/1.43  tff(c_203, plain, (u1_struct_0('#skF_2'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_44, c_172, c_202])).
% 2.66/1.43  tff(c_6, plain, (![B_7, A_5]: (m1_subset_1(u1_struct_0(B_7), k1_zfmisc_1(u1_struct_0(A_5))) | ~m1_pre_topc(B_7, A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.66/1.43  tff(c_397, plain, (![B_93, A_94]: (v2_tex_2(u1_struct_0(B_93), A_94) | ~v1_tdlat_3(B_93) | ~m1_subset_1(u1_struct_0(B_93), k1_zfmisc_1(u1_struct_0(A_94))) | ~m1_pre_topc(B_93, A_94) | v2_struct_0(B_93) | ~l1_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.66/1.43  tff(c_418, plain, (![B_95, A_96]: (v2_tex_2(u1_struct_0(B_95), A_96) | ~v1_tdlat_3(B_95) | v2_struct_0(B_95) | v2_struct_0(A_96) | ~m1_pre_topc(B_95, A_96) | ~l1_pre_topc(A_96))), inference(resolution, [status(thm)], [c_6, c_397])).
% 2.66/1.43  tff(c_424, plain, (![A_96]: (v2_tex_2('#skF_5', A_96) | ~v1_tdlat_3('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(A_96) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_96) | ~l1_pre_topc(A_96))), inference(superposition, [status(thm), theory('equality')], [c_203, c_418])).
% 2.66/1.43  tff(c_426, plain, (![A_96]: (v2_tex_2('#skF_5', A_96) | v2_struct_0('#skF_2'('#skF_4', '#skF_5')) | v2_struct_0(A_96) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_96) | ~l1_pre_topc(A_96))), inference(demodulation, [status(thm), theory('equality')], [c_189, c_424])).
% 2.66/1.43  tff(c_428, plain, (![A_97]: (v2_tex_2('#skF_5', A_97) | v2_struct_0(A_97) | ~m1_pre_topc('#skF_2'('#skF_4', '#skF_5'), A_97) | ~l1_pre_topc(A_97))), inference(negUnitSimplification, [status(thm)], [c_68, c_426])).
% 2.66/1.43  tff(c_431, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_182, c_428])).
% 2.66/1.43  tff(c_434, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_431])).
% 2.66/1.43  tff(c_436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_34, c_434])).
% 2.66/1.43  tff(c_437, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_67])).
% 2.66/1.43  tff(c_475, plain, (![A_108, B_109]: (r2_hidden('#skF_3'(A_108, B_109), B_109) | v2_tex_2(B_109, A_108) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_129])).
% 2.66/1.43  tff(c_479, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_36, c_475])).
% 2.66/1.43  tff(c_483, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5') | v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_479])).
% 2.66/1.43  tff(c_484, plain, (r2_hidden('#skF_3'('#skF_4', '#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_34, c_483])).
% 2.66/1.43  tff(c_487, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_484, c_2])).
% 2.66/1.43  tff(c_491, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_437, c_487])).
% 2.66/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.43  
% 2.66/1.43  Inference rules
% 2.66/1.43  ----------------------
% 2.66/1.43  #Ref     : 0
% 2.66/1.43  #Sup     : 95
% 2.66/1.43  #Fact    : 0
% 2.66/1.43  #Define  : 0
% 2.66/1.43  #Split   : 3
% 2.66/1.43  #Chain   : 0
% 2.66/1.43  #Close   : 0
% 2.66/1.43  
% 2.66/1.43  Ordering : KBO
% 2.66/1.43  
% 2.66/1.43  Simplification rules
% 2.66/1.43  ----------------------
% 2.66/1.43  #Subsume      : 13
% 2.66/1.43  #Demod        : 43
% 2.66/1.43  #Tautology    : 15
% 2.66/1.43  #SimpNegUnit  : 36
% 2.66/1.43  #BackRed      : 0
% 2.66/1.43  
% 2.66/1.43  #Partial instantiations: 0
% 2.66/1.43  #Strategies tried      : 1
% 2.66/1.43  
% 2.66/1.43  Timing (in seconds)
% 2.66/1.43  ----------------------
% 2.66/1.43  Preprocessing        : 0.31
% 2.66/1.43  Parsing              : 0.17
% 2.66/1.43  CNF conversion       : 0.02
% 2.66/1.43  Main loop            : 0.30
% 2.66/1.43  Inferencing          : 0.12
% 2.66/1.43  Reduction            : 0.08
% 2.66/1.43  Demodulation         : 0.06
% 2.66/1.43  BG Simplification    : 0.02
% 2.66/1.43  Subsumption          : 0.06
% 2.66/1.43  Abstraction          : 0.01
% 2.66/1.43  MUC search           : 0.00
% 2.66/1.43  Cooper               : 0.00
% 2.66/1.43  Total                : 0.64
% 2.66/1.43  Index Insertion      : 0.00
% 2.66/1.43  Index Deletion       : 0.00
% 2.66/1.43  Index Matching       : 0.00
% 2.66/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
