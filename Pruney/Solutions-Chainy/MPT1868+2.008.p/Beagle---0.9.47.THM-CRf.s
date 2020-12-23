%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:36 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 237 expanded)
%              Number of leaves         :   35 (  98 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 ( 678 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

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

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_164,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_117,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_131,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v2_pre_topc(k1_tex_2(A,B))
           => ( v1_tdlat_3(k1_tex_2(A,B))
              & v2_tdlat_3(k1_tex_2(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v1_pre_topc(C)
                & m1_pre_topc(C,A) )
             => ( C = k1_tex_2(A,B)
              <=> u1_struct_0(C) = k6_domain_1(u1_struct_0(A),B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tex_2)).

tff(f_151,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_42,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_66,plain,(
    ! [A_52,B_53] :
      ( k6_domain_1(A_52,B_53) = k1_tarski(B_53)
      | ~ m1_subset_1(B_53,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_38,c_66])).

tff(c_75,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_16,plain,(
    ! [B_18,A_16] :
      ( r2_hidden(B_18,k1_connsp_2(A_16,B_18))
      | ~ m1_subset_1(B_18,u1_struct_0(A_16))
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_138,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k1_connsp_2(A_71,B_72),k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(B_72,u1_struct_0(A_71))
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [C_8,B_7,A_6] :
      ( ~ v1_xboole_0(C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_147,plain,(
    ! [A_75,A_76,B_77] :
      ( ~ v1_xboole_0(u1_struct_0(A_75))
      | ~ r2_hidden(A_76,k1_connsp_2(A_75,B_77))
      | ~ m1_subset_1(B_77,u1_struct_0(A_75))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_138,c_8])).

tff(c_157,plain,(
    ! [A_78,B_79] :
      ( ~ v1_xboole_0(u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78)
      | v2_struct_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_16,c_147])).

tff(c_160,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_157])).

tff(c_163,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_75,c_160])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_163])).

tff(c_167,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_189,plain,(
    ! [A_84,B_85] :
      ( m1_pre_topc(k1_tex_2(A_84,B_85),A_84)
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l1_pre_topc(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_191,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_189])).

tff(c_194,plain,
    ( m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_191])).

tff(c_195,plain,(
    m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_194])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(k1_tarski(A_2),k1_zfmisc_1(B_3))
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [A_80,B_81] :
      ( ~ v2_struct_0(k1_tex_2(A_80,B_81))
      | ~ m1_subset_1(B_81,u1_struct_0(A_80))
      | ~ l1_pre_topc(A_80)
      | v2_struct_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_176,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_173])).

tff(c_179,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_176])).

tff(c_180,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_179])).

tff(c_10,plain,(
    ! [B_11,A_9] :
      ( v2_pre_topc(B_11)
      | ~ m1_pre_topc(B_11,A_9)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_198,plain,
    ( v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_195,c_10])).

tff(c_201,plain,(
    v2_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_198])).

tff(c_219,plain,(
    ! [A_93,B_94] :
      ( v1_tdlat_3(k1_tex_2(A_93,B_94))
      | ~ v2_pre_topc(k1_tex_2(A_93,B_94))
      | ~ m1_subset_1(B_94,u1_struct_0(A_93))
      | ~ l1_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_222,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | ~ v2_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_219])).

tff(c_225,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_201,c_222])).

tff(c_226,plain,(
    v1_tdlat_3(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_225])).

tff(c_181,plain,(
    ! [A_82,B_83] :
      ( v1_pre_topc(k1_tex_2(A_82,B_83))
      | ~ m1_subset_1(B_83,u1_struct_0(A_82))
      | ~ l1_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_184,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_181])).

tff(c_187,plain,
    ( v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_184])).

tff(c_188,plain,(
    v1_pre_topc(k1_tex_2('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_187])).

tff(c_166,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_288,plain,(
    ! [A_117,B_118] :
      ( k6_domain_1(u1_struct_0(A_117),B_118) = u1_struct_0(k1_tex_2(A_117,B_118))
      | ~ m1_pre_topc(k1_tex_2(A_117,B_118),A_117)
      | ~ v1_pre_topc(k1_tex_2(A_117,B_118))
      | v2_struct_0(k1_tex_2(A_117,B_118))
      | ~ m1_subset_1(B_118,u1_struct_0(A_117))
      | ~ l1_pre_topc(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_290,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = u1_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ v1_pre_topc(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_195,c_288])).

tff(c_293,plain,
    ( u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = k1_tarski('#skF_2')
    | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_188,c_166,c_290])).

tff(c_294,plain,(
    u1_struct_0(k1_tex_2('#skF_1','#skF_2')) = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_180,c_293])).

tff(c_32,plain,(
    ! [B_35,A_31] :
      ( v2_tex_2(u1_struct_0(B_35),A_31)
      | ~ v1_tdlat_3(B_35)
      | ~ m1_subset_1(u1_struct_0(B_35),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(B_35,A_31)
      | v2_struct_0(B_35)
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_309,plain,(
    ! [A_31] :
      ( v2_tex_2(u1_struct_0(k1_tex_2('#skF_1','#skF_2')),A_31)
      | ~ v1_tdlat_3(k1_tex_2('#skF_1','#skF_2'))
      | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),A_31)
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_32])).

tff(c_344,plain,(
    ! [A_31] :
      ( v2_tex_2(k1_tarski('#skF_2'),A_31)
      | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),A_31)
      | v2_struct_0(k1_tex_2('#skF_1','#skF_2'))
      | ~ l1_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_294,c_309])).

tff(c_360,plain,(
    ! [A_119] :
      ( v2_tex_2(k1_tarski('#skF_2'),A_119)
      | ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),A_119)
      | ~ l1_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_180,c_344])).

tff(c_369,plain,(
    ! [A_120] :
      ( v2_tex_2(k1_tarski('#skF_2'),A_120)
      | ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),A_120)
      | ~ l1_pre_topc(A_120)
      | v2_struct_0(A_120)
      | ~ r2_hidden('#skF_2',u1_struct_0(A_120)) ) ),
    inference(resolution,[status(thm)],[c_4,c_360])).

tff(c_36,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_168,plain,(
    ~ v2_tex_2(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_36])).

tff(c_372,plain,
    ( ~ m1_pre_topc(k1_tex_2('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_369,c_168])).

tff(c_375,plain,
    ( v2_struct_0('#skF_1')
    | ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_195,c_372])).

tff(c_376,plain,(
    ~ r2_hidden('#skF_2',u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_375])).

tff(c_379,plain,
    ( v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_376])).

tff(c_382,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_379])).

tff(c_384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_382])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.26/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.33  
% 2.68/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.34  %$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.68/1.34  
% 2.68/1.34  %Foreground sorts:
% 2.68/1.34  
% 2.68/1.34  
% 2.68/1.34  %Background operators:
% 2.68/1.34  
% 2.68/1.34  
% 2.68/1.34  %Foreground operators:
% 2.68/1.34  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.34  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 2.68/1.34  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.68/1.34  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.68/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.68/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.34  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.68/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.34  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.68/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.34  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.68/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.34  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.68/1.34  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.68/1.34  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.68/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.68/1.34  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.68/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.68/1.34  
% 2.68/1.35  tff(f_164, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.68/1.35  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.68/1.35  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 2.68/1.35  tff(f_71, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 2.68/1.35  tff(f_44, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.68/1.35  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.68/1.35  tff(f_117, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.68/1.35  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.68/1.35  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.68/1.35  tff(f_131, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v2_pre_topc(k1_tex_2(A, B)) => (v1_tdlat_3(k1_tex_2(A, B)) & v2_tdlat_3(k1_tex_2(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tex_2)).
% 2.68/1.35  tff(f_103, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 2.68/1.35  tff(f_151, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.68/1.35  tff(c_44, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.68/1.35  tff(c_42, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.68/1.35  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.68/1.35  tff(c_38, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.68/1.35  tff(c_66, plain, (![A_52, B_53]: (k6_domain_1(A_52, B_53)=k1_tarski(B_53) | ~m1_subset_1(B_53, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.68/1.35  tff(c_74, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_38, c_66])).
% 2.68/1.35  tff(c_75, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_74])).
% 2.68/1.35  tff(c_16, plain, (![B_18, A_16]: (r2_hidden(B_18, k1_connsp_2(A_16, B_18)) | ~m1_subset_1(B_18, u1_struct_0(A_16)) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.68/1.35  tff(c_138, plain, (![A_71, B_72]: (m1_subset_1(k1_connsp_2(A_71, B_72), k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_subset_1(B_72, u1_struct_0(A_71)) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.68/1.35  tff(c_8, plain, (![C_8, B_7, A_6]: (~v1_xboole_0(C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.68/1.35  tff(c_147, plain, (![A_75, A_76, B_77]: (~v1_xboole_0(u1_struct_0(A_75)) | ~r2_hidden(A_76, k1_connsp_2(A_75, B_77)) | ~m1_subset_1(B_77, u1_struct_0(A_75)) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(resolution, [status(thm)], [c_138, c_8])).
% 2.68/1.35  tff(c_157, plain, (![A_78, B_79]: (~v1_xboole_0(u1_struct_0(A_78)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78) | v2_struct_0(A_78))), inference(resolution, [status(thm)], [c_16, c_147])).
% 2.68/1.35  tff(c_160, plain, (~v1_xboole_0(u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_157])).
% 2.68/1.35  tff(c_163, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_75, c_160])).
% 2.68/1.35  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_163])).
% 2.68/1.35  tff(c_167, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_74])).
% 2.68/1.35  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.35  tff(c_189, plain, (![A_84, B_85]: (m1_pre_topc(k1_tex_2(A_84, B_85), A_84) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l1_pre_topc(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.68/1.35  tff(c_191, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_189])).
% 2.68/1.35  tff(c_194, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_191])).
% 2.68/1.35  tff(c_195, plain, (m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_44, c_194])).
% 2.68/1.35  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(k1_tarski(A_2), k1_zfmisc_1(B_3)) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.35  tff(c_173, plain, (![A_80, B_81]: (~v2_struct_0(k1_tex_2(A_80, B_81)) | ~m1_subset_1(B_81, u1_struct_0(A_80)) | ~l1_pre_topc(A_80) | v2_struct_0(A_80))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.68/1.35  tff(c_176, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_173])).
% 2.68/1.35  tff(c_179, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_176])).
% 2.68/1.35  tff(c_180, plain, (~v2_struct_0(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_179])).
% 2.68/1.35  tff(c_10, plain, (![B_11, A_9]: (v2_pre_topc(B_11) | ~m1_pre_topc(B_11, A_9) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.68/1.35  tff(c_198, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_195, c_10])).
% 2.68/1.35  tff(c_201, plain, (v2_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_198])).
% 2.68/1.35  tff(c_219, plain, (![A_93, B_94]: (v1_tdlat_3(k1_tex_2(A_93, B_94)) | ~v2_pre_topc(k1_tex_2(A_93, B_94)) | ~m1_subset_1(B_94, u1_struct_0(A_93)) | ~l1_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.68/1.35  tff(c_222, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~v2_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_219])).
% 2.68/1.35  tff(c_225, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_201, c_222])).
% 2.68/1.35  tff(c_226, plain, (v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_225])).
% 2.68/1.35  tff(c_181, plain, (![A_82, B_83]: (v1_pre_topc(k1_tex_2(A_82, B_83)) | ~m1_subset_1(B_83, u1_struct_0(A_82)) | ~l1_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_117])).
% 2.68/1.35  tff(c_184, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_181])).
% 2.68/1.35  tff(c_187, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_184])).
% 2.68/1.35  tff(c_188, plain, (v1_pre_topc(k1_tex_2('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_187])).
% 2.68/1.35  tff(c_166, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_74])).
% 2.68/1.35  tff(c_288, plain, (![A_117, B_118]: (k6_domain_1(u1_struct_0(A_117), B_118)=u1_struct_0(k1_tex_2(A_117, B_118)) | ~m1_pre_topc(k1_tex_2(A_117, B_118), A_117) | ~v1_pre_topc(k1_tex_2(A_117, B_118)) | v2_struct_0(k1_tex_2(A_117, B_118)) | ~m1_subset_1(B_118, u1_struct_0(A_117)) | ~l1_pre_topc(A_117) | v2_struct_0(A_117))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.68/1.35  tff(c_290, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=u1_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~v1_pre_topc(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_195, c_288])).
% 2.68/1.35  tff(c_293, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=k1_tarski('#skF_2') | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_188, c_166, c_290])).
% 2.68/1.35  tff(c_294, plain, (u1_struct_0(k1_tex_2('#skF_1', '#skF_2'))=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_180, c_293])).
% 2.68/1.35  tff(c_32, plain, (![B_35, A_31]: (v2_tex_2(u1_struct_0(B_35), A_31) | ~v1_tdlat_3(B_35) | ~m1_subset_1(u1_struct_0(B_35), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(B_35, A_31) | v2_struct_0(B_35) | ~l1_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.68/1.35  tff(c_309, plain, (![A_31]: (v2_tex_2(u1_struct_0(k1_tex_2('#skF_1', '#skF_2')), A_31) | ~v1_tdlat_3(k1_tex_2('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), A_31) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(A_31) | v2_struct_0(A_31))), inference(superposition, [status(thm), theory('equality')], [c_294, c_32])).
% 2.68/1.35  tff(c_344, plain, (![A_31]: (v2_tex_2(k1_tarski('#skF_2'), A_31) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), A_31) | v2_struct_0(k1_tex_2('#skF_1', '#skF_2')) | ~l1_pre_topc(A_31) | v2_struct_0(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_294, c_309])).
% 2.68/1.35  tff(c_360, plain, (![A_119]: (v2_tex_2(k1_tarski('#skF_2'), A_119) | ~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), A_119) | ~l1_pre_topc(A_119) | v2_struct_0(A_119))), inference(negUnitSimplification, [status(thm)], [c_180, c_344])).
% 2.68/1.35  tff(c_369, plain, (![A_120]: (v2_tex_2(k1_tarski('#skF_2'), A_120) | ~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), A_120) | ~l1_pre_topc(A_120) | v2_struct_0(A_120) | ~r2_hidden('#skF_2', u1_struct_0(A_120)))), inference(resolution, [status(thm)], [c_4, c_360])).
% 2.68/1.35  tff(c_36, plain, (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.68/1.35  tff(c_168, plain, (~v2_tex_2(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_36])).
% 2.68/1.35  tff(c_372, plain, (~m1_pre_topc(k1_tex_2('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_369, c_168])).
% 2.68/1.35  tff(c_375, plain, (v2_struct_0('#skF_1') | ~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_195, c_372])).
% 2.68/1.35  tff(c_376, plain, (~r2_hidden('#skF_2', u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_375])).
% 2.68/1.35  tff(c_379, plain, (v1_xboole_0(u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_376])).
% 2.68/1.35  tff(c_382, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_379])).
% 2.68/1.35  tff(c_384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_382])).
% 2.68/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.35  
% 2.68/1.35  Inference rules
% 2.68/1.35  ----------------------
% 2.68/1.35  #Ref     : 0
% 2.68/1.35  #Sup     : 62
% 2.68/1.35  #Fact    : 0
% 2.68/1.35  #Define  : 0
% 2.68/1.35  #Split   : 2
% 2.68/1.35  #Chain   : 0
% 2.68/1.35  #Close   : 0
% 2.68/1.36  
% 2.68/1.36  Ordering : KBO
% 2.68/1.36  
% 2.68/1.36  Simplification rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Subsume      : 9
% 2.68/1.36  #Demod        : 46
% 2.68/1.36  #Tautology    : 16
% 2.68/1.36  #SimpNegUnit  : 31
% 2.68/1.36  #BackRed      : 1
% 2.68/1.36  
% 2.68/1.36  #Partial instantiations: 0
% 2.68/1.36  #Strategies tried      : 1
% 2.68/1.36  
% 2.68/1.36  Timing (in seconds)
% 2.68/1.36  ----------------------
% 2.68/1.36  Preprocessing        : 0.34
% 2.68/1.36  Parsing              : 0.18
% 2.68/1.36  CNF conversion       : 0.02
% 2.68/1.36  Main loop            : 0.25
% 2.68/1.36  Inferencing          : 0.10
% 2.68/1.36  Reduction            : 0.07
% 2.68/1.36  Demodulation         : 0.05
% 2.68/1.36  BG Simplification    : 0.02
% 2.68/1.36  Subsumption          : 0.04
% 2.68/1.36  Abstraction          : 0.01
% 2.68/1.36  MUC search           : 0.00
% 2.68/1.36  Cooper               : 0.00
% 2.68/1.36  Total                : 0.63
% 2.68/1.36  Index Insertion      : 0.00
% 2.68/1.36  Index Deletion       : 0.00
% 2.68/1.36  Index Matching       : 0.00
% 2.68/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
