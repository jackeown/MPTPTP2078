%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:35 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 251 expanded)
%              Number of leaves         :   37 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          :  228 ( 715 expanded)
%              Number of equality atoms :   11 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_137,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( v2_pre_topc(k1_tex_2(A,B))
           => ( v1_tdlat_3(k1_tex_2(A,B))
              & v2_tdlat_3(k1_tex_2(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tex_2)).

tff(f_109,axiom,(
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

tff(f_157,axiom,(
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

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_124,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(B_65,k1_connsp_2(A_66,B_65))
      | ~ m1_subset_1(B_65,u1_struct_0(A_66))
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [A_67,B_68] :
      ( ~ v1_xboole_0(k1_connsp_2(A_67,B_68))
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_124,c_2])).

tff(c_132,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_129])).

tff(c_135,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_132])).

tff(c_136,plain,(
    ~ v1_xboole_0(k1_connsp_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_135])).

tff(c_76,plain,(
    ! [A_55,B_56] :
      ( k6_domain_1(A_55,B_56) = k1_tarski(B_56)
      | ~ m1_subset_1(B_56,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_84,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_76])).

tff(c_85,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_153,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k1_connsp_2(A_73,B_74),k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ m1_subset_1(B_74,u1_struct_0(A_73))
      | ~ l1_pre_topc(A_73)
      | ~ v2_pre_topc(A_73)
      | v2_struct_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( v1_xboole_0(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_162,plain,(
    ! [A_75,B_76] :
      ( v1_xboole_0(k1_connsp_2(A_75,B_76))
      | ~ v1_xboole_0(u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75)
      | v2_struct_0(A_75) ) ),
    inference(resolution,[status(thm)],[c_153,c_10])).

tff(c_165,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_2','#skF_3'))
    | ~ v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_162])).

tff(c_168,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_85,c_165])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_136,c_168])).

tff(c_172,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_194,plain,(
    ! [A_81,B_82] :
      ( m1_pre_topc(k1_tex_2(A_81,B_82),A_81)
      | ~ m1_subset_1(B_82,u1_struct_0(A_81))
      | ~ l1_pre_topc(A_81)
      | v2_struct_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_196,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_194])).

tff(c_199,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_196])).

tff(c_200,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_199])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k1_tarski(A_6),k1_zfmisc_1(B_7))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_178,plain,(
    ! [A_77,B_78] :
      ( ~ v2_struct_0(k1_tex_2(A_77,B_78))
      | ~ m1_subset_1(B_78,u1_struct_0(A_77))
      | ~ l1_pre_topc(A_77)
      | v2_struct_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_181,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_178])).

tff(c_184,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_181])).

tff(c_185,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_184])).

tff(c_14,plain,(
    ! [B_15,A_13] :
      ( v2_pre_topc(B_15)
      | ~ m1_pre_topc(B_15,A_13)
      | ~ l1_pre_topc(A_13)
      | ~ v2_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_203,plain,
    ( v2_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_200,c_14])).

tff(c_206,plain,(
    v2_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_203])).

tff(c_237,plain,(
    ! [A_91,B_92] :
      ( v1_tdlat_3(k1_tex_2(A_91,B_92))
      | ~ v2_pre_topc(k1_tex_2(A_91,B_92))
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_240,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_2','#skF_3'))
    | ~ v2_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_237])).

tff(c_243,plain,
    ( v1_tdlat_3(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_206,c_240])).

tff(c_244,plain,(
    v1_tdlat_3(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_243])).

tff(c_186,plain,(
    ! [A_79,B_80] :
      ( v1_pre_topc(k1_tex_2(A_79,B_80))
      | ~ m1_subset_1(B_80,u1_struct_0(A_79))
      | ~ l1_pre_topc(A_79)
      | v2_struct_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_189,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_186])).

tff(c_192,plain,
    ( v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_189])).

tff(c_193,plain,(
    v1_pre_topc(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_192])).

tff(c_171,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_270,plain,(
    ! [A_104,B_105] :
      ( k6_domain_1(u1_struct_0(A_104),B_105) = u1_struct_0(k1_tex_2(A_104,B_105))
      | ~ m1_pre_topc(k1_tex_2(A_104,B_105),A_104)
      | ~ v1_pre_topc(k1_tex_2(A_104,B_105))
      | v2_struct_0(k1_tex_2(A_104,B_105))
      | ~ m1_subset_1(B_105,u1_struct_0(A_104))
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_272,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ v1_pre_topc(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_200,c_270])).

tff(c_275,plain,
    ( u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = k1_tarski('#skF_3')
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_193,c_171,c_272])).

tff(c_276,plain,(
    u1_struct_0(k1_tex_2('#skF_2','#skF_3')) = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_185,c_275])).

tff(c_36,plain,(
    ! [B_39,A_35] :
      ( v2_tex_2(u1_struct_0(B_39),A_35)
      | ~ v1_tdlat_3(B_39)
      | ~ m1_subset_1(u1_struct_0(B_39),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(B_39,A_35)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_282,plain,(
    ! [A_35] :
      ( v2_tex_2(u1_struct_0(k1_tex_2('#skF_2','#skF_3')),A_35)
      | ~ v1_tdlat_3(k1_tex_2('#skF_2','#skF_3'))
      | ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),A_35)
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_276,c_36])).

tff(c_320,plain,(
    ! [A_35] :
      ( v2_tex_2(k1_tarski('#skF_3'),A_35)
      | ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0(A_35)))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),A_35)
      | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
      | ~ l1_pre_topc(A_35)
      | v2_struct_0(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_276,c_282])).

tff(c_366,plain,(
    ! [A_109] :
      ( v2_tex_2(k1_tarski('#skF_3'),A_109)
      | ~ m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),A_109)
      | ~ l1_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_320])).

tff(c_375,plain,(
    ! [A_110] :
      ( v2_tex_2(k1_tarski('#skF_3'),A_110)
      | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),A_110)
      | ~ l1_pre_topc(A_110)
      | v2_struct_0(A_110)
      | ~ r2_hidden('#skF_3',u1_struct_0(A_110)) ) ),
    inference(resolution,[status(thm)],[c_8,c_366])).

tff(c_40,plain,(
    ~ v2_tex_2(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_173,plain,(
    ~ v2_tex_2(k1_tarski('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_40])).

tff(c_378,plain,
    ( ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_375,c_173])).

tff(c_381,plain,
    ( v2_struct_0('#skF_2')
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_200,c_378])).

tff(c_382,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_381])).

tff(c_385,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_382])).

tff(c_388,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_385])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:01:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.43  
% 2.46/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.43  %$ v2_tex_2 > r2_hidden > m1_subset_1 > m1_pre_topc > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 2.46/1.43  
% 2.46/1.43  %Foreground sorts:
% 2.46/1.43  
% 2.46/1.43  
% 2.46/1.43  %Background operators:
% 2.46/1.43  
% 2.46/1.43  
% 2.46/1.43  %Foreground operators:
% 2.46/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.46/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.46/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.46/1.43  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 2.46/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.46/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.46/1.43  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 2.46/1.43  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.46/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.46/1.43  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 2.46/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.43  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.46/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.43  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.46/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.43  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.46/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.46/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.46/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.46/1.43  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 2.46/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.43  
% 2.84/1.45  tff(f_170, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 2.84/1.45  tff(f_89, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_connsp_2)).
% 2.84/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.84/1.45  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.84/1.45  tff(f_77, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 2.84/1.45  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.84/1.45  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.84/1.45  tff(f_123, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.84/1.45  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.84/1.45  tff(f_59, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 2.84/1.45  tff(f_137, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v2_pre_topc(k1_tex_2(A, B)) => (v1_tdlat_3(k1_tex_2(A, B)) & v2_tdlat_3(k1_tex_2(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_tex_2)).
% 2.84/1.45  tff(f_109, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) => ((C = k1_tex_2(A, B)) <=> (u1_struct_0(C) = k6_domain_1(u1_struct_0(A), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tex_2)).
% 2.84/1.45  tff(f_157, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 2.84/1.45  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 2.84/1.45  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 2.84/1.45  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 2.84/1.45  tff(c_42, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 2.84/1.45  tff(c_124, plain, (![B_65, A_66]: (r2_hidden(B_65, k1_connsp_2(A_66, B_65)) | ~m1_subset_1(B_65, u1_struct_0(A_66)) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.84/1.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.45  tff(c_129, plain, (![A_67, B_68]: (~v1_xboole_0(k1_connsp_2(A_67, B_68)) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(resolution, [status(thm)], [c_124, c_2])).
% 2.84/1.45  tff(c_132, plain, (~v1_xboole_0(k1_connsp_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_129])).
% 2.84/1.45  tff(c_135, plain, (~v1_xboole_0(k1_connsp_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_132])).
% 2.84/1.45  tff(c_136, plain, (~v1_xboole_0(k1_connsp_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_135])).
% 2.84/1.45  tff(c_76, plain, (![A_55, B_56]: (k6_domain_1(A_55, B_56)=k1_tarski(B_56) | ~m1_subset_1(B_56, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.84/1.45  tff(c_84, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_76])).
% 2.84/1.45  tff(c_85, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_84])).
% 2.84/1.45  tff(c_153, plain, (![A_73, B_74]: (m1_subset_1(k1_connsp_2(A_73, B_74), k1_zfmisc_1(u1_struct_0(A_73))) | ~m1_subset_1(B_74, u1_struct_0(A_73)) | ~l1_pre_topc(A_73) | ~v2_pre_topc(A_73) | v2_struct_0(A_73))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.84/1.45  tff(c_10, plain, (![B_10, A_8]: (v1_xboole_0(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.84/1.45  tff(c_162, plain, (![A_75, B_76]: (v1_xboole_0(k1_connsp_2(A_75, B_76)) | ~v1_xboole_0(u1_struct_0(A_75)) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75) | v2_struct_0(A_75))), inference(resolution, [status(thm)], [c_153, c_10])).
% 2.84/1.45  tff(c_165, plain, (v1_xboole_0(k1_connsp_2('#skF_2', '#skF_3')) | ~v1_xboole_0(u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_162])).
% 2.84/1.45  tff(c_168, plain, (v1_xboole_0(k1_connsp_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_85, c_165])).
% 2.84/1.45  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_136, c_168])).
% 2.84/1.45  tff(c_172, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_84])).
% 2.84/1.45  tff(c_12, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.84/1.45  tff(c_194, plain, (![A_81, B_82]: (m1_pre_topc(k1_tex_2(A_81, B_82), A_81) | ~m1_subset_1(B_82, u1_struct_0(A_81)) | ~l1_pre_topc(A_81) | v2_struct_0(A_81))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.84/1.45  tff(c_196, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_194])).
% 2.84/1.45  tff(c_199, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_196])).
% 2.84/1.45  tff(c_200, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_199])).
% 2.84/1.45  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(k1_tarski(A_6), k1_zfmisc_1(B_7)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.45  tff(c_178, plain, (![A_77, B_78]: (~v2_struct_0(k1_tex_2(A_77, B_78)) | ~m1_subset_1(B_78, u1_struct_0(A_77)) | ~l1_pre_topc(A_77) | v2_struct_0(A_77))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.84/1.45  tff(c_181, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_178])).
% 2.84/1.45  tff(c_184, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_181])).
% 2.84/1.45  tff(c_185, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_184])).
% 2.84/1.45  tff(c_14, plain, (![B_15, A_13]: (v2_pre_topc(B_15) | ~m1_pre_topc(B_15, A_13) | ~l1_pre_topc(A_13) | ~v2_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.45  tff(c_203, plain, (v2_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_200, c_14])).
% 2.84/1.45  tff(c_206, plain, (v2_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_203])).
% 2.84/1.45  tff(c_237, plain, (![A_91, B_92]: (v1_tdlat_3(k1_tex_2(A_91, B_92)) | ~v2_pre_topc(k1_tex_2(A_91, B_92)) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.84/1.45  tff(c_240, plain, (v1_tdlat_3(k1_tex_2('#skF_2', '#skF_3')) | ~v2_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_237])).
% 2.84/1.45  tff(c_243, plain, (v1_tdlat_3(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_206, c_240])).
% 2.84/1.45  tff(c_244, plain, (v1_tdlat_3(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_243])).
% 2.84/1.45  tff(c_186, plain, (![A_79, B_80]: (v1_pre_topc(k1_tex_2(A_79, B_80)) | ~m1_subset_1(B_80, u1_struct_0(A_79)) | ~l1_pre_topc(A_79) | v2_struct_0(A_79))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.84/1.45  tff(c_189, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_42, c_186])).
% 2.84/1.45  tff(c_192, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_189])).
% 2.84/1.45  tff(c_193, plain, (v1_pre_topc(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_48, c_192])).
% 2.84/1.45  tff(c_171, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_84])).
% 2.84/1.45  tff(c_270, plain, (![A_104, B_105]: (k6_domain_1(u1_struct_0(A_104), B_105)=u1_struct_0(k1_tex_2(A_104, B_105)) | ~m1_pre_topc(k1_tex_2(A_104, B_105), A_104) | ~v1_pre_topc(k1_tex_2(A_104, B_105)) | v2_struct_0(k1_tex_2(A_104, B_105)) | ~m1_subset_1(B_105, u1_struct_0(A_104)) | ~l1_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.84/1.45  tff(c_272, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~v1_pre_topc(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_200, c_270])).
% 2.84/1.45  tff(c_275, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=k1_tarski('#skF_3') | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_193, c_171, c_272])).
% 2.84/1.45  tff(c_276, plain, (u1_struct_0(k1_tex_2('#skF_2', '#skF_3'))=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_185, c_275])).
% 2.84/1.45  tff(c_36, plain, (![B_39, A_35]: (v2_tex_2(u1_struct_0(B_39), A_35) | ~v1_tdlat_3(B_39) | ~m1_subset_1(u1_struct_0(B_39), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(B_39, A_35) | v2_struct_0(B_39) | ~l1_pre_topc(A_35) | v2_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_157])).
% 2.84/1.45  tff(c_282, plain, (![A_35]: (v2_tex_2(u1_struct_0(k1_tex_2('#skF_2', '#skF_3')), A_35) | ~v1_tdlat_3(k1_tex_2('#skF_2', '#skF_3')) | ~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), A_35) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc(A_35) | v2_struct_0(A_35))), inference(superposition, [status(thm), theory('equality')], [c_276, c_36])).
% 2.84/1.45  tff(c_320, plain, (![A_35]: (v2_tex_2(k1_tarski('#skF_3'), A_35) | ~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0(A_35))) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), A_35) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc(A_35) | v2_struct_0(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_276, c_282])).
% 2.84/1.45  tff(c_366, plain, (![A_109]: (v2_tex_2(k1_tarski('#skF_3'), A_109) | ~m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), A_109) | ~l1_pre_topc(A_109) | v2_struct_0(A_109))), inference(negUnitSimplification, [status(thm)], [c_185, c_320])).
% 2.84/1.45  tff(c_375, plain, (![A_110]: (v2_tex_2(k1_tarski('#skF_3'), A_110) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), A_110) | ~l1_pre_topc(A_110) | v2_struct_0(A_110) | ~r2_hidden('#skF_3', u1_struct_0(A_110)))), inference(resolution, [status(thm)], [c_8, c_366])).
% 2.84/1.45  tff(c_40, plain, (~v2_tex_2(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 2.84/1.45  tff(c_173, plain, (~v2_tex_2(k1_tarski('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_40])).
% 2.84/1.45  tff(c_378, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_375, c_173])).
% 2.84/1.45  tff(c_381, plain, (v2_struct_0('#skF_2') | ~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_200, c_378])).
% 2.84/1.45  tff(c_382, plain, (~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_48, c_381])).
% 2.84/1.45  tff(c_385, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_12, c_382])).
% 2.84/1.45  tff(c_388, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_385])).
% 2.84/1.45  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_388])).
% 2.84/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.45  
% 2.84/1.45  Inference rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Ref     : 0
% 2.84/1.45  #Sup     : 60
% 2.84/1.45  #Fact    : 0
% 2.84/1.45  #Define  : 0
% 2.84/1.45  #Split   : 2
% 2.84/1.45  #Chain   : 0
% 2.84/1.45  #Close   : 0
% 2.84/1.45  
% 2.84/1.45  Ordering : KBO
% 2.84/1.45  
% 2.84/1.45  Simplification rules
% 2.84/1.45  ----------------------
% 2.84/1.45  #Subsume      : 9
% 2.84/1.45  #Demod        : 52
% 2.84/1.45  #Tautology    : 16
% 2.84/1.45  #SimpNegUnit  : 34
% 2.84/1.45  #BackRed      : 1
% 2.84/1.45  
% 2.84/1.45  #Partial instantiations: 0
% 2.84/1.45  #Strategies tried      : 1
% 2.84/1.45  
% 2.84/1.45  Timing (in seconds)
% 2.84/1.45  ----------------------
% 2.84/1.45  Preprocessing        : 0.34
% 2.84/1.45  Parsing              : 0.18
% 2.84/1.45  CNF conversion       : 0.02
% 2.84/1.45  Main loop            : 0.27
% 2.84/1.45  Inferencing          : 0.10
% 2.84/1.45  Reduction            : 0.08
% 2.84/1.45  Demodulation         : 0.05
% 2.84/1.46  BG Simplification    : 0.02
% 2.84/1.46  Subsumption          : 0.05
% 2.84/1.46  Abstraction          : 0.02
% 2.84/1.46  MUC search           : 0.00
% 2.84/1.46  Cooper               : 0.00
% 2.84/1.46  Total                : 0.66
% 2.84/1.46  Index Insertion      : 0.00
% 2.84/1.46  Index Deletion       : 0.00
% 2.84/1.46  Index Matching       : 0.00
% 2.84/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
