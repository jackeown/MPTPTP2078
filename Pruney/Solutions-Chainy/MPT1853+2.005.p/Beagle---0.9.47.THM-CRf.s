%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:00 EST 2020

% Result     : Theorem 2.54s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 331 expanded)
%              Number of leaves         :   39 ( 121 expanded)
%              Depth                    :   12
%              Number of atoms          :  239 ( 792 expanded)
%              Number of equality atoms :   12 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v1_tex_2,type,(
    v1_tex_2: ( $i * $i ) > $o )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_tex_2,type,(
    k1_tex_2: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_177,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_151,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_137,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & ~ v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) )
           => ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc13_tex_2)).

tff(f_164,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_37,axiom,(
    ! [A] : v1_zfmisc_1(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_zfmisc_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v7_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ~ v2_struct_0(B)
           => ( ~ v2_struct_0(B)
              & ~ v1_tex_2(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc10_tex_2)).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_52,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_248,plain,(
    ! [A_83,B_84] :
      ( k6_domain_1(A_83,B_84) = k1_tarski(B_84)
      | ~ m1_subset_1(B_84,A_83)
      | v1_xboole_0(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_256,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_248])).

tff(c_257,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_18,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_260,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_257,c_18])).

tff(c_263,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_260])).

tff(c_266,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_263])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_266])).

tff(c_272,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( r2_hidden(A_11,B_12)
      | v1_xboole_0(B_12)
      | ~ m1_subset_1(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k1_tarski(A_9),k1_zfmisc_1(B_10))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_240,plain,(
    ! [B_80,A_81] :
      ( v1_subset_1(B_80,A_81)
      | B_80 = A_81
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_286,plain,(
    ! [A_87,B_88] :
      ( v1_subset_1(k1_tarski(A_87),B_88)
      | k1_tarski(A_87) = B_88
      | ~ r2_hidden(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_12,c_240])).

tff(c_271,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_110,plain,(
    ! [A_52,B_53] :
      ( k6_domain_1(A_52,B_53) = k1_tarski(B_53)
      | ~ m1_subset_1(B_53,A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_118,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_110])).

tff(c_121,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_124,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_121,c_18])).

tff(c_127,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_124])).

tff(c_130,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_127])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_130])).

tff(c_135,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_62,plain,
    ( v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_81,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_137,plain,(
    v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_81])).

tff(c_157,plain,(
    ! [A_58,B_59] :
      ( ~ v2_struct_0(k1_tex_2(A_58,B_59))
      | ~ m1_subset_1(B_59,u1_struct_0(A_58))
      | ~ l1_pre_topc(A_58)
      | v2_struct_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_160,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_157])).

tff(c_163,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_160])).

tff(c_164,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_163])).

tff(c_173,plain,(
    ! [A_62,B_63] :
      ( m1_pre_topc(k1_tex_2(A_62,B_63),A_62)
      | ~ m1_subset_1(B_63,u1_struct_0(A_62))
      | ~ l1_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_175,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_173])).

tff(c_178,plain,
    ( m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_175])).

tff(c_179,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_178])).

tff(c_165,plain,(
    ! [A_60,B_61] :
      ( v7_struct_0(k1_tex_2(A_60,B_61))
      | ~ m1_subset_1(B_61,u1_struct_0(A_60))
      | ~ l1_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_168,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_165])).

tff(c_171,plain,
    ( v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_168])).

tff(c_172,plain,(
    v7_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_171])).

tff(c_190,plain,(
    ! [B_68,A_69] :
      ( ~ v7_struct_0(B_68)
      | v1_tex_2(B_68,A_69)
      | v2_struct_0(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69)
      | v7_struct_0(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_56,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_120,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_56])).

tff(c_196,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_190,c_120])).

tff(c_200,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_179,c_172,c_196])).

tff(c_201,plain,(
    v7_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_164,c_200])).

tff(c_202,plain,(
    ! [A_70,B_71] :
      ( ~ v7_struct_0(A_70)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_70),B_71),u1_struct_0(A_70))
      | ~ m1_subset_1(B_71,u1_struct_0(A_70))
      | ~ l1_struct_0(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_205,plain,
    ( ~ v7_struct_0('#skF_2')
    | ~ v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_202])).

tff(c_207,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_137,c_201,c_205])).

tff(c_208,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_207])).

tff(c_211,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_211])).

tff(c_217,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_281,plain,(
    ~ v1_subset_1(k1_tarski('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_217])).

tff(c_294,plain,
    ( u1_struct_0('#skF_2') = k1_tarski('#skF_3')
    | ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_286,c_281])).

tff(c_297,plain,(
    ~ r2_hidden('#skF_3',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_294])).

tff(c_300,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_297])).

tff(c_303,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_300])).

tff(c_305,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_303])).

tff(c_306,plain,(
    u1_struct_0('#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_294])).

tff(c_311,plain,(
    m1_subset_1('#skF_3',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_50])).

tff(c_331,plain,(
    ! [A_89,B_90] :
      ( ~ v2_struct_0(k1_tex_2(A_89,B_90))
      | ~ m1_subset_1(B_90,u1_struct_0(A_89))
      | ~ l1_pre_topc(A_89)
      | v2_struct_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_334,plain,(
    ! [B_90] :
      ( ~ v2_struct_0(k1_tex_2('#skF_2',B_90))
      | ~ m1_subset_1(B_90,k1_tarski('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_331])).

tff(c_336,plain,(
    ! [B_90] :
      ( ~ v2_struct_0(k1_tex_2('#skF_2',B_90))
      | ~ m1_subset_1(B_90,k1_tarski('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_334])).

tff(c_391,plain,(
    ! [B_95] :
      ( ~ v2_struct_0(k1_tex_2('#skF_2',B_95))
      | ~ m1_subset_1(B_95,k1_tarski('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_336])).

tff(c_395,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_311,c_391])).

tff(c_10,plain,(
    ! [A_8] : v1_zfmisc_1(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_15] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v7_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_318,plain,
    ( ~ v1_zfmisc_1(k1_tarski('#skF_3'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_20])).

tff(c_328,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_318])).

tff(c_349,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_352,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_349])).

tff(c_356,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_352])).

tff(c_357,plain,(
    v7_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_216,plain,(
    v1_tex_2(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_407,plain,(
    ! [B_99,A_100] :
      ( ~ v1_tex_2(B_99,A_100)
      | v2_struct_0(B_99)
      | ~ m1_pre_topc(B_99,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v7_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_410,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v7_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_216,c_407])).

tff(c_413,plain,
    ( v2_struct_0(k1_tex_2('#skF_2','#skF_3'))
    | ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_52,c_410])).

tff(c_414,plain,(
    ~ m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_395,c_413])).

tff(c_396,plain,(
    ! [A_96,B_97] :
      ( m1_pre_topc(k1_tex_2(A_96,B_97),A_96)
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_pre_topc(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_398,plain,(
    ! [B_97] :
      ( m1_pre_topc(k1_tex_2('#skF_2',B_97),'#skF_2')
      | ~ m1_subset_1(B_97,k1_tarski('#skF_3'))
      | ~ l1_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_396])).

tff(c_400,plain,(
    ! [B_97] :
      ( m1_pre_topc(k1_tex_2('#skF_2',B_97),'#skF_2')
      | ~ m1_subset_1(B_97,k1_tarski('#skF_3'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_398])).

tff(c_402,plain,(
    ! [B_98] :
      ( m1_pre_topc(k1_tex_2('#skF_2',B_98),'#skF_2')
      | ~ m1_subset_1(B_98,k1_tarski('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_400])).

tff(c_406,plain,(
    m1_pre_topc(k1_tex_2('#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_311,c_402])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_414,c_406])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:13:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.54/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.32  
% 2.54/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.33  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k1_enumset1 > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 2.54/1.33  
% 2.54/1.33  %Foreground sorts:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Background operators:
% 2.54/1.33  
% 2.54/1.33  
% 2.54/1.33  %Foreground operators:
% 2.54/1.33  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.54/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.54/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.54/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.54/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.54/1.33  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 2.54/1.33  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.54/1.33  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.54/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.54/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.54/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.54/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.54/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.54/1.33  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.54/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.54/1.33  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.54/1.33  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 2.54/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.54/1.33  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.54/1.33  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.54/1.33  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.54/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.54/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.54/1.33  
% 2.54/1.35  tff(f_177, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 2.54/1.35  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.54/1.35  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.54/1.35  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.54/1.35  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.54/1.35  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.54/1.35  tff(f_123, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.54/1.35  tff(f_151, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 2.54/1.35  tff(f_137, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 2.54/1.35  tff(f_116, axiom, (![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v1_tex_2(B, A)) => (~v2_struct_0(B) & ~v7_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc13_tex_2)).
% 2.54/1.35  tff(f_164, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 2.54/1.35  tff(f_37, axiom, (![A]: v1_zfmisc_1(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_zfmisc_1)).
% 2.54/1.35  tff(f_67, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.54/1.35  tff(f_93, axiom, (![A]: (((~v2_struct_0(A) & v7_struct_0(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (~v2_struct_0(B) => (~v2_struct_0(B) & ~v1_tex_2(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc10_tex_2)).
% 2.54/1.35  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.54/1.35  tff(c_52, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.54/1.35  tff(c_16, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.54/1.35  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.54/1.35  tff(c_248, plain, (![A_83, B_84]: (k6_domain_1(A_83, B_84)=k1_tarski(B_84) | ~m1_subset_1(B_84, A_83) | v1_xboole_0(A_83))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.54/1.35  tff(c_256, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_248])).
% 2.54/1.35  tff(c_257, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_256])).
% 2.54/1.35  tff(c_18, plain, (![A_14]: (~v1_xboole_0(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.54/1.35  tff(c_260, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_257, c_18])).
% 2.54/1.35  tff(c_263, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_260])).
% 2.54/1.35  tff(c_266, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_263])).
% 2.54/1.35  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_266])).
% 2.54/1.35  tff(c_272, plain, (~v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_256])).
% 2.54/1.35  tff(c_14, plain, (![A_11, B_12]: (r2_hidden(A_11, B_12) | v1_xboole_0(B_12) | ~m1_subset_1(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.54/1.35  tff(c_12, plain, (![A_9, B_10]: (m1_subset_1(k1_tarski(A_9), k1_zfmisc_1(B_10)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.35  tff(c_240, plain, (![B_80, A_81]: (v1_subset_1(B_80, A_81) | B_80=A_81 | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.54/1.35  tff(c_286, plain, (![A_87, B_88]: (v1_subset_1(k1_tarski(A_87), B_88) | k1_tarski(A_87)=B_88 | ~r2_hidden(A_87, B_88))), inference(resolution, [status(thm)], [c_12, c_240])).
% 2.54/1.35  tff(c_271, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_256])).
% 2.54/1.35  tff(c_110, plain, (![A_52, B_53]: (k6_domain_1(A_52, B_53)=k1_tarski(B_53) | ~m1_subset_1(B_53, A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.54/1.35  tff(c_118, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_50, c_110])).
% 2.54/1.35  tff(c_121, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_118])).
% 2.54/1.35  tff(c_124, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_121, c_18])).
% 2.54/1.35  tff(c_127, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_124])).
% 2.54/1.35  tff(c_130, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_127])).
% 2.54/1.35  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_130])).
% 2.54/1.35  tff(c_135, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_118])).
% 2.54/1.35  tff(c_62, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.54/1.35  tff(c_81, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_62])).
% 2.54/1.35  tff(c_137, plain, (v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_81])).
% 2.54/1.35  tff(c_157, plain, (![A_58, B_59]: (~v2_struct_0(k1_tex_2(A_58, B_59)) | ~m1_subset_1(B_59, u1_struct_0(A_58)) | ~l1_pre_topc(A_58) | v2_struct_0(A_58))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.54/1.35  tff(c_160, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_157])).
% 2.54/1.35  tff(c_163, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_160])).
% 2.54/1.35  tff(c_164, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_163])).
% 2.54/1.35  tff(c_173, plain, (![A_62, B_63]: (m1_pre_topc(k1_tex_2(A_62, B_63), A_62) | ~m1_subset_1(B_63, u1_struct_0(A_62)) | ~l1_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.54/1.35  tff(c_175, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_173])).
% 2.54/1.35  tff(c_178, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_175])).
% 2.54/1.35  tff(c_179, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_178])).
% 2.54/1.35  tff(c_165, plain, (![A_60, B_61]: (v7_struct_0(k1_tex_2(A_60, B_61)) | ~m1_subset_1(B_61, u1_struct_0(A_60)) | ~l1_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.54/1.35  tff(c_168, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_165])).
% 2.54/1.35  tff(c_171, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_168])).
% 2.54/1.35  tff(c_172, plain, (v7_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_54, c_171])).
% 2.54/1.35  tff(c_190, plain, (![B_68, A_69]: (~v7_struct_0(B_68) | v1_tex_2(B_68, A_69) | v2_struct_0(B_68) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69) | v7_struct_0(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.54/1.35  tff(c_56, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2')) | ~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_177])).
% 2.54/1.35  tff(c_120, plain, (~v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_81, c_56])).
% 2.54/1.35  tff(c_196, plain, (~v7_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_190, c_120])).
% 2.54/1.35  tff(c_200, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_179, c_172, c_196])).
% 2.54/1.35  tff(c_201, plain, (v7_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_164, c_200])).
% 2.54/1.35  tff(c_202, plain, (![A_70, B_71]: (~v7_struct_0(A_70) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_70), B_71), u1_struct_0(A_70)) | ~m1_subset_1(B_71, u1_struct_0(A_70)) | ~l1_struct_0(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_164])).
% 2.54/1.35  tff(c_205, plain, (~v7_struct_0('#skF_2') | ~v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_135, c_202])).
% 2.54/1.35  tff(c_207, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_137, c_201, c_205])).
% 2.54/1.35  tff(c_208, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_207])).
% 2.54/1.35  tff(c_211, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_208])).
% 2.54/1.35  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_211])).
% 2.54/1.35  tff(c_217, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_62])).
% 2.54/1.35  tff(c_281, plain, (~v1_subset_1(k1_tarski('#skF_3'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_271, c_217])).
% 2.54/1.35  tff(c_294, plain, (u1_struct_0('#skF_2')=k1_tarski('#skF_3') | ~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_286, c_281])).
% 2.54/1.35  tff(c_297, plain, (~r2_hidden('#skF_3', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_294])).
% 2.54/1.35  tff(c_300, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_14, c_297])).
% 2.54/1.35  tff(c_303, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_300])).
% 2.54/1.35  tff(c_305, plain, $false, inference(negUnitSimplification, [status(thm)], [c_272, c_303])).
% 2.54/1.35  tff(c_306, plain, (u1_struct_0('#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_294])).
% 2.54/1.35  tff(c_311, plain, (m1_subset_1('#skF_3', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_50])).
% 2.54/1.35  tff(c_331, plain, (![A_89, B_90]: (~v2_struct_0(k1_tex_2(A_89, B_90)) | ~m1_subset_1(B_90, u1_struct_0(A_89)) | ~l1_pre_topc(A_89) | v2_struct_0(A_89))), inference(cnfTransformation, [status(thm)], [f_151])).
% 2.54/1.35  tff(c_334, plain, (![B_90]: (~v2_struct_0(k1_tex_2('#skF_2', B_90)) | ~m1_subset_1(B_90, k1_tarski('#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_306, c_331])).
% 2.54/1.35  tff(c_336, plain, (![B_90]: (~v2_struct_0(k1_tex_2('#skF_2', B_90)) | ~m1_subset_1(B_90, k1_tarski('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_334])).
% 2.54/1.35  tff(c_391, plain, (![B_95]: (~v2_struct_0(k1_tex_2('#skF_2', B_95)) | ~m1_subset_1(B_95, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_336])).
% 2.54/1.35  tff(c_395, plain, (~v2_struct_0(k1_tex_2('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_311, c_391])).
% 2.54/1.35  tff(c_10, plain, (![A_8]: (v1_zfmisc_1(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.54/1.35  tff(c_20, plain, (![A_15]: (~v1_zfmisc_1(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v7_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.54/1.35  tff(c_318, plain, (~v1_zfmisc_1(k1_tarski('#skF_3')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_306, c_20])).
% 2.54/1.35  tff(c_328, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_318])).
% 2.54/1.35  tff(c_349, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_328])).
% 2.54/1.35  tff(c_352, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_16, c_349])).
% 2.54/1.35  tff(c_356, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_352])).
% 2.54/1.35  tff(c_357, plain, (v7_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_328])).
% 2.54/1.35  tff(c_216, plain, (v1_tex_2(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 2.54/1.35  tff(c_407, plain, (![B_99, A_100]: (~v1_tex_2(B_99, A_100) | v2_struct_0(B_99) | ~m1_pre_topc(B_99, A_100) | ~l1_pre_topc(A_100) | ~v7_struct_0(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.54/1.35  tff(c_410, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | ~l1_pre_topc('#skF_2') | ~v7_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_216, c_407])).
% 2.54/1.35  tff(c_413, plain, (v2_struct_0(k1_tex_2('#skF_2', '#skF_3')) | ~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_357, c_52, c_410])).
% 2.54/1.35  tff(c_414, plain, (~m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_54, c_395, c_413])).
% 2.54/1.35  tff(c_396, plain, (![A_96, B_97]: (m1_pre_topc(k1_tex_2(A_96, B_97), A_96) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_pre_topc(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.54/1.35  tff(c_398, plain, (![B_97]: (m1_pre_topc(k1_tex_2('#skF_2', B_97), '#skF_2') | ~m1_subset_1(B_97, k1_tarski('#skF_3')) | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_306, c_396])).
% 2.54/1.35  tff(c_400, plain, (![B_97]: (m1_pre_topc(k1_tex_2('#skF_2', B_97), '#skF_2') | ~m1_subset_1(B_97, k1_tarski('#skF_3')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_398])).
% 2.54/1.35  tff(c_402, plain, (![B_98]: (m1_pre_topc(k1_tex_2('#skF_2', B_98), '#skF_2') | ~m1_subset_1(B_98, k1_tarski('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_54, c_400])).
% 2.54/1.35  tff(c_406, plain, (m1_pre_topc(k1_tex_2('#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_311, c_402])).
% 2.54/1.35  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_414, c_406])).
% 2.54/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.54/1.35  
% 2.54/1.35  Inference rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Ref     : 0
% 2.54/1.35  #Sup     : 59
% 2.54/1.35  #Fact    : 0
% 2.54/1.35  #Define  : 0
% 2.54/1.35  #Split   : 5
% 2.54/1.35  #Chain   : 0
% 2.54/1.35  #Close   : 0
% 2.54/1.35  
% 2.54/1.35  Ordering : KBO
% 2.54/1.35  
% 2.54/1.35  Simplification rules
% 2.54/1.35  ----------------------
% 2.54/1.35  #Subsume      : 6
% 2.54/1.35  #Demod        : 36
% 2.54/1.35  #Tautology    : 29
% 2.54/1.35  #SimpNegUnit  : 18
% 2.54/1.35  #BackRed      : 6
% 2.54/1.35  
% 2.54/1.35  #Partial instantiations: 0
% 2.54/1.35  #Strategies tried      : 1
% 2.54/1.35  
% 2.54/1.35  Timing (in seconds)
% 2.54/1.35  ----------------------
% 2.54/1.35  Preprocessing        : 0.34
% 2.54/1.35  Parsing              : 0.18
% 2.54/1.35  CNF conversion       : 0.02
% 2.54/1.35  Main loop            : 0.24
% 2.54/1.35  Inferencing          : 0.09
% 2.54/1.35  Reduction            : 0.07
% 2.54/1.35  Demodulation         : 0.05
% 2.54/1.35  BG Simplification    : 0.02
% 2.54/1.35  Subsumption          : 0.03
% 2.54/1.35  Abstraction          : 0.01
% 2.54/1.35  MUC search           : 0.00
% 2.54/1.35  Cooper               : 0.00
% 2.54/1.35  Total                : 0.62
% 2.54/1.35  Index Insertion      : 0.00
% 2.54/1.35  Index Deletion       : 0.00
% 2.54/1.35  Index Matching       : 0.00
% 2.54/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
