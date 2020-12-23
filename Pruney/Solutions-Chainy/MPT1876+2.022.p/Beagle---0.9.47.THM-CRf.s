%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:53 EST 2020

% Result     : Theorem 5.32s
% Output     : CNFRefutation 5.44s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 224 expanded)
%              Number of leaves         :   42 (  97 expanded)
%              Depth                    :   12
%              Number of atoms          :  280 ( 783 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

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

tff(f_190,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_34,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_129,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_170,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_158,axiom,(
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

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v2_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( ( ~ v2_struct_0(B)
              & ~ v7_struct_0(B) )
           => ( ~ v2_struct_0(B)
              & ~ v1_tdlat_3(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

tff(c_52,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_66,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_69,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( ~ v1_zfmisc_1('#skF_4')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_72,plain,(
    ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_60])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_159,plain,(
    ! [A_67,C_68,B_69] :
      ( m1_subset_1(A_67,C_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(C_68))
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169,plain,(
    ! [A_67] :
      ( m1_subset_1(A_67,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_159])).

tff(c_85,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(A_48,B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_89,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_85])).

tff(c_6,plain,(
    ! [A_5] : ~ v1_xboole_0(k1_tarski(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_135,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_146,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_89,c_135])).

tff(c_202,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(k6_domain_1(A_75,B_76),k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_76,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_244,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k6_domain_1(A_79,B_80),A_79)
      | ~ m1_subset_1(B_80,A_79)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_202,c_12])).

tff(c_410,plain,(
    ! [A_100] :
      ( r1_tarski(k1_tarski('#skF_1'(A_100)),A_100)
      | ~ m1_subset_1('#skF_1'(A_100),A_100)
      | v1_xboole_0(A_100)
      | v1_xboole_0(A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_244])).

tff(c_34,plain,(
    ! [B_31,A_29] :
      ( B_31 = A_29
      | ~ r1_tarski(A_29,B_31)
      | ~ v1_zfmisc_1(B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_417,plain,(
    ! [A_100] :
      ( k1_tarski('#skF_1'(A_100)) = A_100
      | ~ v1_zfmisc_1(A_100)
      | v1_xboole_0(k1_tarski('#skF_1'(A_100)))
      | ~ m1_subset_1('#skF_1'(A_100),A_100)
      | v1_xboole_0(A_100) ) ),
    inference(resolution,[status(thm)],[c_410,c_34])).

tff(c_431,plain,(
    ! [A_103] :
      ( k1_tarski('#skF_1'(A_103)) = A_103
      | ~ v1_zfmisc_1(A_103)
      | ~ m1_subset_1('#skF_1'(A_103),A_103)
      | v1_xboole_0(A_103) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_417])).

tff(c_452,plain,(
    ! [A_104] :
      ( k1_tarski('#skF_1'(A_104)) = A_104
      | ~ v1_zfmisc_1(A_104)
      | v1_xboole_0(A_104) ) ),
    inference(resolution,[status(thm)],[c_89,c_431])).

tff(c_108,plain,(
    ! [B_58,A_59] :
      ( v1_xboole_0(B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59))
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_108])).

tff(c_123,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_118])).

tff(c_170,plain,(
    ! [A_70] :
      ( m1_subset_1(A_70,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_48,c_159])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k6_domain_1(A_23,B_24) = k1_tarski(B_24)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_173,plain,(
    ! [A_70] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_70) = k1_tarski(A_70)
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_170,c_26])).

tff(c_176,plain,(
    ! [A_70] :
      ( k6_domain_1(u1_struct_0('#skF_3'),A_70) = k1_tarski(A_70)
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_173])).

tff(c_298,plain,(
    ! [A_86,B_87] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_86),B_87),A_86)
      | ~ m1_subset_1(B_87,u1_struct_0(A_86))
      | ~ l1_pre_topc(A_86)
      | ~ v2_pre_topc(A_86)
      | v2_struct_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_301,plain,(
    ! [A_70] :
      ( v2_tex_2(k1_tarski(A_70),'#skF_3')
      | ~ m1_subset_1(A_70,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_298])).

tff(c_307,plain,(
    ! [A_70] :
      ( v2_tex_2(k1_tarski(A_70),'#skF_3')
      | ~ m1_subset_1(A_70,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3')
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_301])).

tff(c_308,plain,(
    ! [A_70] :
      ( v2_tex_2(k1_tarski(A_70),'#skF_3')
      | ~ m1_subset_1(A_70,u1_struct_0('#skF_3'))
      | ~ r2_hidden(A_70,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_307])).

tff(c_1204,plain,(
    ! [A_147] :
      ( v2_tex_2(A_147,'#skF_3')
      | ~ m1_subset_1('#skF_1'(A_147),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_1'(A_147),'#skF_4')
      | ~ v1_zfmisc_1(A_147)
      | v1_xboole_0(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_308])).

tff(c_1250,plain,(
    ! [A_148] :
      ( v2_tex_2(A_148,'#skF_3')
      | ~ v1_zfmisc_1(A_148)
      | v1_xboole_0(A_148)
      | ~ r2_hidden('#skF_1'(A_148),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_169,c_1204])).

tff(c_1254,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1250])).

tff(c_1257,plain,
    ( v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_1254])).

tff(c_1259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_72,c_1257])).

tff(c_1260,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2422,plain,(
    ! [A_253,B_254] :
      ( m1_pre_topc('#skF_2'(A_253,B_254),A_253)
      | ~ v2_tex_2(B_254,A_253)
      | ~ m1_subset_1(B_254,k1_zfmisc_1(u1_struct_0(A_253)))
      | v1_xboole_0(B_254)
      | ~ l1_pre_topc(A_253)
      | ~ v2_pre_topc(A_253)
      | v2_struct_0(A_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2456,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2422])).

tff(c_2475,plain,
    ( m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1260,c_2456])).

tff(c_2476,plain,(
    m1_pre_topc('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_2475])).

tff(c_20,plain,(
    ! [B_19,A_17] :
      ( l1_pre_topc(B_19)
      | ~ m1_pre_topc(B_19,A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2482,plain,
    ( l1_pre_topc('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_2476,c_20])).

tff(c_2489,plain,(
    l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2482])).

tff(c_18,plain,(
    ! [A_16] :
      ( l1_struct_0(A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1261,plain,(
    ~ v1_zfmisc_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_2234,plain,(
    ! [A_244,B_245] :
      ( ~ v2_struct_0('#skF_2'(A_244,B_245))
      | ~ v2_tex_2(B_245,A_244)
      | ~ m1_subset_1(B_245,k1_zfmisc_1(u1_struct_0(A_244)))
      | v1_xboole_0(B_245)
      | ~ l1_pre_topc(A_244)
      | ~ v2_pre_topc(A_244)
      | v2_struct_0(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2280,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2234])).

tff(c_2299,plain,
    ( ~ v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1260,c_2280])).

tff(c_2300,plain,(
    ~ v2_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_2299])).

tff(c_54,plain,(
    v2_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_1816,plain,(
    ! [A_224,B_225] :
      ( v1_tdlat_3('#skF_2'(A_224,B_225))
      | ~ v2_tex_2(B_225,A_224)
      | ~ m1_subset_1(B_225,k1_zfmisc_1(u1_struct_0(A_224)))
      | v1_xboole_0(B_225)
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_1854,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_1816])).

tff(c_1871,plain,
    ( v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1260,c_1854])).

tff(c_1872,plain,(
    v1_tdlat_3('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_1871])).

tff(c_30,plain,(
    ! [B_28,A_26] :
      ( ~ v1_tdlat_3(B_28)
      | v7_struct_0(B_28)
      | v2_struct_0(B_28)
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_tdlat_3(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2479,plain,
    ( ~ v1_tdlat_3('#skF_2'('#skF_3','#skF_4'))
    | v7_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_2476,c_30])).

tff(c_2485,plain,
    ( v7_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_2'('#skF_3','#skF_4'))
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1872,c_2479])).

tff(c_2486,plain,(
    v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2300,c_2485])).

tff(c_2565,plain,(
    ! [A_259,B_260] :
      ( u1_struct_0('#skF_2'(A_259,B_260)) = B_260
      | ~ v2_tex_2(B_260,A_259)
      | ~ m1_subset_1(B_260,k1_zfmisc_1(u1_struct_0(A_259)))
      | v1_xboole_0(B_260)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259)
      | v2_struct_0(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_2611,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | ~ v2_tex_2('#skF_4','#skF_3')
    | v1_xboole_0('#skF_4')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_2565])).

tff(c_2630,plain,
    ( u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52,c_1260,c_2611])).

tff(c_2631,plain,(
    u1_struct_0('#skF_2'('#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_50,c_2630])).

tff(c_22,plain,(
    ! [A_20] :
      ( v1_zfmisc_1(u1_struct_0(A_20))
      | ~ l1_struct_0(A_20)
      | ~ v7_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2652,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4'))
    | ~ v7_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2631,c_22])).

tff(c_2674,plain,
    ( v1_zfmisc_1('#skF_4')
    | ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2486,c_2652])).

tff(c_2675,plain,(
    ~ l1_struct_0('#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_1261,c_2674])).

tff(c_2679,plain,(
    ~ l1_pre_topc('#skF_2'('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_2675])).

tff(c_2683,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2489,c_2679])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:58:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.32/2.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.13  
% 5.32/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/2.13  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 5.32/2.13  
% 5.32/2.13  %Foreground sorts:
% 5.32/2.13  
% 5.32/2.13  
% 5.32/2.13  %Background operators:
% 5.32/2.13  
% 5.32/2.13  
% 5.32/2.13  %Foreground operators:
% 5.32/2.13  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.32/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.32/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.32/2.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.32/2.13  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 5.32/2.13  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.32/2.13  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 5.32/2.13  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 5.32/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.32/2.13  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 5.32/2.13  tff('#skF_3', type, '#skF_3': $i).
% 5.32/2.13  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.32/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.32/2.13  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.32/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/2.13  tff('#skF_4', type, '#skF_4': $i).
% 5.32/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.32/2.13  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 5.32/2.13  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.32/2.13  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.32/2.13  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.32/2.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.32/2.13  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 5.32/2.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/2.13  
% 5.44/2.15  tff(f_190, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tex_2)).
% 5.44/2.15  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.44/2.15  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.44/2.15  tff(f_45, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 5.44/2.15  tff(f_34, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 5.44/2.15  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 5.44/2.15  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 5.44/2.15  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.44/2.15  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 5.44/2.15  tff(f_41, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.44/2.15  tff(f_170, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tex_2)).
% 5.44/2.15  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => ~(v2_tex_2(B, A) & (![C]: ((((~v2_struct_0(C) & v1_pre_topc(C)) & v1_tdlat_3(C)) & m1_pre_topc(C, A)) => ~(B = u1_struct_0(C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tex_2)).
% 5.44/2.15  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.44/2.15  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.44/2.15  tff(f_116, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc32_tex_2)).
% 5.44/2.15  tff(f_72, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_struct_0)).
% 5.44/2.15  tff(c_52, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.44/2.15  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.44/2.15  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.44/2.15  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.44/2.15  tff(c_66, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.44/2.15  tff(c_69, plain, (v1_zfmisc_1('#skF_4')), inference(splitLeft, [status(thm)], [c_66])).
% 5.44/2.15  tff(c_60, plain, (~v1_zfmisc_1('#skF_4') | ~v2_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.44/2.15  tff(c_72, plain, (~v2_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_60])).
% 5.44/2.15  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.44/2.15  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.44/2.15  tff(c_159, plain, (![A_67, C_68, B_69]: (m1_subset_1(A_67, C_68) | ~m1_subset_1(B_69, k1_zfmisc_1(C_68)) | ~r2_hidden(A_67, B_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.44/2.15  tff(c_169, plain, (![A_67]: (m1_subset_1(A_67, u1_struct_0('#skF_3')) | ~r2_hidden(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_159])).
% 5.44/2.15  tff(c_85, plain, (![A_48, B_49]: (m1_subset_1(A_48, B_49) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.44/2.15  tff(c_89, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_85])).
% 5.44/2.15  tff(c_6, plain, (![A_5]: (~v1_xboole_0(k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.44/2.15  tff(c_135, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.44/2.15  tff(c_146, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_89, c_135])).
% 5.44/2.15  tff(c_202, plain, (![A_75, B_76]: (m1_subset_1(k6_domain_1(A_75, B_76), k1_zfmisc_1(A_75)) | ~m1_subset_1(B_76, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.44/2.15  tff(c_12, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.44/2.15  tff(c_244, plain, (![A_79, B_80]: (r1_tarski(k6_domain_1(A_79, B_80), A_79) | ~m1_subset_1(B_80, A_79) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_202, c_12])).
% 5.44/2.15  tff(c_410, plain, (![A_100]: (r1_tarski(k1_tarski('#skF_1'(A_100)), A_100) | ~m1_subset_1('#skF_1'(A_100), A_100) | v1_xboole_0(A_100) | v1_xboole_0(A_100))), inference(superposition, [status(thm), theory('equality')], [c_146, c_244])).
% 5.44/2.15  tff(c_34, plain, (![B_31, A_29]: (B_31=A_29 | ~r1_tarski(A_29, B_31) | ~v1_zfmisc_1(B_31) | v1_xboole_0(B_31) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.44/2.15  tff(c_417, plain, (![A_100]: (k1_tarski('#skF_1'(A_100))=A_100 | ~v1_zfmisc_1(A_100) | v1_xboole_0(k1_tarski('#skF_1'(A_100))) | ~m1_subset_1('#skF_1'(A_100), A_100) | v1_xboole_0(A_100))), inference(resolution, [status(thm)], [c_410, c_34])).
% 5.44/2.15  tff(c_431, plain, (![A_103]: (k1_tarski('#skF_1'(A_103))=A_103 | ~v1_zfmisc_1(A_103) | ~m1_subset_1('#skF_1'(A_103), A_103) | v1_xboole_0(A_103))), inference(negUnitSimplification, [status(thm)], [c_6, c_417])).
% 5.44/2.15  tff(c_452, plain, (![A_104]: (k1_tarski('#skF_1'(A_104))=A_104 | ~v1_zfmisc_1(A_104) | v1_xboole_0(A_104))), inference(resolution, [status(thm)], [c_89, c_431])).
% 5.44/2.15  tff(c_108, plain, (![B_58, A_59]: (v1_xboole_0(B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)) | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.44/2.15  tff(c_118, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_48, c_108])).
% 5.44/2.15  tff(c_123, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_50, c_118])).
% 5.44/2.15  tff(c_170, plain, (![A_70]: (m1_subset_1(A_70, u1_struct_0('#skF_3')) | ~r2_hidden(A_70, '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_159])).
% 5.44/2.15  tff(c_26, plain, (![A_23, B_24]: (k6_domain_1(A_23, B_24)=k1_tarski(B_24) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.44/2.15  tff(c_173, plain, (![A_70]: (k6_domain_1(u1_struct_0('#skF_3'), A_70)=k1_tarski(A_70) | v1_xboole_0(u1_struct_0('#skF_3')) | ~r2_hidden(A_70, '#skF_4'))), inference(resolution, [status(thm)], [c_170, c_26])).
% 5.44/2.15  tff(c_176, plain, (![A_70]: (k6_domain_1(u1_struct_0('#skF_3'), A_70)=k1_tarski(A_70) | ~r2_hidden(A_70, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_123, c_173])).
% 5.44/2.15  tff(c_298, plain, (![A_86, B_87]: (v2_tex_2(k6_domain_1(u1_struct_0(A_86), B_87), A_86) | ~m1_subset_1(B_87, u1_struct_0(A_86)) | ~l1_pre_topc(A_86) | ~v2_pre_topc(A_86) | v2_struct_0(A_86))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.44/2.15  tff(c_301, plain, (![A_70]: (v2_tex_2(k1_tarski(A_70), '#skF_3') | ~m1_subset_1(A_70, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~r2_hidden(A_70, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_298])).
% 5.44/2.15  tff(c_307, plain, (![A_70]: (v2_tex_2(k1_tarski(A_70), '#skF_3') | ~m1_subset_1(A_70, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | ~r2_hidden(A_70, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_301])).
% 5.44/2.15  tff(c_308, plain, (![A_70]: (v2_tex_2(k1_tarski(A_70), '#skF_3') | ~m1_subset_1(A_70, u1_struct_0('#skF_3')) | ~r2_hidden(A_70, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_307])).
% 5.44/2.15  tff(c_1204, plain, (![A_147]: (v2_tex_2(A_147, '#skF_3') | ~m1_subset_1('#skF_1'(A_147), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_1'(A_147), '#skF_4') | ~v1_zfmisc_1(A_147) | v1_xboole_0(A_147))), inference(superposition, [status(thm), theory('equality')], [c_452, c_308])).
% 5.44/2.15  tff(c_1250, plain, (![A_148]: (v2_tex_2(A_148, '#skF_3') | ~v1_zfmisc_1(A_148) | v1_xboole_0(A_148) | ~r2_hidden('#skF_1'(A_148), '#skF_4'))), inference(resolution, [status(thm)], [c_169, c_1204])).
% 5.44/2.15  tff(c_1254, plain, (v2_tex_2('#skF_4', '#skF_3') | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1250])).
% 5.44/2.15  tff(c_1257, plain, (v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_69, c_1254])).
% 5.44/2.15  tff(c_1259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_72, c_1257])).
% 5.44/2.15  tff(c_1260, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_66])).
% 5.44/2.15  tff(c_2422, plain, (![A_253, B_254]: (m1_pre_topc('#skF_2'(A_253, B_254), A_253) | ~v2_tex_2(B_254, A_253) | ~m1_subset_1(B_254, k1_zfmisc_1(u1_struct_0(A_253))) | v1_xboole_0(B_254) | ~l1_pre_topc(A_253) | ~v2_pre_topc(A_253) | v2_struct_0(A_253))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.44/2.15  tff(c_2456, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2422])).
% 5.44/2.15  tff(c_2475, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1260, c_2456])).
% 5.44/2.15  tff(c_2476, plain, (m1_pre_topc('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_2475])).
% 5.44/2.15  tff(c_20, plain, (![B_19, A_17]: (l1_pre_topc(B_19) | ~m1_pre_topc(B_19, A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.44/2.15  tff(c_2482, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_2476, c_20])).
% 5.44/2.15  tff(c_2489, plain, (l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2482])).
% 5.44/2.15  tff(c_18, plain, (![A_16]: (l1_struct_0(A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.44/2.15  tff(c_1261, plain, (~v1_zfmisc_1('#skF_4')), inference(splitRight, [status(thm)], [c_66])).
% 5.44/2.15  tff(c_2234, plain, (![A_244, B_245]: (~v2_struct_0('#skF_2'(A_244, B_245)) | ~v2_tex_2(B_245, A_244) | ~m1_subset_1(B_245, k1_zfmisc_1(u1_struct_0(A_244))) | v1_xboole_0(B_245) | ~l1_pre_topc(A_244) | ~v2_pre_topc(A_244) | v2_struct_0(A_244))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.44/2.15  tff(c_2280, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2234])).
% 5.44/2.15  tff(c_2299, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1260, c_2280])).
% 5.44/2.15  tff(c_2300, plain, (~v2_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_2299])).
% 5.44/2.15  tff(c_54, plain, (v2_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_190])).
% 5.44/2.15  tff(c_1816, plain, (![A_224, B_225]: (v1_tdlat_3('#skF_2'(A_224, B_225)) | ~v2_tex_2(B_225, A_224) | ~m1_subset_1(B_225, k1_zfmisc_1(u1_struct_0(A_224))) | v1_xboole_0(B_225) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.44/2.15  tff(c_1854, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_1816])).
% 5.44/2.15  tff(c_1871, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1260, c_1854])).
% 5.44/2.15  tff(c_1872, plain, (v1_tdlat_3('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_1871])).
% 5.44/2.15  tff(c_30, plain, (![B_28, A_26]: (~v1_tdlat_3(B_28) | v7_struct_0(B_28) | v2_struct_0(B_28) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26) | ~v2_tdlat_3(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.44/2.15  tff(c_2479, plain, (~v1_tdlat_3('#skF_2'('#skF_3', '#skF_4')) | v7_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~l1_pre_topc('#skF_3') | ~v2_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_2476, c_30])).
% 5.44/2.15  tff(c_2485, plain, (v7_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_2'('#skF_3', '#skF_4')) | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1872, c_2479])).
% 5.44/2.15  tff(c_2486, plain, (v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_58, c_2300, c_2485])).
% 5.44/2.15  tff(c_2565, plain, (![A_259, B_260]: (u1_struct_0('#skF_2'(A_259, B_260))=B_260 | ~v2_tex_2(B_260, A_259) | ~m1_subset_1(B_260, k1_zfmisc_1(u1_struct_0(A_259))) | v1_xboole_0(B_260) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259) | v2_struct_0(A_259))), inference(cnfTransformation, [status(thm)], [f_158])).
% 5.44/2.15  tff(c_2611, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | ~v2_tex_2('#skF_4', '#skF_3') | v1_xboole_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_2565])).
% 5.44/2.15  tff(c_2630, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4' | v1_xboole_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52, c_1260, c_2611])).
% 5.44/2.15  tff(c_2631, plain, (u1_struct_0('#skF_2'('#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_50, c_2630])).
% 5.44/2.15  tff(c_22, plain, (![A_20]: (v1_zfmisc_1(u1_struct_0(A_20)) | ~l1_struct_0(A_20) | ~v7_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.44/2.15  tff(c_2652, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4')) | ~v7_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2631, c_22])).
% 5.44/2.15  tff(c_2674, plain, (v1_zfmisc_1('#skF_4') | ~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2486, c_2652])).
% 5.44/2.15  tff(c_2675, plain, (~l1_struct_0('#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_1261, c_2674])).
% 5.44/2.15  tff(c_2679, plain, (~l1_pre_topc('#skF_2'('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_2675])).
% 5.44/2.15  tff(c_2683, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2489, c_2679])).
% 5.44/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.44/2.15  
% 5.44/2.15  Inference rules
% 5.44/2.15  ----------------------
% 5.44/2.15  #Ref     : 0
% 5.44/2.15  #Sup     : 538
% 5.44/2.15  #Fact    : 0
% 5.44/2.15  #Define  : 0
% 5.44/2.15  #Split   : 7
% 5.44/2.15  #Chain   : 0
% 5.44/2.15  #Close   : 0
% 5.44/2.15  
% 5.44/2.15  Ordering : KBO
% 5.44/2.15  
% 5.44/2.15  Simplification rules
% 5.44/2.15  ----------------------
% 5.44/2.15  #Subsume      : 106
% 5.44/2.15  #Demod        : 71
% 5.44/2.15  #Tautology    : 89
% 5.44/2.15  #SimpNegUnit  : 115
% 5.44/2.15  #BackRed      : 0
% 5.44/2.15  
% 5.44/2.15  #Partial instantiations: 0
% 5.44/2.15  #Strategies tried      : 1
% 5.44/2.15  
% 5.44/2.15  Timing (in seconds)
% 5.44/2.15  ----------------------
% 5.44/2.16  Preprocessing        : 0.55
% 5.44/2.16  Parsing              : 0.29
% 5.44/2.16  CNF conversion       : 0.04
% 5.44/2.16  Main loop            : 0.82
% 5.44/2.16  Inferencing          : 0.31
% 5.44/2.16  Reduction            : 0.22
% 5.44/2.16  Demodulation         : 0.14
% 5.44/2.16  BG Simplification    : 0.05
% 5.44/2.16  Subsumption          : 0.18
% 5.44/2.16  Abstraction          : 0.05
% 5.44/2.16  MUC search           : 0.00
% 5.44/2.16  Cooper               : 0.00
% 5.44/2.16  Total                : 1.41
% 5.44/2.16  Index Insertion      : 0.00
% 5.44/2.16  Index Deletion       : 0.00
% 5.44/2.16  Index Matching       : 0.00
% 5.44/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
