%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:54 EST 2020

% Result     : Theorem 6.60s
% Output     : CNFRefutation 6.66s
% Verified   : 
% Statistics : Number of formulae       :  211 (1542 expanded)
%              Number of leaves         :   45 ( 541 expanded)
%              Depth                    :   25
%              Number of atoms          :  521 (5615 expanded)
%              Number of equality atoms :   30 ( 222 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(v2_tdlat_3,type,(
    v2_tdlat_3: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_246,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_152,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_226,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_200,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_xboole_0(B)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

tff(f_186,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( B = u1_struct_0(A)
           => ( v2_tex_2(B,A)
            <=> v1_tdlat_3(A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tex_2)).

tff(f_131,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_212,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => v2_tex_2(k6_domain_1(u1_struct_0(A),B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_172,axiom,(
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

tff(f_121,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_3908,plain,(
    ! [A_326,B_327] :
      ( m1_pre_topc('#skF_3'(A_326,B_327),A_326)
      | ~ m1_subset_1(B_327,k1_zfmisc_1(u1_struct_0(A_326)))
      | v1_xboole_0(B_327)
      | ~ l1_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3922,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_3908])).

tff(c_3929,plain,
    ( m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3922])).

tff(c_3930,plain,(
    m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_74,c_3929])).

tff(c_30,plain,(
    ! [B_18,A_16] :
      ( l1_pre_topc(B_18)
      | ~ m1_pre_topc(B_18,A_16)
      | ~ l1_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3933,plain,
    ( l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_3930,c_30])).

tff(c_3936,plain,(
    l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3933])).

tff(c_28,plain,(
    ! [A_15] :
      ( l1_struct_0(A_15)
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3665,plain,(
    ! [A_308,B_309] :
      ( ~ v2_struct_0('#skF_3'(A_308,B_309))
      | ~ m1_subset_1(B_309,k1_zfmisc_1(u1_struct_0(A_308)))
      | v1_xboole_0(B_309)
      | ~ l1_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_3684,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_3665])).

tff(c_3691,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3684])).

tff(c_3692,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_74,c_3691])).

tff(c_90,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_94,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_90])).

tff(c_84,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_96,plain,(
    ~ v2_tex_2('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_84])).

tff(c_80,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_725,plain,(
    ! [B_140,A_141] :
      ( v2_tex_2(B_140,A_141)
      | ~ m1_subset_1(B_140,k1_zfmisc_1(u1_struct_0(A_141)))
      | ~ l1_pre_topc(A_141)
      | ~ v1_tdlat_3(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_748,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_725])).

tff(c_756,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_748])).

tff(c_757,plain,(
    ~ v1_tdlat_3('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_96,c_756])).

tff(c_107,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ m1_subset_1(A_64,k1_zfmisc_1(B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_107])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_193,plain,(
    ! [C_88,B_89,A_90] :
      ( r2_hidden(C_88,B_89)
      | ~ r2_hidden(C_88,A_90)
      | ~ r1_tarski(A_90,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_390,plain,(
    ! [B_114,B_115,A_116] :
      ( r2_hidden(B_114,B_115)
      | ~ r1_tarski(A_116,B_115)
      | ~ m1_subset_1(B_114,A_116)
      | v1_xboole_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_18,c_193])).

tff(c_398,plain,(
    ! [B_114] :
      ( r2_hidden(B_114,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_114,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_115,c_390])).

tff(c_408,plain,(
    ! [B_117] :
      ( r2_hidden(B_117,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_117,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_398])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( m1_subset_1(B_12,A_11)
      | ~ r2_hidden(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_419,plain,(
    ! [B_117] :
      ( m1_subset_1(B_117,u1_struct_0('#skF_4'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_117,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_408,c_16])).

tff(c_430,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_419])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_592,plain,(
    ! [B_129,A_130] :
      ( v2_tex_2(B_129,A_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(u1_struct_0(A_130)))
      | ~ v1_xboole_0(B_129)
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_2743,plain,(
    ! [A_225,A_226] :
      ( v2_tex_2(A_225,A_226)
      | ~ v1_xboole_0(A_225)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226)
      | ~ r1_tarski(A_225,u1_struct_0(A_226)) ) ),
    inference(resolution,[status(thm)],[c_26,c_592])).

tff(c_2801,plain,(
    ! [A_227] :
      ( v2_tex_2(u1_struct_0(A_227),A_227)
      | ~ v1_xboole_0(u1_struct_0(A_227))
      | ~ l1_pre_topc(A_227)
      | ~ v2_pre_topc(A_227)
      | v2_struct_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_12,c_2743])).

tff(c_1708,plain,(
    ! [A_183] :
      ( v1_tdlat_3(A_183)
      | ~ v2_tex_2(u1_struct_0(A_183),A_183)
      | ~ m1_subset_1(u1_struct_0(A_183),k1_zfmisc_1(u1_struct_0(A_183)))
      | ~ l1_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_1730,plain,(
    ! [A_183] :
      ( v1_tdlat_3(A_183)
      | ~ v2_tex_2(u1_struct_0(A_183),A_183)
      | ~ l1_pre_topc(A_183)
      | v2_struct_0(A_183)
      | ~ r1_tarski(u1_struct_0(A_183),u1_struct_0(A_183)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1708])).

tff(c_1744,plain,(
    ! [A_183] :
      ( v1_tdlat_3(A_183)
      | ~ v2_tex_2(u1_struct_0(A_183),A_183)
      | ~ l1_pre_topc(A_183)
      | v2_struct_0(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1730])).

tff(c_2815,plain,(
    ! [A_228] :
      ( v1_tdlat_3(A_228)
      | ~ v1_xboole_0(u1_struct_0(A_228))
      | ~ l1_pre_topc(A_228)
      | ~ v2_pre_topc(A_228)
      | v2_struct_0(A_228) ) ),
    inference(resolution,[status(thm)],[c_2801,c_1744])).

tff(c_2824,plain,
    ( v1_tdlat_3('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_430,c_2815])).

tff(c_2830,plain,
    ( v1_tdlat_3('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_2824])).

tff(c_2832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_757,c_2830])).

tff(c_2834,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_48,plain,(
    ! [A_27] :
      ( m1_subset_1('#skF_2'(A_27),A_27)
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2847,plain,(
    ! [B_230] :
      ( m1_subset_1(B_230,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_230,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_419])).

tff(c_34,plain,(
    ! [A_20,B_21] :
      ( k6_domain_1(A_20,B_21) = k1_tarski(B_21)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2857,plain,(
    ! [B_230] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_230) = k1_tarski(B_230)
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_230,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2847,c_34])).

tff(c_2868,plain,(
    ! [B_230] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_230) = k1_tarski(B_230)
      | ~ m1_subset_1(B_230,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2834,c_2857])).

tff(c_44,plain,(
    ! [A_27,B_30] :
      ( v1_zfmisc_1(A_27)
      | k6_domain_1(A_27,B_30) != A_27
      | ~ m1_subset_1(B_30,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2850,plain,(
    ! [B_230] :
      ( v1_zfmisc_1(u1_struct_0('#skF_4'))
      | k6_domain_1(u1_struct_0('#skF_4'),B_230) != u1_struct_0('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_230,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2847,c_44])).

tff(c_2863,plain,(
    ! [B_230] :
      ( v1_zfmisc_1(u1_struct_0('#skF_4'))
      | k6_domain_1(u1_struct_0('#skF_4'),B_230) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_230,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_2834,c_2850])).

tff(c_3065,plain,(
    ! [B_241] :
      ( k6_domain_1(u1_struct_0('#skF_4'),B_241) != u1_struct_0('#skF_4')
      | ~ m1_subset_1(B_241,'#skF_5') ) ),
    inference(splitLeft,[status(thm)],[c_2863])).

tff(c_3100,plain,(
    ! [B_244] :
      ( u1_struct_0('#skF_4') != k1_tarski(B_244)
      | ~ m1_subset_1(B_244,'#skF_5')
      | ~ m1_subset_1(B_244,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2868,c_3065])).

tff(c_3106,plain,
    ( k1_tarski('#skF_2'('#skF_5')) != u1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_5'),'#skF_5')
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_3100])).

tff(c_3115,plain,
    ( k1_tarski('#skF_2'('#skF_5')) != u1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_5'),'#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3106])).

tff(c_3116,plain,
    ( k1_tarski('#skF_2'('#skF_5')) != u1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3115])).

tff(c_3118,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3116])).

tff(c_3121,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_3118])).

tff(c_3127,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3121])).

tff(c_3129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3127])).

tff(c_3131,plain,(
    m1_subset_1('#skF_2'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_3116])).

tff(c_200,plain,(
    ! [A_91,C_92,B_93] :
      ( r1_tarski(A_91,C_92)
      | ~ r1_tarski(B_93,C_92)
      | ~ r1_tarski(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_205,plain,(
    ! [A_91] :
      ( r1_tarski(A_91,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_91,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_115,c_200])).

tff(c_403,plain,(
    ! [B_114,A_91] :
      ( r2_hidden(B_114,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_114,A_91)
      | v1_xboole_0(A_91)
      | ~ r1_tarski(A_91,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_205,c_390])).

tff(c_3146,plain,
    ( r2_hidden('#skF_2'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_3131,c_403])).

tff(c_3161,plain,
    ( r2_hidden('#skF_2'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_3146])).

tff(c_3162,plain,(
    r2_hidden('#skF_2'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3161])).

tff(c_3180,plain,
    ( m1_subset_1('#skF_2'('#skF_5'),u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3162,c_16])).

tff(c_3184,plain,(
    m1_subset_1('#skF_2'('#skF_5'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_2834,c_3180])).

tff(c_3152,plain,
    ( k6_domain_1('#skF_5','#skF_2'('#skF_5')) = k1_tarski('#skF_2'('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_3131,c_34])).

tff(c_3168,plain,(
    k6_domain_1('#skF_5','#skF_2'('#skF_5')) = k1_tarski('#skF_2'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3152])).

tff(c_46,plain,(
    ! [A_27] :
      ( k6_domain_1(A_27,'#skF_2'(A_27)) = A_27
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_3212,plain,
    ( k1_tarski('#skF_2'('#skF_5')) = '#skF_5'
    | ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3168,c_46])).

tff(c_3226,plain,
    ( k1_tarski('#skF_2'('#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_3212])).

tff(c_3227,plain,(
    k1_tarski('#skF_2'('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3226])).

tff(c_3192,plain,
    ( k6_domain_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5')) = k1_tarski('#skF_2'('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_3184,c_34])).

tff(c_3204,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5')) = k1_tarski('#skF_2'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_2834,c_3192])).

tff(c_3340,plain,(
    k6_domain_1(u1_struct_0('#skF_4'),'#skF_2'('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3227,c_3204])).

tff(c_3401,plain,(
    ! [A_255,B_256] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(A_255),B_256),A_255)
      | ~ m1_subset_1(B_256,u1_struct_0(A_255))
      | ~ l1_pre_topc(A_255)
      | ~ v2_pre_topc(A_255)
      | v2_struct_0(A_255) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_3404,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_5'),u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3340,c_3401])).

tff(c_3417,plain,
    ( v2_tex_2('#skF_5','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3184,c_3404])).

tff(c_3419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_96,c_3417])).

tff(c_3421,plain,(
    ~ v1_zfmisc_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_4686,plain,(
    ! [A_371,B_372] :
      ( u1_struct_0('#skF_3'(A_371,B_372)) = B_372
      | ~ m1_subset_1(B_372,k1_zfmisc_1(u1_struct_0(A_371)))
      | v1_xboole_0(B_372)
      | ~ l1_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_4712,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_4686])).

tff(c_4724,plain,
    ( u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5'
    | v1_xboole_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4712])).

tff(c_4725,plain,(
    u1_struct_0('#skF_3'('#skF_4','#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_74,c_4724])).

tff(c_32,plain,(
    ! [A_19] :
      ( v1_zfmisc_1(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | ~ v7_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4749,plain,
    ( v1_zfmisc_1('#skF_5')
    | ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_32])).

tff(c_4773,plain,
    ( ~ l1_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3421,c_4749])).

tff(c_4775,plain,(
    ~ v7_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4773])).

tff(c_78,plain,(
    v2_tdlat_3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_4026,plain,(
    ! [A_337] :
      ( v1_tdlat_3(A_337)
      | ~ v2_tex_2(u1_struct_0(A_337),A_337)
      | ~ m1_subset_1(u1_struct_0(A_337),k1_zfmisc_1(u1_struct_0(A_337)))
      | ~ l1_pre_topc(A_337)
      | v2_struct_0(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_4032,plain,(
    ! [A_337] :
      ( v1_tdlat_3(A_337)
      | ~ v2_tex_2(u1_struct_0(A_337),A_337)
      | ~ l1_pre_topc(A_337)
      | v2_struct_0(A_337)
      | ~ r1_tarski(u1_struct_0(A_337),u1_struct_0(A_337)) ) ),
    inference(resolution,[status(thm)],[c_26,c_4026])).

tff(c_4036,plain,(
    ! [A_337] :
      ( v1_tdlat_3(A_337)
      | ~ v2_tex_2(u1_struct_0(A_337),A_337)
      | ~ l1_pre_topc(A_337)
      | v2_struct_0(A_337) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4032])).

tff(c_4738,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_4036])).

tff(c_4762,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3936,c_4738])).

tff(c_4763,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2('#skF_5','#skF_3'('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3692,c_4762])).

tff(c_4808,plain,(
    ~ v2_tex_2('#skF_5','#skF_3'('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4763])).

tff(c_4857,plain,(
    ! [A_377] :
      ( v2_tex_2(u1_struct_0(A_377),A_377)
      | ~ v1_tdlat_3(A_377)
      | ~ m1_subset_1(u1_struct_0(A_377),k1_zfmisc_1(u1_struct_0(A_377)))
      | ~ l1_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_4866,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'('#skF_4','#skF_5')),'#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'('#skF_4','#skF_5'))))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_4857])).

tff(c_4881,plain,
    ( v2_tex_2('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3936,c_4725,c_4725,c_4866])).

tff(c_4882,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3692,c_4808,c_4881])).

tff(c_4894,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4882])).

tff(c_4900,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_4894])).

tff(c_4905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_4900])).

tff(c_4907,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4882])).

tff(c_4869,plain,
    ( v2_tex_2(u1_struct_0('#skF_3'('#skF_4','#skF_5')),'#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ m1_subset_1(u1_struct_0('#skF_3'('#skF_4','#skF_5')),k1_zfmisc_1('#skF_5'))
    | ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_4857])).

tff(c_4884,plain,
    ( v2_tex_2('#skF_5','#skF_3'('#skF_4','#skF_5'))
    | ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3936,c_4725,c_4725,c_4869])).

tff(c_4885,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_3692,c_4808,c_4884])).

tff(c_4959,plain,(
    ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4907,c_4885])).

tff(c_3420,plain,(
    v2_tex_2('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_90])).

tff(c_3444,plain,(
    ! [B_266,A_267] :
      ( v1_xboole_0(B_266)
      | ~ m1_subset_1(B_266,A_267)
      | ~ v1_xboole_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3450,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_72,c_3444])).

tff(c_3454,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3450])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3500,plain,(
    ! [B_279,A_280] :
      ( m1_subset_1(B_279,A_280)
      | ~ r2_hidden(B_279,A_280)
      | v1_xboole_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3583,plain,(
    ! [A_297,B_298] :
      ( m1_subset_1('#skF_1'(A_297,B_298),A_297)
      | v1_xboole_0(A_297)
      | r1_tarski(A_297,B_298) ) ),
    inference(resolution,[status(thm)],[c_6,c_3500])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4001,plain,(
    ! [B_335,B_336] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(B_335),B_336),B_335)
      | v1_xboole_0(k1_zfmisc_1(B_335))
      | r1_tarski(k1_zfmisc_1(B_335),B_336) ) ),
    inference(resolution,[status(thm)],[c_3583,c_24])).

tff(c_3434,plain,(
    ! [A_262,B_263] :
      ( r1_tarski(A_262,B_263)
      | ~ m1_subset_1(A_262,k1_zfmisc_1(B_263)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3442,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_3434])).

tff(c_3527,plain,(
    ! [A_289,C_290,B_291] :
      ( r1_tarski(A_289,C_290)
      | ~ r1_tarski(B_291,C_290)
      | ~ r1_tarski(A_289,B_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_3532,plain,(
    ! [A_289] :
      ( r1_tarski(A_289,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_289,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3442,c_3527])).

tff(c_3467,plain,(
    ! [A_274,B_275] :
      ( ~ r2_hidden('#skF_1'(A_274,B_275),B_275)
      | r1_tarski(A_274,B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3601,plain,(
    ! [A_299,A_300] :
      ( r1_tarski(A_299,A_300)
      | ~ m1_subset_1('#skF_1'(A_299,A_300),A_300)
      | v1_xboole_0(A_300) ) ),
    inference(resolution,[status(thm)],[c_18,c_3467])).

tff(c_3946,plain,(
    ! [A_329,B_330] :
      ( r1_tarski(A_329,k1_zfmisc_1(B_330))
      | v1_xboole_0(k1_zfmisc_1(B_330))
      | ~ r1_tarski('#skF_1'(A_329,k1_zfmisc_1(B_330)),B_330) ) ),
    inference(resolution,[status(thm)],[c_26,c_3601])).

tff(c_3950,plain,(
    ! [A_329] :
      ( r1_tarski(A_329,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_1'(A_329,k1_zfmisc_1(u1_struct_0('#skF_4'))),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_3532,c_3946])).

tff(c_3953,plain,(
    ! [A_329] :
      ( r1_tarski(A_329,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ r1_tarski('#skF_1'(A_329,k1_zfmisc_1(u1_struct_0('#skF_4'))),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3454,c_3950])).

tff(c_4018,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_5'))
    | r1_tarski(k1_zfmisc_1('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_4001,c_3953])).

tff(c_4025,plain,(
    r1_tarski(k1_zfmisc_1('#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_4018])).

tff(c_3520,plain,(
    ! [C_286,B_287,A_288] :
      ( r2_hidden(C_286,B_287)
      | ~ r2_hidden(C_286,A_288)
      | ~ r1_tarski(A_288,B_287) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3525,plain,(
    ! [B_12,B_287,A_11] :
      ( r2_hidden(B_12,B_287)
      | ~ r1_tarski(A_11,B_287)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_3520])).

tff(c_4045,plain,(
    ! [B_12] :
      ( r2_hidden(B_12,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_12,k1_zfmisc_1('#skF_5'))
      | v1_xboole_0(k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4025,c_3525])).

tff(c_4079,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4045])).

tff(c_3451,plain,(
    ! [A_13,B_14] :
      ( v1_xboole_0(A_13)
      | ~ v1_xboole_0(k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_26,c_3444])).

tff(c_4119,plain,(
    ! [A_342] :
      ( v1_xboole_0(A_342)
      | ~ r1_tarski(A_342,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_4079,c_3451])).

tff(c_4131,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_4119])).

tff(c_4139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4131])).

tff(c_4146,plain,(
    ! [B_343] :
      ( r2_hidden(B_343,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_343,k1_zfmisc_1('#skF_5')) ) ),
    inference(splitRight,[status(thm)],[c_4045])).

tff(c_4151,plain,(
    ! [B_343] :
      ( m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_343,k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4146,c_16])).

tff(c_4159,plain,(
    ! [B_343] :
      ( m1_subset_1(B_343,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_343,k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3454,c_4151])).

tff(c_5267,plain,(
    ! [B_392,A_393] :
      ( v1_tdlat_3(B_392)
      | ~ v2_tex_2(u1_struct_0(B_392),A_393)
      | ~ m1_subset_1(u1_struct_0(B_392),k1_zfmisc_1(u1_struct_0(A_393)))
      | ~ m1_pre_topc(B_392,A_393)
      | v2_struct_0(B_392)
      | ~ l1_pre_topc(A_393)
      | v2_struct_0(A_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_5289,plain,(
    ! [B_392] :
      ( v1_tdlat_3(B_392)
      | ~ v2_tex_2(u1_struct_0(B_392),'#skF_4')
      | ~ m1_pre_topc(B_392,'#skF_4')
      | v2_struct_0(B_392)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_392),k1_zfmisc_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_4159,c_5267])).

tff(c_5303,plain,(
    ! [B_392] :
      ( v1_tdlat_3(B_392)
      | ~ v2_tex_2(u1_struct_0(B_392),'#skF_4')
      | ~ m1_pre_topc(B_392,'#skF_4')
      | v2_struct_0(B_392)
      | v2_struct_0('#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_392),k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5289])).

tff(c_5308,plain,(
    ! [B_395] :
      ( v1_tdlat_3(B_395)
      | ~ v2_tex_2(u1_struct_0(B_395),'#skF_4')
      | ~ m1_pre_topc(B_395,'#skF_4')
      | v2_struct_0(B_395)
      | ~ m1_subset_1(u1_struct_0(B_395),k1_zfmisc_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_5303])).

tff(c_5317,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | ~ v2_tex_2(u1_struct_0('#skF_3'('#skF_4','#skF_5')),'#skF_4')
    | ~ m1_pre_topc('#skF_3'('#skF_4','#skF_5'),'#skF_4')
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4725,c_5308])).

tff(c_5325,plain,
    ( v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4907,c_3930,c_3420,c_4725,c_5317])).

tff(c_5327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3692,c_4959,c_5325])).

tff(c_5328,plain,(
    v1_tdlat_3('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4763])).

tff(c_5656,plain,(
    ! [B_413,A_414] :
      ( ~ v1_tdlat_3(B_413)
      | v7_struct_0(B_413)
      | v2_struct_0(B_413)
      | ~ m1_pre_topc(B_413,A_414)
      | ~ l1_pre_topc(A_414)
      | ~ v2_tdlat_3(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5662,plain,
    ( ~ v1_tdlat_3('#skF_3'('#skF_4','#skF_5'))
    | v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_tdlat_3('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_3930,c_5656])).

tff(c_5669,plain,
    ( v7_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_5328,c_5662])).

tff(c_5671,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_3692,c_4775,c_5669])).

tff(c_5672,plain,(
    ~ l1_struct_0('#skF_3'('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4773])).

tff(c_5676,plain,(
    ~ l1_pre_topc('#skF_3'('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_28,c_5672])).

tff(c_5680,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3936,c_5676])).

tff(c_5681,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4018])).

tff(c_5689,plain,(
    ! [A_415] :
      ( v1_xboole_0(A_415)
      | ~ r1_tarski(A_415,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5681,c_3451])).

tff(c_5701,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_5689])).

tff(c_5709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_5701])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.60/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.44  
% 6.66/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.44  %$ v2_tex_2 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_tdlat_3 > v2_struct_0 > v2_pre_topc > v1_zfmisc_1 > v1_xboole_0 > v1_tdlat_3 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 6.66/2.44  
% 6.66/2.44  %Foreground sorts:
% 6.66/2.44  
% 6.66/2.44  
% 6.66/2.44  %Background operators:
% 6.66/2.44  
% 6.66/2.44  
% 6.66/2.44  %Foreground operators:
% 6.66/2.44  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.66/2.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.66/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.66/2.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.66/2.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.66/2.44  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 6.66/2.44  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.66/2.44  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 6.66/2.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.66/2.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 6.66/2.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.66/2.44  tff('#skF_5', type, '#skF_5': $i).
% 6.66/2.44  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 6.66/2.44  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.66/2.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.66/2.44  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.66/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.66/2.44  tff('#skF_4', type, '#skF_4': $i).
% 6.66/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.66/2.44  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 6.66/2.44  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.66/2.44  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.66/2.44  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.66/2.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.66/2.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.66/2.44  tff(v2_tdlat_3, type, v2_tdlat_3: $i > $o).
% 6.66/2.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.66/2.44  
% 6.66/2.47  tff(f_246, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (v2_tex_2(B, A) <=> v1_zfmisc_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tex_2)).
% 6.66/2.47  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.66/2.47  tff(f_152, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (?[C]: (((~v2_struct_0(C) & v1_pre_topc(C)) & m1_pre_topc(C, A)) & (B = u1_struct_0(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_tsep_1)).
% 6.66/2.47  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.66/2.47  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.66/2.47  tff(f_226, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 6.66/2.47  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.66/2.47  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.66/2.47  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.66/2.47  tff(f_200, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_xboole_0(B) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_tex_2)).
% 6.66/2.47  tff(f_186, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((B = u1_struct_0(A)) => (v2_tex_2(B, A) <=> v1_tdlat_3(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_tex_2)).
% 6.66/2.47  tff(f_131, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 6.66/2.47  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 6.66/2.47  tff(f_44, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.66/2.47  tff(f_212, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v2_tex_2(k6_domain_1(u1_struct_0(A), B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_tex_2)).
% 6.66/2.47  tff(f_78, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 6.66/2.47  tff(f_172, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => (v2_tex_2(C, A) <=> v1_tdlat_3(B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_tex_2)).
% 6.66/2.47  tff(f_121, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v2_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => ((~v2_struct_0(B) & ~v7_struct_0(B)) => (~v2_struct_0(B) & ~v1_tdlat_3(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc32_tex_2)).
% 6.66/2.47  tff(c_74, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.66/2.47  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.66/2.47  tff(c_76, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.66/2.47  tff(c_82, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.66/2.47  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.66/2.47  tff(c_3908, plain, (![A_326, B_327]: (m1_pre_topc('#skF_3'(A_326, B_327), A_326) | ~m1_subset_1(B_327, k1_zfmisc_1(u1_struct_0(A_326))) | v1_xboole_0(B_327) | ~l1_pre_topc(A_326) | v2_struct_0(A_326))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.66/2.47  tff(c_3922, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_3908])).
% 6.66/2.47  tff(c_3929, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3922])).
% 6.66/2.47  tff(c_3930, plain, (m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_74, c_3929])).
% 6.66/2.47  tff(c_30, plain, (![B_18, A_16]: (l1_pre_topc(B_18) | ~m1_pre_topc(B_18, A_16) | ~l1_pre_topc(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.66/2.47  tff(c_3933, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_3930, c_30])).
% 6.66/2.47  tff(c_3936, plain, (l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3933])).
% 6.66/2.47  tff(c_28, plain, (![A_15]: (l1_struct_0(A_15) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.66/2.47  tff(c_3665, plain, (![A_308, B_309]: (~v2_struct_0('#skF_3'(A_308, B_309)) | ~m1_subset_1(B_309, k1_zfmisc_1(u1_struct_0(A_308))) | v1_xboole_0(B_309) | ~l1_pre_topc(A_308) | v2_struct_0(A_308))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.66/2.47  tff(c_3684, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_3665])).
% 6.66/2.47  tff(c_3691, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_3684])).
% 6.66/2.47  tff(c_3692, plain, (~v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_82, c_74, c_3691])).
% 6.66/2.47  tff(c_90, plain, (v2_tex_2('#skF_5', '#skF_4') | v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.66/2.47  tff(c_94, plain, (v1_zfmisc_1('#skF_5')), inference(splitLeft, [status(thm)], [c_90])).
% 6.66/2.47  tff(c_84, plain, (~v1_zfmisc_1('#skF_5') | ~v2_tex_2('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.66/2.47  tff(c_96, plain, (~v2_tex_2('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_84])).
% 6.66/2.47  tff(c_80, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.66/2.47  tff(c_725, plain, (![B_140, A_141]: (v2_tex_2(B_140, A_141) | ~m1_subset_1(B_140, k1_zfmisc_1(u1_struct_0(A_141))) | ~l1_pre_topc(A_141) | ~v1_tdlat_3(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_226])).
% 6.66/2.47  tff(c_748, plain, (v2_tex_2('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_725])).
% 6.66/2.47  tff(c_756, plain, (v2_tex_2('#skF_5', '#skF_4') | ~v1_tdlat_3('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_748])).
% 6.66/2.47  tff(c_757, plain, (~v1_tdlat_3('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_82, c_96, c_756])).
% 6.66/2.47  tff(c_107, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~m1_subset_1(A_64, k1_zfmisc_1(B_65)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.66/2.47  tff(c_115, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_107])).
% 6.66/2.47  tff(c_18, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.66/2.47  tff(c_193, plain, (![C_88, B_89, A_90]: (r2_hidden(C_88, B_89) | ~r2_hidden(C_88, A_90) | ~r1_tarski(A_90, B_89))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.47  tff(c_390, plain, (![B_114, B_115, A_116]: (r2_hidden(B_114, B_115) | ~r1_tarski(A_116, B_115) | ~m1_subset_1(B_114, A_116) | v1_xboole_0(A_116))), inference(resolution, [status(thm)], [c_18, c_193])).
% 6.66/2.47  tff(c_398, plain, (![B_114]: (r2_hidden(B_114, u1_struct_0('#skF_4')) | ~m1_subset_1(B_114, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_115, c_390])).
% 6.66/2.47  tff(c_408, plain, (![B_117]: (r2_hidden(B_117, u1_struct_0('#skF_4')) | ~m1_subset_1(B_117, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_398])).
% 6.66/2.47  tff(c_16, plain, (![B_12, A_11]: (m1_subset_1(B_12, A_11) | ~r2_hidden(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.66/2.47  tff(c_419, plain, (![B_117]: (m1_subset_1(B_117, u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_117, '#skF_5'))), inference(resolution, [status(thm)], [c_408, c_16])).
% 6.66/2.47  tff(c_430, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_419])).
% 6.66/2.47  tff(c_26, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.66/2.47  tff(c_592, plain, (![B_129, A_130]: (v2_tex_2(B_129, A_130) | ~m1_subset_1(B_129, k1_zfmisc_1(u1_struct_0(A_130))) | ~v1_xboole_0(B_129) | ~l1_pre_topc(A_130) | ~v2_pre_topc(A_130) | v2_struct_0(A_130))), inference(cnfTransformation, [status(thm)], [f_200])).
% 6.66/2.47  tff(c_2743, plain, (![A_225, A_226]: (v2_tex_2(A_225, A_226) | ~v1_xboole_0(A_225) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226) | ~r1_tarski(A_225, u1_struct_0(A_226)))), inference(resolution, [status(thm)], [c_26, c_592])).
% 6.66/2.47  tff(c_2801, plain, (![A_227]: (v2_tex_2(u1_struct_0(A_227), A_227) | ~v1_xboole_0(u1_struct_0(A_227)) | ~l1_pre_topc(A_227) | ~v2_pre_topc(A_227) | v2_struct_0(A_227))), inference(resolution, [status(thm)], [c_12, c_2743])).
% 6.66/2.47  tff(c_1708, plain, (![A_183]: (v1_tdlat_3(A_183) | ~v2_tex_2(u1_struct_0(A_183), A_183) | ~m1_subset_1(u1_struct_0(A_183), k1_zfmisc_1(u1_struct_0(A_183))) | ~l1_pre_topc(A_183) | v2_struct_0(A_183))), inference(cnfTransformation, [status(thm)], [f_186])).
% 6.66/2.47  tff(c_1730, plain, (![A_183]: (v1_tdlat_3(A_183) | ~v2_tex_2(u1_struct_0(A_183), A_183) | ~l1_pre_topc(A_183) | v2_struct_0(A_183) | ~r1_tarski(u1_struct_0(A_183), u1_struct_0(A_183)))), inference(resolution, [status(thm)], [c_26, c_1708])).
% 6.66/2.47  tff(c_1744, plain, (![A_183]: (v1_tdlat_3(A_183) | ~v2_tex_2(u1_struct_0(A_183), A_183) | ~l1_pre_topc(A_183) | v2_struct_0(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1730])).
% 6.66/2.47  tff(c_2815, plain, (![A_228]: (v1_tdlat_3(A_228) | ~v1_xboole_0(u1_struct_0(A_228)) | ~l1_pre_topc(A_228) | ~v2_pre_topc(A_228) | v2_struct_0(A_228))), inference(resolution, [status(thm)], [c_2801, c_1744])).
% 6.66/2.47  tff(c_2824, plain, (v1_tdlat_3('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_430, c_2815])).
% 6.66/2.47  tff(c_2830, plain, (v1_tdlat_3('#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_2824])).
% 6.66/2.47  tff(c_2832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_757, c_2830])).
% 6.66/2.47  tff(c_2834, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_419])).
% 6.66/2.47  tff(c_48, plain, (![A_27]: (m1_subset_1('#skF_2'(A_27), A_27) | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.66/2.47  tff(c_2847, plain, (![B_230]: (m1_subset_1(B_230, u1_struct_0('#skF_4')) | ~m1_subset_1(B_230, '#skF_5'))), inference(splitRight, [status(thm)], [c_419])).
% 6.66/2.47  tff(c_34, plain, (![A_20, B_21]: (k6_domain_1(A_20, B_21)=k1_tarski(B_21) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.66/2.47  tff(c_2857, plain, (![B_230]: (k6_domain_1(u1_struct_0('#skF_4'), B_230)=k1_tarski(B_230) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_230, '#skF_5'))), inference(resolution, [status(thm)], [c_2847, c_34])).
% 6.66/2.47  tff(c_2868, plain, (![B_230]: (k6_domain_1(u1_struct_0('#skF_4'), B_230)=k1_tarski(B_230) | ~m1_subset_1(B_230, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2834, c_2857])).
% 6.66/2.47  tff(c_44, plain, (![A_27, B_30]: (v1_zfmisc_1(A_27) | k6_domain_1(A_27, B_30)!=A_27 | ~m1_subset_1(B_30, A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.66/2.47  tff(c_2850, plain, (![B_230]: (v1_zfmisc_1(u1_struct_0('#skF_4')) | k6_domain_1(u1_struct_0('#skF_4'), B_230)!=u1_struct_0('#skF_4') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(B_230, '#skF_5'))), inference(resolution, [status(thm)], [c_2847, c_44])).
% 6.66/2.47  tff(c_2863, plain, (![B_230]: (v1_zfmisc_1(u1_struct_0('#skF_4')) | k6_domain_1(u1_struct_0('#skF_4'), B_230)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_230, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2834, c_2850])).
% 6.66/2.47  tff(c_3065, plain, (![B_241]: (k6_domain_1(u1_struct_0('#skF_4'), B_241)!=u1_struct_0('#skF_4') | ~m1_subset_1(B_241, '#skF_5'))), inference(splitLeft, [status(thm)], [c_2863])).
% 6.66/2.47  tff(c_3100, plain, (![B_244]: (u1_struct_0('#skF_4')!=k1_tarski(B_244) | ~m1_subset_1(B_244, '#skF_5') | ~m1_subset_1(B_244, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2868, c_3065])).
% 6.66/2.47  tff(c_3106, plain, (k1_tarski('#skF_2'('#skF_5'))!=u1_struct_0('#skF_4') | ~m1_subset_1('#skF_2'('#skF_5'), '#skF_5') | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_3100])).
% 6.66/2.47  tff(c_3115, plain, (k1_tarski('#skF_2'('#skF_5'))!=u1_struct_0('#skF_4') | ~m1_subset_1('#skF_2'('#skF_5'), '#skF_5') | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_3106])).
% 6.66/2.47  tff(c_3116, plain, (k1_tarski('#skF_2'('#skF_5'))!=u1_struct_0('#skF_4') | ~m1_subset_1('#skF_2'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_74, c_3115])).
% 6.66/2.47  tff(c_3118, plain, (~m1_subset_1('#skF_2'('#skF_5'), '#skF_5')), inference(splitLeft, [status(thm)], [c_3116])).
% 6.66/2.47  tff(c_3121, plain, (~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_3118])).
% 6.66/2.47  tff(c_3127, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_3121])).
% 6.66/2.47  tff(c_3129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_3127])).
% 6.66/2.47  tff(c_3131, plain, (m1_subset_1('#skF_2'('#skF_5'), '#skF_5')), inference(splitRight, [status(thm)], [c_3116])).
% 6.66/2.47  tff(c_200, plain, (![A_91, C_92, B_93]: (r1_tarski(A_91, C_92) | ~r1_tarski(B_93, C_92) | ~r1_tarski(A_91, B_93))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.66/2.47  tff(c_205, plain, (![A_91]: (r1_tarski(A_91, u1_struct_0('#skF_4')) | ~r1_tarski(A_91, '#skF_5'))), inference(resolution, [status(thm)], [c_115, c_200])).
% 6.66/2.47  tff(c_403, plain, (![B_114, A_91]: (r2_hidden(B_114, u1_struct_0('#skF_4')) | ~m1_subset_1(B_114, A_91) | v1_xboole_0(A_91) | ~r1_tarski(A_91, '#skF_5'))), inference(resolution, [status(thm)], [c_205, c_390])).
% 6.66/2.47  tff(c_3146, plain, (r2_hidden('#skF_2'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5') | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_3131, c_403])).
% 6.66/2.47  tff(c_3161, plain, (r2_hidden('#skF_2'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_3146])).
% 6.66/2.47  tff(c_3162, plain, (r2_hidden('#skF_2'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_3161])).
% 6.66/2.47  tff(c_3180, plain, (m1_subset_1('#skF_2'('#skF_5'), u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_3162, c_16])).
% 6.66/2.47  tff(c_3184, plain, (m1_subset_1('#skF_2'('#skF_5'), u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_2834, c_3180])).
% 6.66/2.47  tff(c_3152, plain, (k6_domain_1('#skF_5', '#skF_2'('#skF_5'))=k1_tarski('#skF_2'('#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_3131, c_34])).
% 6.66/2.47  tff(c_3168, plain, (k6_domain_1('#skF_5', '#skF_2'('#skF_5'))=k1_tarski('#skF_2'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_3152])).
% 6.66/2.47  tff(c_46, plain, (![A_27]: (k6_domain_1(A_27, '#skF_2'(A_27))=A_27 | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.66/2.47  tff(c_3212, plain, (k1_tarski('#skF_2'('#skF_5'))='#skF_5' | ~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3168, c_46])).
% 6.66/2.47  tff(c_3226, plain, (k1_tarski('#skF_2'('#skF_5'))='#skF_5' | v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_3212])).
% 6.66/2.47  tff(c_3227, plain, (k1_tarski('#skF_2'('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_74, c_3226])).
% 6.66/2.47  tff(c_3192, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_5'))=k1_tarski('#skF_2'('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_3184, c_34])).
% 6.66/2.47  tff(c_3204, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_5'))=k1_tarski('#skF_2'('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_2834, c_3192])).
% 6.66/2.47  tff(c_3340, plain, (k6_domain_1(u1_struct_0('#skF_4'), '#skF_2'('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3227, c_3204])).
% 6.66/2.47  tff(c_3401, plain, (![A_255, B_256]: (v2_tex_2(k6_domain_1(u1_struct_0(A_255), B_256), A_255) | ~m1_subset_1(B_256, u1_struct_0(A_255)) | ~l1_pre_topc(A_255) | ~v2_pre_topc(A_255) | v2_struct_0(A_255))), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.66/2.47  tff(c_3404, plain, (v2_tex_2('#skF_5', '#skF_4') | ~m1_subset_1('#skF_2'('#skF_5'), u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3340, c_3401])).
% 6.66/2.47  tff(c_3417, plain, (v2_tex_2('#skF_5', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3184, c_3404])).
% 6.66/2.47  tff(c_3419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_96, c_3417])).
% 6.66/2.47  tff(c_3421, plain, (~v1_zfmisc_1('#skF_5')), inference(splitRight, [status(thm)], [c_90])).
% 6.66/2.47  tff(c_4686, plain, (![A_371, B_372]: (u1_struct_0('#skF_3'(A_371, B_372))=B_372 | ~m1_subset_1(B_372, k1_zfmisc_1(u1_struct_0(A_371))) | v1_xboole_0(B_372) | ~l1_pre_topc(A_371) | v2_struct_0(A_371))), inference(cnfTransformation, [status(thm)], [f_152])).
% 6.66/2.47  tff(c_4712, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_72, c_4686])).
% 6.66/2.47  tff(c_4724, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5' | v1_xboole_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4712])).
% 6.66/2.47  tff(c_4725, plain, (u1_struct_0('#skF_3'('#skF_4', '#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_82, c_74, c_4724])).
% 6.66/2.47  tff(c_32, plain, (![A_19]: (v1_zfmisc_1(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | ~v7_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.66/2.47  tff(c_4749, plain, (v1_zfmisc_1('#skF_5') | ~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_32])).
% 6.66/2.47  tff(c_4773, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3421, c_4749])).
% 6.66/2.47  tff(c_4775, plain, (~v7_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_4773])).
% 6.66/2.47  tff(c_78, plain, (v2_tdlat_3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.66/2.47  tff(c_4026, plain, (![A_337]: (v1_tdlat_3(A_337) | ~v2_tex_2(u1_struct_0(A_337), A_337) | ~m1_subset_1(u1_struct_0(A_337), k1_zfmisc_1(u1_struct_0(A_337))) | ~l1_pre_topc(A_337) | v2_struct_0(A_337))), inference(cnfTransformation, [status(thm)], [f_186])).
% 6.66/2.47  tff(c_4032, plain, (![A_337]: (v1_tdlat_3(A_337) | ~v2_tex_2(u1_struct_0(A_337), A_337) | ~l1_pre_topc(A_337) | v2_struct_0(A_337) | ~r1_tarski(u1_struct_0(A_337), u1_struct_0(A_337)))), inference(resolution, [status(thm)], [c_26, c_4026])).
% 6.66/2.47  tff(c_4036, plain, (![A_337]: (v1_tdlat_3(A_337) | ~v2_tex_2(u1_struct_0(A_337), A_337) | ~l1_pre_topc(A_337) | v2_struct_0(A_337))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_4032])).
% 6.66/2.47  tff(c_4738, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_4036])).
% 6.66/2.47  tff(c_4762, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3936, c_4738])).
% 6.66/2.47  tff(c_4763, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2('#skF_5', '#skF_3'('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3692, c_4762])).
% 6.66/2.47  tff(c_4808, plain, (~v2_tex_2('#skF_5', '#skF_3'('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_4763])).
% 6.66/2.47  tff(c_4857, plain, (![A_377]: (v2_tex_2(u1_struct_0(A_377), A_377) | ~v1_tdlat_3(A_377) | ~m1_subset_1(u1_struct_0(A_377), k1_zfmisc_1(u1_struct_0(A_377))) | ~l1_pre_topc(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_186])).
% 6.66/2.47  tff(c_4866, plain, (v2_tex_2(u1_struct_0('#skF_3'('#skF_4', '#skF_5')), '#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3'('#skF_4', '#skF_5')))) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_4857])).
% 6.66/2.47  tff(c_4881, plain, (v2_tex_2('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3936, c_4725, c_4725, c_4866])).
% 6.66/2.47  tff(c_4882, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3692, c_4808, c_4881])).
% 6.66/2.47  tff(c_4894, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4882])).
% 6.66/2.47  tff(c_4900, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_26, c_4894])).
% 6.66/2.47  tff(c_4905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_4900])).
% 6.66/2.47  tff(c_4907, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4882])).
% 6.66/2.47  tff(c_4869, plain, (v2_tex_2(u1_struct_0('#skF_3'('#skF_4', '#skF_5')), '#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~m1_subset_1(u1_struct_0('#skF_3'('#skF_4', '#skF_5')), k1_zfmisc_1('#skF_5')) | ~l1_pre_topc('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_4857])).
% 6.66/2.47  tff(c_4884, plain, (v2_tex_2('#skF_5', '#skF_3'('#skF_4', '#skF_5')) | ~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3936, c_4725, c_4725, c_4869])).
% 6.66/2.47  tff(c_4885, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3692, c_4808, c_4884])).
% 6.66/2.47  tff(c_4959, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4907, c_4885])).
% 6.66/2.47  tff(c_3420, plain, (v2_tex_2('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_90])).
% 6.66/2.47  tff(c_3444, plain, (![B_266, A_267]: (v1_xboole_0(B_266) | ~m1_subset_1(B_266, A_267) | ~v1_xboole_0(A_267))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.66/2.47  tff(c_3450, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_72, c_3444])).
% 6.66/2.47  tff(c_3454, plain, (~v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_74, c_3450])).
% 6.66/2.47  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.47  tff(c_3500, plain, (![B_279, A_280]: (m1_subset_1(B_279, A_280) | ~r2_hidden(B_279, A_280) | v1_xboole_0(A_280))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.66/2.47  tff(c_3583, plain, (![A_297, B_298]: (m1_subset_1('#skF_1'(A_297, B_298), A_297) | v1_xboole_0(A_297) | r1_tarski(A_297, B_298))), inference(resolution, [status(thm)], [c_6, c_3500])).
% 6.66/2.47  tff(c_24, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.66/2.47  tff(c_4001, plain, (![B_335, B_336]: (r1_tarski('#skF_1'(k1_zfmisc_1(B_335), B_336), B_335) | v1_xboole_0(k1_zfmisc_1(B_335)) | r1_tarski(k1_zfmisc_1(B_335), B_336))), inference(resolution, [status(thm)], [c_3583, c_24])).
% 6.66/2.47  tff(c_3434, plain, (![A_262, B_263]: (r1_tarski(A_262, B_263) | ~m1_subset_1(A_262, k1_zfmisc_1(B_263)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.66/2.47  tff(c_3442, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_3434])).
% 6.66/2.47  tff(c_3527, plain, (![A_289, C_290, B_291]: (r1_tarski(A_289, C_290) | ~r1_tarski(B_291, C_290) | ~r1_tarski(A_289, B_291))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.66/2.47  tff(c_3532, plain, (![A_289]: (r1_tarski(A_289, u1_struct_0('#skF_4')) | ~r1_tarski(A_289, '#skF_5'))), inference(resolution, [status(thm)], [c_3442, c_3527])).
% 6.66/2.47  tff(c_3467, plain, (![A_274, B_275]: (~r2_hidden('#skF_1'(A_274, B_275), B_275) | r1_tarski(A_274, B_275))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.47  tff(c_3601, plain, (![A_299, A_300]: (r1_tarski(A_299, A_300) | ~m1_subset_1('#skF_1'(A_299, A_300), A_300) | v1_xboole_0(A_300))), inference(resolution, [status(thm)], [c_18, c_3467])).
% 6.66/2.47  tff(c_3946, plain, (![A_329, B_330]: (r1_tarski(A_329, k1_zfmisc_1(B_330)) | v1_xboole_0(k1_zfmisc_1(B_330)) | ~r1_tarski('#skF_1'(A_329, k1_zfmisc_1(B_330)), B_330))), inference(resolution, [status(thm)], [c_26, c_3601])).
% 6.66/2.47  tff(c_3950, plain, (![A_329]: (r1_tarski(A_329, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_1'(A_329, k1_zfmisc_1(u1_struct_0('#skF_4'))), '#skF_5'))), inference(resolution, [status(thm)], [c_3532, c_3946])).
% 6.66/2.47  tff(c_3953, plain, (![A_329]: (r1_tarski(A_329, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~r1_tarski('#skF_1'(A_329, k1_zfmisc_1(u1_struct_0('#skF_4'))), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_3454, c_3950])).
% 6.66/2.47  tff(c_4018, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5')) | r1_tarski(k1_zfmisc_1('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4001, c_3953])).
% 6.66/2.47  tff(c_4025, plain, (r1_tarski(k1_zfmisc_1('#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_4018])).
% 6.66/2.47  tff(c_3520, plain, (![C_286, B_287, A_288]: (r2_hidden(C_286, B_287) | ~r2_hidden(C_286, A_288) | ~r1_tarski(A_288, B_287))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.66/2.47  tff(c_3525, plain, (![B_12, B_287, A_11]: (r2_hidden(B_12, B_287) | ~r1_tarski(A_11, B_287) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_18, c_3520])).
% 6.66/2.47  tff(c_4045, plain, (![B_12]: (r2_hidden(B_12, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_12, k1_zfmisc_1('#skF_5')) | v1_xboole_0(k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_4025, c_3525])).
% 6.66/2.47  tff(c_4079, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_4045])).
% 6.66/2.47  tff(c_3451, plain, (![A_13, B_14]: (v1_xboole_0(A_13) | ~v1_xboole_0(k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_26, c_3444])).
% 6.66/2.47  tff(c_4119, plain, (![A_342]: (v1_xboole_0(A_342) | ~r1_tarski(A_342, '#skF_5'))), inference(resolution, [status(thm)], [c_4079, c_3451])).
% 6.66/2.47  tff(c_4131, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_12, c_4119])).
% 6.66/2.47  tff(c_4139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_4131])).
% 6.66/2.47  tff(c_4146, plain, (![B_343]: (r2_hidden(B_343, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_343, k1_zfmisc_1('#skF_5')))), inference(splitRight, [status(thm)], [c_4045])).
% 6.66/2.47  tff(c_4151, plain, (![B_343]: (m1_subset_1(B_343, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_343, k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_4146, c_16])).
% 6.66/2.47  tff(c_4159, plain, (![B_343]: (m1_subset_1(B_343, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_343, k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_3454, c_4151])).
% 6.66/2.47  tff(c_5267, plain, (![B_392, A_393]: (v1_tdlat_3(B_392) | ~v2_tex_2(u1_struct_0(B_392), A_393) | ~m1_subset_1(u1_struct_0(B_392), k1_zfmisc_1(u1_struct_0(A_393))) | ~m1_pre_topc(B_392, A_393) | v2_struct_0(B_392) | ~l1_pre_topc(A_393) | v2_struct_0(A_393))), inference(cnfTransformation, [status(thm)], [f_172])).
% 6.66/2.47  tff(c_5289, plain, (![B_392]: (v1_tdlat_3(B_392) | ~v2_tex_2(u1_struct_0(B_392), '#skF_4') | ~m1_pre_topc(B_392, '#skF_4') | v2_struct_0(B_392) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_subset_1(u1_struct_0(B_392), k1_zfmisc_1('#skF_5')))), inference(resolution, [status(thm)], [c_4159, c_5267])).
% 6.66/2.47  tff(c_5303, plain, (![B_392]: (v1_tdlat_3(B_392) | ~v2_tex_2(u1_struct_0(B_392), '#skF_4') | ~m1_pre_topc(B_392, '#skF_4') | v2_struct_0(B_392) | v2_struct_0('#skF_4') | ~m1_subset_1(u1_struct_0(B_392), k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5289])).
% 6.66/2.47  tff(c_5308, plain, (![B_395]: (v1_tdlat_3(B_395) | ~v2_tex_2(u1_struct_0(B_395), '#skF_4') | ~m1_pre_topc(B_395, '#skF_4') | v2_struct_0(B_395) | ~m1_subset_1(u1_struct_0(B_395), k1_zfmisc_1('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_82, c_5303])).
% 6.66/2.47  tff(c_5317, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | ~v2_tex_2(u1_struct_0('#skF_3'('#skF_4', '#skF_5')), '#skF_4') | ~m1_pre_topc('#skF_3'('#skF_4', '#skF_5'), '#skF_4') | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_4725, c_5308])).
% 6.66/2.47  tff(c_5325, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4907, c_3930, c_3420, c_4725, c_5317])).
% 6.66/2.47  tff(c_5327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3692, c_4959, c_5325])).
% 6.66/2.47  tff(c_5328, plain, (v1_tdlat_3('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_4763])).
% 6.66/2.47  tff(c_5656, plain, (![B_413, A_414]: (~v1_tdlat_3(B_413) | v7_struct_0(B_413) | v2_struct_0(B_413) | ~m1_pre_topc(B_413, A_414) | ~l1_pre_topc(A_414) | ~v2_tdlat_3(A_414) | ~v2_pre_topc(A_414) | v2_struct_0(A_414))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.66/2.47  tff(c_5662, plain, (~v1_tdlat_3('#skF_3'('#skF_4', '#skF_5')) | v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_tdlat_3('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_3930, c_5656])).
% 6.66/2.47  tff(c_5669, plain, (v7_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_3'('#skF_4', '#skF_5')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_5328, c_5662])).
% 6.66/2.47  tff(c_5671, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_3692, c_4775, c_5669])).
% 6.66/2.47  tff(c_5672, plain, (~l1_struct_0('#skF_3'('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_4773])).
% 6.66/2.47  tff(c_5676, plain, (~l1_pre_topc('#skF_3'('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_28, c_5672])).
% 6.66/2.47  tff(c_5680, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3936, c_5676])).
% 6.66/2.47  tff(c_5681, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_4018])).
% 6.66/2.47  tff(c_5689, plain, (![A_415]: (v1_xboole_0(A_415) | ~r1_tarski(A_415, '#skF_5'))), inference(resolution, [status(thm)], [c_5681, c_3451])).
% 6.66/2.47  tff(c_5701, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_12, c_5689])).
% 6.66/2.47  tff(c_5709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_5701])).
% 6.66/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.66/2.47  
% 6.66/2.47  Inference rules
% 6.66/2.47  ----------------------
% 6.66/2.47  #Ref     : 0
% 6.66/2.47  #Sup     : 1141
% 6.66/2.47  #Fact    : 0
% 6.66/2.47  #Define  : 0
% 6.66/2.47  #Split   : 43
% 6.66/2.47  #Chain   : 0
% 6.66/2.47  #Close   : 0
% 6.66/2.47  
% 6.66/2.47  Ordering : KBO
% 6.66/2.47  
% 6.66/2.47  Simplification rules
% 6.66/2.47  ----------------------
% 6.66/2.47  #Subsume      : 275
% 6.66/2.47  #Demod        : 317
% 6.66/2.47  #Tautology    : 288
% 6.66/2.47  #SimpNegUnit  : 333
% 6.66/2.47  #BackRed      : 3
% 6.66/2.47  
% 6.66/2.47  #Partial instantiations: 0
% 6.66/2.47  #Strategies tried      : 1
% 6.66/2.47  
% 6.66/2.47  Timing (in seconds)
% 6.66/2.47  ----------------------
% 6.66/2.48  Preprocessing        : 0.37
% 6.66/2.48  Parsing              : 0.19
% 6.66/2.48  CNF conversion       : 0.03
% 6.66/2.48  Main loop            : 1.31
% 6.66/2.48  Inferencing          : 0.44
% 6.66/2.48  Reduction            : 0.39
% 6.66/2.48  Demodulation         : 0.24
% 6.66/2.48  BG Simplification    : 0.05
% 6.66/2.48  Subsumption          : 0.33
% 6.66/2.48  Abstraction          : 0.06
% 6.66/2.48  MUC search           : 0.00
% 6.66/2.48  Cooper               : 0.00
% 6.66/2.48  Total                : 1.74
% 6.66/2.48  Index Insertion      : 0.00
% 6.66/2.48  Index Deletion       : 0.00
% 6.66/2.48  Index Matching       : 0.00
% 6.66/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
