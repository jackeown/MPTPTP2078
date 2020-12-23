%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:29:05 EST 2020

% Result     : Theorem 19.36s
% Output     : CNFRefutation 19.52s
% Verified   : 
% Statistics : Number of formulae       :  331 (20690 expanded)
%              Number of leaves         :   48 (6593 expanded)
%              Depth                    :   40
%              Number of atoms          :  775 (55741 expanded)
%              Number of equality atoms :   70 (6068 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_208,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ( v1_tex_2(k1_tex_2(A,B),A)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_171,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,A)
         => ~ ( v1_subset_1(k6_domain_1(A,B),A)
              & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_146,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B))
        & m1_pre_topc(k1_tex_2(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_tex_2(B,A)
          <=> ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ( C = u1_struct_0(B)
                 => v1_subset_1(C,u1_struct_0(A)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

tff(f_132,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_160,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ( ~ v2_struct_0(k1_tex_2(A,B))
        & v7_struct_0(k1_tex_2(A,B))
        & v1_pre_topc(k1_tex_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_182,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,A)
         => v1_subset_1(k6_domain_1(A,B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

tff(f_195,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
              & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_71,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(c_82,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_38,plain,(
    ! [A_21] :
      ( l1_struct_0(A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_8,plain,(
    ! [C_9] : r2_hidden(C_9,k1_tarski(C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6804,plain,(
    ! [B_437,A_438] :
      ( ~ r2_hidden(B_437,A_438)
      | ~ v1_xboole_0(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6808,plain,(
    ! [C_9] : ~ v1_xboole_0(k1_tarski(C_9)) ),
    inference(resolution,[status(thm)],[c_8,c_6804])).

tff(c_6890,plain,(
    ! [A_457] :
      ( v1_xboole_0(A_457)
      | r2_hidden('#skF_1'(A_457),A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6894,plain,(
    ! [A_5] :
      ( '#skF_1'(k1_tarski(A_5)) = A_5
      | v1_xboole_0(k1_tarski(A_5)) ) ),
    inference(resolution,[status(thm)],[c_6890,c_6])).

tff(c_6900,plain,(
    ! [A_5] : '#skF_1'(k1_tarski(A_5)) = A_5 ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_6894])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6952,plain,(
    ! [B_471,A_472] :
      ( m1_subset_1(B_471,A_472)
      | ~ r2_hidden(B_471,A_472)
      | v1_xboole_0(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6963,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_6952])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_6917,plain,(
    ! [B_460,A_461] :
      ( v1_xboole_0(B_460)
      | ~ m1_subset_1(B_460,A_461)
      | ~ v1_xboole_0(A_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6924,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_6917])).

tff(c_6926,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_6924])).

tff(c_7033,plain,(
    ! [A_482,B_483] :
      ( k6_domain_1(A_482,B_483) = k1_tarski(B_483)
      | ~ m1_subset_1(B_483,A_482)
      | v1_xboole_0(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_7045,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_7033])).

tff(c_7056,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_6926,c_7045])).

tff(c_158,plain,(
    ! [B_75,A_76] :
      ( v1_xboole_0(B_75)
      | ~ m1_subset_1(B_75,A_76)
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_169,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_158])).

tff(c_172,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_275,plain,(
    ! [A_96,B_97] :
      ( k6_domain_1(A_96,B_97) = k1_tarski(B_97)
      | ~ m1_subset_1(B_97,A_96)
      | v1_xboole_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_287,plain,
    ( k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_275])).

tff(c_298,plain,(
    k6_domain_1(u1_struct_0('#skF_5'),'#skF_6') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_287])).

tff(c_86,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_109,plain,(
    ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_92,plain,
    ( v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_171,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_92])).

tff(c_300,plain,(
    v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_171])).

tff(c_1921,plain,(
    ! [A_202,B_203] :
      ( ~ v1_zfmisc_1(A_202)
      | ~ v1_subset_1(k6_domain_1(A_202,B_203),A_202)
      | ~ m1_subset_1(B_203,A_202)
      | v1_xboole_0(A_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1942,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_5'))
    | ~ v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_1921])).

tff(c_1955,plain,
    ( ~ v1_zfmisc_1(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_300,c_1942])).

tff(c_1956,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_1955])).

tff(c_2226,plain,(
    ! [A_226,B_227] :
      ( m1_pre_topc(k1_tex_2(A_226,B_227),A_226)
      | ~ m1_subset_1(B_227,u1_struct_0(A_226))
      | ~ l1_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2238,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_2226])).

tff(c_2248,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2238])).

tff(c_2249,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2248])).

tff(c_2772,plain,(
    ! [A_257,B_258] :
      ( m1_subset_1('#skF_4'(A_257,B_258),k1_zfmisc_1(u1_struct_0(A_257)))
      | v1_tex_2(B_258,A_257)
      | ~ m1_pre_topc(B_258,A_257)
      | ~ l1_pre_topc(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    ! [B_44,A_43] :
      ( v1_subset_1(B_44,A_43)
      | B_44 = A_43
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_6596,plain,(
    ! [A_429,B_430] :
      ( v1_subset_1('#skF_4'(A_429,B_430),u1_struct_0(A_429))
      | u1_struct_0(A_429) = '#skF_4'(A_429,B_430)
      | v1_tex_2(B_430,A_429)
      | ~ m1_pre_topc(B_430,A_429)
      | ~ l1_pre_topc(A_429) ) ),
    inference(resolution,[status(thm)],[c_2772,c_58])).

tff(c_52,plain,(
    ! [A_33,B_39] :
      ( ~ v1_subset_1('#skF_4'(A_33,B_39),u1_struct_0(A_33))
      | v1_tex_2(B_39,A_33)
      | ~ m1_pre_topc(B_39,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_6756,plain,(
    ! [A_434,B_435] :
      ( u1_struct_0(A_434) = '#skF_4'(A_434,B_435)
      | v1_tex_2(B_435,A_434)
      | ~ m1_pre_topc(B_435,A_434)
      | ~ l1_pre_topc(A_434) ) ),
    inference(resolution,[status(thm)],[c_6596,c_52])).

tff(c_6763,plain,
    ( '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_6756,c_109])).

tff(c_6767,plain,(
    '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) = u1_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2249,c_6763])).

tff(c_40,plain,(
    ! [B_24,A_22] :
      ( l1_pre_topc(B_24)
      | ~ m1_pre_topc(B_24,A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2252,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2249,c_40])).

tff(c_2255,plain,(
    l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2252])).

tff(c_1897,plain,(
    ! [A_198,B_199] :
      ( ~ v2_struct_0(k1_tex_2(A_198,B_199))
      | ~ m1_subset_1(B_199,u1_struct_0(A_198))
      | ~ l1_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1908,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_1897])).

tff(c_1913,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1908])).

tff(c_1914,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1913])).

tff(c_2419,plain,(
    ! [B_239,A_240] :
      ( u1_struct_0(B_239) = '#skF_4'(A_240,B_239)
      | v1_tex_2(B_239,A_240)
      | ~ m1_pre_topc(B_239,A_240)
      | ~ l1_pre_topc(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_2422,plain,
    ( u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2419,c_109])).

tff(c_2425,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = '#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2249,c_2422])).

tff(c_42,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(u1_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2459,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2425,c_42])).

tff(c_2486,plain,
    ( ~ v1_xboole_0('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_1914,c_2459])).

tff(c_2488,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_2486])).

tff(c_2491,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_2488])).

tff(c_2495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_2491])).

tff(c_2496,plain,(
    ~ v1_xboole_0('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_2486])).

tff(c_194,plain,(
    ! [B_85,A_86] :
      ( m1_subset_1(B_85,A_86)
      | ~ r2_hidden(B_85,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_205,plain,(
    ! [A_1] :
      ( m1_subset_1('#skF_1'(A_1),A_1)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_194])).

tff(c_76,plain,(
    ! [A_52,B_54] :
      ( v1_subset_1(k6_domain_1(A_52,B_54),A_52)
      | ~ m1_subset_1(B_54,A_52)
      | v1_zfmisc_1(A_52)
      | v1_xboole_0(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2497,plain,(
    l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2486])).

tff(c_584,plain,(
    ! [A_116,B_117] :
      ( v7_struct_0(k1_tex_2(A_116,B_117))
      | ~ m1_subset_1(B_117,u1_struct_0(A_116))
      | ~ l1_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_595,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_584])).

tff(c_600,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_595])).

tff(c_601,plain,(
    v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_600])).

tff(c_2941,plain,(
    ! [A_264,B_265] :
      ( ~ v7_struct_0(A_264)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_264),B_265),u1_struct_0(A_264))
      | ~ m1_subset_1(B_265,u1_struct_0(A_264))
      | ~ l1_struct_0(A_264)
      | v2_struct_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_2944,plain,(
    ! [B_265] :
      ( ~ v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
      | ~ v1_subset_1(k6_domain_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')),B_265),u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
      | ~ m1_subset_1(B_265,u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
      | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
      | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2425,c_2941])).

tff(c_2960,plain,(
    ! [B_265] :
      ( ~ v1_subset_1(k6_domain_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')),B_265),'#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
      | ~ m1_subset_1(B_265,'#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
      | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2497,c_2425,c_2425,c_601,c_2944])).

tff(c_3177,plain,(
    ! [B_287] :
      ( ~ v1_subset_1(k6_domain_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')),B_287),'#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
      | ~ m1_subset_1(B_287,'#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1914,c_2960])).

tff(c_3184,plain,(
    ! [B_54] :
      ( ~ m1_subset_1(B_54,'#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
      | v1_zfmisc_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_76,c_3177])).

tff(c_3192,plain,(
    ! [B_54] :
      ( ~ m1_subset_1(B_54,'#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6')))
      | v1_zfmisc_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2496,c_3184])).

tff(c_3195,plain,(
    ! [B_288] : ~ m1_subset_1(B_288,'#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_3192])).

tff(c_3203,plain,(
    v1_xboole_0('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_205,c_3195])).

tff(c_3214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2496,c_3203])).

tff(c_3215,plain,(
    v1_zfmisc_1('#skF_4'('#skF_5',k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_3192])).

tff(c_6771,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6767,c_3215])).

tff(c_6785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1956,c_6771])).

tff(c_6787,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_6791,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_6787,c_42])).

tff(c_6794,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_6791])).

tff(c_6797,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_6794])).

tff(c_6801,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_6797])).

tff(c_6802,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'),'#skF_6'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_7058,plain,(
    ~ v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7056,c_6802])).

tff(c_7102,plain,(
    ! [A_487,B_488] :
      ( m1_subset_1(k6_domain_1(A_487,B_488),k1_zfmisc_1(A_487))
      | ~ m1_subset_1(B_488,A_487)
      | v1_xboole_0(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7123,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7056,c_7102])).

tff(c_7135,plain,
    ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_7123])).

tff(c_7136,plain,(
    m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_6926,c_7135])).

tff(c_7145,plain,
    ( v1_subset_1(k1_tarski('#skF_6'),u1_struct_0('#skF_5'))
    | u1_struct_0('#skF_5') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_7136,c_58])).

tff(c_7153,plain,(
    u1_struct_0('#skF_5') = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_7058,c_7145])).

tff(c_7580,plain,(
    ! [A_528,B_529] :
      ( ~ v2_struct_0(k1_tex_2(A_528,B_529))
      | ~ m1_subset_1(B_529,u1_struct_0(A_528))
      | ~ l1_pre_topc(A_528)
      | v2_struct_0(A_528) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_7583,plain,(
    ! [B_529] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5',B_529))
      | ~ m1_subset_1(B_529,k1_tarski('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7153,c_7580])).

tff(c_7593,plain,(
    ! [B_529] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5',B_529))
      | ~ m1_subset_1(B_529,k1_tarski('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7583])).

tff(c_7597,plain,(
    ! [B_530] :
      ( ~ v2_struct_0(k1_tex_2('#skF_5',B_530))
      | ~ m1_subset_1(B_530,k1_tarski('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_7593])).

tff(c_7601,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_6'))))
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6963,c_7597])).

tff(c_7611,plain,
    ( ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6900,c_7601])).

tff(c_7612,plain,(
    ~ v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_7611])).

tff(c_7924,plain,(
    ! [A_561,B_562] :
      ( m1_pre_topc(k1_tex_2(A_561,B_562),A_561)
      | ~ m1_subset_1(B_562,u1_struct_0(A_561))
      | ~ l1_pre_topc(A_561)
      | v2_struct_0(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_7929,plain,(
    ! [B_562] :
      ( m1_pre_topc(k1_tex_2('#skF_5',B_562),'#skF_5')
      | ~ m1_subset_1(B_562,k1_tarski('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7153,c_7924])).

tff(c_7938,plain,(
    ! [B_562] :
      ( m1_pre_topc(k1_tex_2('#skF_5',B_562),'#skF_5')
      | ~ m1_subset_1(B_562,k1_tarski('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7929])).

tff(c_7942,plain,(
    ! [B_563] :
      ( m1_pre_topc(k1_tex_2('#skF_5',B_563),'#skF_5')
      | ~ m1_subset_1(B_563,k1_tarski('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_7938])).

tff(c_7950,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_6'))),'#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6963,c_7942])).

tff(c_7963,plain,
    ( m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6900,c_7950])).

tff(c_7964,plain,(
    m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_7963])).

tff(c_7969,plain,
    ( l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_7964,c_40])).

tff(c_7972,plain,(
    l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7969])).

tff(c_7291,plain,(
    ! [B_500,A_501] :
      ( m1_subset_1(u1_struct_0(B_500),k1_zfmisc_1(u1_struct_0(A_501)))
      | ~ m1_pre_topc(B_500,A_501)
      | ~ l1_pre_topc(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7309,plain,(
    ! [B_500] :
      ( m1_subset_1(u1_struct_0(B_500),k1_zfmisc_1(k1_tarski('#skF_6')))
      | ~ m1_pre_topc(B_500,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7153,c_7291])).

tff(c_7315,plain,(
    ! [B_500] :
      ( m1_subset_1(u1_struct_0(B_500),k1_zfmisc_1(k1_tarski('#skF_6')))
      | ~ m1_pre_topc(B_500,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7309])).

tff(c_7012,plain,(
    ! [C_477,A_478,B_479] :
      ( r2_hidden(C_477,A_478)
      | ~ r2_hidden(C_477,B_479)
      | ~ m1_subset_1(B_479,k1_zfmisc_1(A_478)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_7245,plain,(
    ! [A_496,A_497] :
      ( r2_hidden('#skF_1'(A_496),A_497)
      | ~ m1_subset_1(A_496,k1_zfmisc_1(A_497))
      | v1_xboole_0(A_496) ) ),
    inference(resolution,[status(thm)],[c_4,c_7012])).

tff(c_7340,plain,(
    ! [A_504,A_505] :
      ( A_504 = '#skF_1'(A_505)
      | ~ m1_subset_1(A_505,k1_zfmisc_1(k1_tarski(A_504)))
      | v1_xboole_0(A_505) ) ),
    inference(resolution,[status(thm)],[c_7245,c_6])).

tff(c_7369,plain,(
    ! [B_506] :
      ( '#skF_1'(u1_struct_0(B_506)) = '#skF_6'
      | v1_xboole_0(u1_struct_0(B_506))
      | ~ m1_pre_topc(B_506,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7315,c_7340])).

tff(c_7482,plain,(
    ! [B_518] :
      ( ~ l1_struct_0(B_518)
      | v2_struct_0(B_518)
      | '#skF_1'(u1_struct_0(B_518)) = '#skF_6'
      | ~ m1_pre_topc(B_518,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7369,c_42])).

tff(c_10287,plain,(
    ! [B_697] :
      ( m1_subset_1('#skF_6',u1_struct_0(B_697))
      | v1_xboole_0(u1_struct_0(B_697))
      | ~ l1_struct_0(B_697)
      | v2_struct_0(B_697)
      | ~ m1_pre_topc(B_697,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7482,c_6963])).

tff(c_62,plain,(
    ! [A_45,B_46] :
      ( m1_pre_topc(k1_tex_2(A_45,B_46),A_45)
      | ~ m1_subset_1(B_46,u1_struct_0(A_45))
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_10320,plain,(
    ! [B_697] :
      ( m1_pre_topc(k1_tex_2(B_697,'#skF_6'),B_697)
      | ~ l1_pre_topc(B_697)
      | v1_xboole_0(u1_struct_0(B_697))
      | ~ l1_struct_0(B_697)
      | v2_struct_0(B_697)
      | ~ m1_pre_topc(B_697,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10287,c_62])).

tff(c_7940,plain,(
    ! [A_561] :
      ( m1_pre_topc(k1_tex_2(A_561,'#skF_1'(u1_struct_0(A_561))),A_561)
      | ~ l1_pre_topc(A_561)
      | v2_struct_0(A_561)
      | v1_xboole_0(u1_struct_0(A_561)) ) ),
    inference(resolution,[status(thm)],[c_6963,c_7924])).

tff(c_48,plain,(
    ! [B_32,A_30] :
      ( m1_subset_1(u1_struct_0(B_32),k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_34,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_9488,plain,(
    ! [A_649,A_650,A_651] :
      ( r2_hidden('#skF_1'(A_649),A_650)
      | ~ m1_subset_1(A_651,k1_zfmisc_1(A_650))
      | ~ m1_subset_1(A_649,k1_zfmisc_1(A_651))
      | v1_xboole_0(A_649) ) ),
    inference(resolution,[status(thm)],[c_7245,c_34])).

tff(c_11972,plain,(
    ! [A_758,B_759] :
      ( r2_hidden('#skF_1'(A_758),k1_tarski('#skF_6'))
      | ~ m1_subset_1(A_758,k1_zfmisc_1(u1_struct_0(B_759)))
      | v1_xboole_0(A_758)
      | ~ m1_pre_topc(B_759,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7315,c_9488])).

tff(c_18527,plain,(
    ! [B_988,A_989] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_988)),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(B_988))
      | ~ m1_pre_topc(A_989,'#skF_5')
      | ~ m1_pre_topc(B_988,A_989)
      | ~ l1_pre_topc(A_989) ) ),
    inference(resolution,[status(thm)],[c_48,c_11972])).

tff(c_18544,plain,(
    ! [B_988] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_988)),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(B_988))
      | ~ m1_pre_topc(B_988,k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
      | ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_1'(u1_struct_0('#skF_5'))))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_7940,c_18527])).

tff(c_18566,plain,(
    ! [B_988] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_988)),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(B_988))
      | ~ m1_pre_topc(B_988,k1_tex_2('#skF_5','#skF_6'))
      | v2_struct_0('#skF_5')
      | v1_xboole_0(k1_tarski('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_82,c_7972,c_6900,c_7153,c_6900,c_7153,c_18544])).

tff(c_18567,plain,(
    ! [B_988] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_988)),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(B_988))
      | ~ m1_pre_topc(B_988,k1_tex_2('#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_84,c_18566])).

tff(c_20337,plain,(
    ! [B_1030] :
      ( m1_pre_topc(k1_tex_2(B_1030,'#skF_6'),B_1030)
      | ~ l1_pre_topc(B_1030)
      | v1_xboole_0(u1_struct_0(B_1030))
      | ~ l1_struct_0(B_1030)
      | v2_struct_0(B_1030)
      | ~ m1_pre_topc(B_1030,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10287,c_62])).

tff(c_20364,plain,(
    ! [B_1031] :
      ( l1_pre_topc(k1_tex_2(B_1031,'#skF_6'))
      | ~ l1_pre_topc(B_1031)
      | v1_xboole_0(u1_struct_0(B_1031))
      | ~ l1_struct_0(B_1031)
      | v2_struct_0(B_1031)
      | ~ m1_pre_topc(B_1031,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20337,c_40])).

tff(c_20396,plain,(
    ! [B_1031] :
      ( l1_pre_topc(k1_tex_2(B_1031,'#skF_6'))
      | ~ l1_pre_topc(B_1031)
      | ~ l1_struct_0(B_1031)
      | v2_struct_0(B_1031)
      | ~ m1_pre_topc(B_1031,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_20364,c_42])).

tff(c_30,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [A_20] : ~ v1_subset_1(k2_subset_1(A_20),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_93,plain,(
    ! [A_20] : ~ v1_subset_1(A_20,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_36])).

tff(c_6961,plain,(
    ! [C_9] :
      ( m1_subset_1(C_9,k1_tarski(C_9))
      | v1_xboole_0(k1_tarski(C_9)) ) ),
    inference(resolution,[status(thm)],[c_8,c_6952])).

tff(c_6966,plain,(
    ! [C_9] : m1_subset_1(C_9,k1_tarski(C_9)) ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_6961])).

tff(c_7039,plain,(
    ! [C_9] :
      ( k6_domain_1(k1_tarski(C_9),C_9) = k1_tarski(C_9)
      | v1_xboole_0(k1_tarski(C_9)) ) ),
    inference(resolution,[status(thm)],[c_6966,c_7033])).

tff(c_7052,plain,(
    ! [C_9] : k6_domain_1(k1_tarski(C_9),C_9) = k1_tarski(C_9) ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_7039])).

tff(c_7525,plain,(
    ! [A_521,B_522] :
      ( v1_subset_1(k6_domain_1(A_521,B_522),A_521)
      | ~ m1_subset_1(B_522,A_521)
      | v1_zfmisc_1(A_521)
      | v1_xboole_0(A_521) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_7540,plain,(
    ! [C_9] :
      ( v1_subset_1(k1_tarski(C_9),k1_tarski(C_9))
      | ~ m1_subset_1(C_9,k1_tarski(C_9))
      | v1_zfmisc_1(k1_tarski(C_9))
      | v1_xboole_0(k1_tarski(C_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7052,c_7525])).

tff(c_7547,plain,(
    ! [C_9] :
      ( v1_subset_1(k1_tarski(C_9),k1_tarski(C_9))
      | v1_zfmisc_1(k1_tarski(C_9))
      | v1_xboole_0(k1_tarski(C_9)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6966,c_7540])).

tff(c_7548,plain,(
    ! [C_9] : v1_zfmisc_1(k1_tarski(C_9)) ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_93,c_7547])).

tff(c_7615,plain,(
    ! [A_531,B_532] :
      ( '#skF_2'(A_531,B_532) = A_531
      | r2_hidden('#skF_3'(A_531,B_532),B_532)
      | k1_tarski(A_531) = B_532 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7630,plain,(
    ! [A_531,A_5] :
      ( '#skF_3'(A_531,k1_tarski(A_5)) = A_5
      | '#skF_2'(A_531,k1_tarski(A_5)) = A_531
      | k1_tarski(A_531) = k1_tarski(A_5) ) ),
    inference(resolution,[status(thm)],[c_7615,c_6])).

tff(c_7306,plain,(
    ! [A_501] :
      ( m1_subset_1(k1_tarski('#skF_6'),k1_zfmisc_1(u1_struct_0(A_501)))
      | ~ m1_pre_topc('#skF_5',A_501)
      | ~ l1_pre_topc(A_501) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7153,c_7291])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( m1_subset_1(B_13,A_12)
      | ~ r2_hidden(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7803,plain,(
    ! [A_554,A_555] :
      ( m1_subset_1('#skF_1'(A_554),A_555)
      | v1_xboole_0(A_555)
      | ~ m1_subset_1(A_554,k1_zfmisc_1(A_555))
      | v1_xboole_0(A_554) ) ),
    inference(resolution,[status(thm)],[c_7245,c_22])).

tff(c_7862,plain,(
    ! [A_5,A_555] :
      ( m1_subset_1(A_5,A_555)
      | v1_xboole_0(A_555)
      | ~ m1_subset_1(k1_tarski(A_5),k1_zfmisc_1(A_555))
      | v1_xboole_0(k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6900,c_7803])).

tff(c_7887,plain,(
    ! [A_556,A_557] :
      ( m1_subset_1(A_556,A_557)
      | v1_xboole_0(A_557)
      | ~ m1_subset_1(k1_tarski(A_556),k1_zfmisc_1(A_557)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_7862])).

tff(c_8095,plain,(
    ! [A_568] :
      ( m1_subset_1('#skF_6',u1_struct_0(A_568))
      | v1_xboole_0(u1_struct_0(A_568))
      | ~ m1_pre_topc('#skF_5',A_568)
      | ~ l1_pre_topc(A_568) ) ),
    inference(resolution,[status(thm)],[c_7306,c_7887])).

tff(c_8116,plain,(
    ! [A_568] :
      ( m1_pre_topc(k1_tex_2(A_568,'#skF_6'),A_568)
      | v2_struct_0(A_568)
      | v1_xboole_0(u1_struct_0(A_568))
      | ~ m1_pre_topc('#skF_5',A_568)
      | ~ l1_pre_topc(A_568) ) ),
    inference(resolution,[status(thm)],[c_8095,c_62])).

tff(c_9168,plain,(
    ! [A_631,B_632] :
      ( m1_subset_1('#skF_3'(A_631,B_632),B_632)
      | v1_xboole_0(B_632)
      | '#skF_2'(A_631,B_632) = A_631
      | k1_tarski(A_631) = B_632 ) ),
    inference(resolution,[status(thm)],[c_7615,c_22])).

tff(c_9306,plain,(
    ! [A_45,A_631] :
      ( m1_pre_topc(k1_tex_2(A_45,'#skF_3'(A_631,u1_struct_0(A_45))),A_45)
      | ~ l1_pre_topc(A_45)
      | v2_struct_0(A_45)
      | v1_xboole_0(u1_struct_0(A_45))
      | '#skF_2'(A_631,u1_struct_0(A_45)) = A_631
      | u1_struct_0(A_45) = k1_tarski(A_631) ) ),
    inference(resolution,[status(thm)],[c_9168,c_62])).

tff(c_18530,plain,(
    ! [B_988,A_631] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_988)),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(B_988))
      | ~ m1_pre_topc(B_988,k1_tex_2('#skF_5','#skF_3'(A_631,u1_struct_0('#skF_5'))))
      | ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_3'(A_631,u1_struct_0('#skF_5'))))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | '#skF_2'(A_631,u1_struct_0('#skF_5')) = A_631
      | u1_struct_0('#skF_5') = k1_tarski(A_631) ) ),
    inference(resolution,[status(thm)],[c_9306,c_18527])).

tff(c_18554,plain,(
    ! [B_988,A_631] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_988)),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(B_988))
      | ~ m1_pre_topc(B_988,k1_tex_2('#skF_5','#skF_3'(A_631,k1_tarski('#skF_6'))))
      | ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_3'(A_631,k1_tarski('#skF_6'))))
      | v2_struct_0('#skF_5')
      | v1_xboole_0(k1_tarski('#skF_6'))
      | '#skF_2'(A_631,k1_tarski('#skF_6')) = A_631
      | k1_tarski(A_631) = k1_tarski('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7153,c_7153,c_7153,c_82,c_7153,c_7153,c_18530])).

tff(c_18618,plain,(
    ! [B_991,A_992] :
      ( r2_hidden('#skF_1'(u1_struct_0(B_991)),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(B_991))
      | ~ m1_pre_topc(B_991,k1_tex_2('#skF_5','#skF_3'(A_992,k1_tarski('#skF_6'))))
      | ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_3'(A_992,k1_tarski('#skF_6'))))
      | '#skF_2'(A_992,k1_tarski('#skF_6')) = A_992
      | k1_tarski(A_992) = k1_tarski('#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_84,c_18554])).

tff(c_19947,plain,(
    ! [A_1020] :
      ( r2_hidden('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_3'(A_1020,k1_tarski('#skF_6'))),'#skF_6'))),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_3'(A_1020,k1_tarski('#skF_6'))),'#skF_6')))
      | '#skF_2'(A_1020,k1_tarski('#skF_6')) = A_1020
      | k1_tarski(A_1020) = k1_tarski('#skF_6')
      | v2_struct_0(k1_tex_2('#skF_5','#skF_3'(A_1020,k1_tarski('#skF_6'))))
      | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_3'(A_1020,k1_tarski('#skF_6')))))
      | ~ m1_pre_topc('#skF_5',k1_tex_2('#skF_5','#skF_3'(A_1020,k1_tarski('#skF_6'))))
      | ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_3'(A_1020,k1_tarski('#skF_6')))) ) ),
    inference(resolution,[status(thm)],[c_8116,c_18618])).

tff(c_19968,plain,(
    ! [A_531] :
      ( r2_hidden('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))),k1_tarski('#skF_6'))
      | v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_3'(A_531,k1_tarski('#skF_6'))),'#skF_6')))
      | '#skF_2'(A_531,k1_tarski('#skF_6')) = A_531
      | k1_tarski(A_531) = k1_tarski('#skF_6')
      | v2_struct_0(k1_tex_2('#skF_5','#skF_3'(A_531,k1_tarski('#skF_6'))))
      | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_3'(A_531,k1_tarski('#skF_6')))))
      | ~ m1_pre_topc('#skF_5',k1_tex_2('#skF_5','#skF_3'(A_531,k1_tarski('#skF_6'))))
      | ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_3'(A_531,k1_tarski('#skF_6'))))
      | '#skF_2'(A_531,k1_tarski('#skF_6')) = A_531
      | k1_tarski(A_531) = k1_tarski('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7630,c_19947])).

tff(c_26896,plain,(
    r2_hidden('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_19968])).

tff(c_8862,plain,(
    ! [A_621,B_622] :
      ( v1_subset_1(k6_domain_1(A_621,B_622),A_621)
      | k6_domain_1(A_621,B_622) = A_621
      | ~ m1_subset_1(B_622,A_621)
      | v1_xboole_0(A_621) ) ),
    inference(resolution,[status(thm)],[c_7102,c_58])).

tff(c_74,plain,(
    ! [A_49,B_51] :
      ( ~ v1_zfmisc_1(A_49)
      | ~ v1_subset_1(k6_domain_1(A_49,B_51),A_49)
      | ~ m1_subset_1(B_51,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_8900,plain,(
    ! [A_623,B_624] :
      ( ~ v1_zfmisc_1(A_623)
      | k6_domain_1(A_623,B_624) = A_623
      | ~ m1_subset_1(B_624,A_623)
      | v1_xboole_0(A_623) ) ),
    inference(resolution,[status(thm)],[c_8862,c_74])).

tff(c_8965,plain,(
    ! [A_626] :
      ( ~ v1_zfmisc_1(A_626)
      | k6_domain_1(A_626,'#skF_1'(A_626)) = A_626
      | v1_xboole_0(A_626) ) ),
    inference(resolution,[status(thm)],[c_6963,c_8900])).

tff(c_7049,plain,(
    ! [A_1] :
      ( k6_domain_1(A_1,'#skF_1'(A_1)) = k1_tarski('#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_6963,c_7033])).

tff(c_9011,plain,(
    ! [A_627] :
      ( k1_tarski('#skF_1'(A_627)) = A_627
      | v1_xboole_0(A_627)
      | ~ v1_zfmisc_1(A_627)
      | v1_xboole_0(A_627) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8965,c_7049])).

tff(c_9073,plain,(
    ! [C_9,A_627] :
      ( C_9 = '#skF_1'(A_627)
      | ~ r2_hidden(C_9,A_627)
      | v1_xboole_0(A_627)
      | ~ v1_zfmisc_1(A_627)
      | v1_xboole_0(A_627) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9011,c_6])).

tff(c_26899,plain,
    ( '#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))) = '#skF_1'(k1_tarski('#skF_6'))
    | ~ v1_zfmisc_1(k1_tarski('#skF_6'))
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_26896,c_9073])).

tff(c_26922,plain,
    ( '#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))) = '#skF_6'
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7548,c_6900,c_26899])).

tff(c_26923,plain,(
    '#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_26922])).

tff(c_27145,plain,
    ( m1_subset_1('#skF_6',u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')))
    | v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_26923,c_6963])).

tff(c_38272,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_27145])).

tff(c_38497,plain,
    ( ~ l1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))
    | v2_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_38272,c_42])).

tff(c_38498,plain,(
    ~ l1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_38497])).

tff(c_38502,plain,(
    ~ l1_pre_topc(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_38498])).

tff(c_38544,plain,
    ( ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_20396,c_38502])).

tff(c_38553,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7964,c_7972,c_38544])).

tff(c_38554,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_7612,c_38553])).

tff(c_38565,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_38554])).

tff(c_38569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7972,c_38565])).

tff(c_38570,plain,(
    v2_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_38497])).

tff(c_72,plain,(
    ! [A_47,B_48] :
      ( ~ v2_struct_0(k1_tex_2(A_47,B_48))
      | ~ m1_subset_1(B_48,u1_struct_0(A_47))
      | ~ l1_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_10322,plain,(
    ! [B_697] :
      ( ~ v2_struct_0(k1_tex_2(B_697,'#skF_6'))
      | ~ l1_pre_topc(B_697)
      | v1_xboole_0(u1_struct_0(B_697))
      | ~ l1_struct_0(B_697)
      | v2_struct_0(B_697)
      | ~ m1_pre_topc(B_697,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10287,c_72])).

tff(c_38574,plain,
    ( ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_38570,c_10322])).

tff(c_38583,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7964,c_7972,c_38574])).

tff(c_38584,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_7612,c_38583])).

tff(c_38593,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_38584])).

tff(c_38731,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_38593])).

tff(c_38735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7972,c_38731])).

tff(c_38737,plain,(
    l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_38584])).

tff(c_38736,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_38584])).

tff(c_38759,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38736,c_42])).

tff(c_38789,plain,(
    v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38737,c_38759])).

tff(c_38791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7612,c_38789])).

tff(c_38793,plain,(
    ~ v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_27145])).

tff(c_38792,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_27145])).

tff(c_24,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7678,plain,(
    ! [B_538,A_539,A_540] :
      ( r2_hidden(B_538,A_539)
      | ~ m1_subset_1(A_540,k1_zfmisc_1(A_539))
      | ~ m1_subset_1(B_538,A_540)
      | v1_xboole_0(A_540) ) ),
    inference(resolution,[status(thm)],[c_24,c_7012])).

tff(c_7701,plain,(
    ! [B_538,A_30,B_32] :
      ( r2_hidden(B_538,u1_struct_0(A_30))
      | ~ m1_subset_1(B_538,u1_struct_0(B_32))
      | v1_xboole_0(u1_struct_0(B_32))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_48,c_7678])).

tff(c_38810,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_6',u1_struct_0(A_30))
      | v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')))
      | ~ m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'),A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(resolution,[status(thm)],[c_38792,c_7701])).

tff(c_39763,plain,(
    ! [A_1347] :
      ( r2_hidden('#skF_6',u1_struct_0(A_1347))
      | ~ m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'),A_1347)
      | ~ l1_pre_topc(A_1347) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38793,c_38810])).

tff(c_39767,plain,
    ( r2_hidden('#skF_6',u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10320,c_39763])).

tff(c_39778,plain,
    ( r2_hidden('#skF_6',u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7964,c_7972,c_39767])).

tff(c_39779,plain,
    ( r2_hidden('#skF_6',u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_7612,c_39778])).

tff(c_41105,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_39779])).

tff(c_41108,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_41105])).

tff(c_41112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7972,c_41108])).

tff(c_41114,plain,(
    l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_39779])).

tff(c_6803,plain,(
    v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_41113,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | r2_hidden('#skF_6',u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_39779])).

tff(c_41115,plain,(
    r2_hidden('#skF_6',u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_41113])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_41130,plain,(
    ~ v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_41115,c_2])).

tff(c_7642,plain,(
    ! [A_535,B_536] :
      ( v7_struct_0(k1_tex_2(A_535,B_536))
      | ~ m1_subset_1(B_536,u1_struct_0(A_535))
      | ~ l1_pre_topc(A_535)
      | v2_struct_0(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_7645,plain,(
    ! [B_536] :
      ( v7_struct_0(k1_tex_2('#skF_5',B_536))
      | ~ m1_subset_1(B_536,k1_tarski('#skF_6'))
      | ~ l1_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7153,c_7642])).

tff(c_7655,plain,(
    ! [B_536] :
      ( v7_struct_0(k1_tex_2('#skF_5',B_536))
      | ~ m1_subset_1(B_536,k1_tarski('#skF_6'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_7645])).

tff(c_7659,plain,(
    ! [B_537] :
      ( v7_struct_0(k1_tex_2('#skF_5',B_537))
      | ~ m1_subset_1(B_537,k1_tarski('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_7655])).

tff(c_7663,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_1'(k1_tarski('#skF_6'))))
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_6963,c_7659])).

tff(c_7673,plain,
    ( v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v1_xboole_0(k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6900,c_7663])).

tff(c_7674,plain,(
    v7_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_6808,c_7673])).

tff(c_7360,plain,(
    ! [B_500] :
      ( '#skF_1'(u1_struct_0(B_500)) = '#skF_6'
      | v1_xboole_0(u1_struct_0(B_500))
      | ~ m1_pre_topc(B_500,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_7315,c_7340])).

tff(c_41133,plain,
    ( '#skF_1'(u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) = '#skF_6'
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_7360,c_41130])).

tff(c_41136,plain,(
    '#skF_1'(u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7964,c_41133])).

tff(c_78,plain,(
    ! [A_55,B_57] :
      ( ~ v7_struct_0(A_55)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(A_55),B_57),u1_struct_0(A_55))
      | ~ m1_subset_1(B_57,u1_struct_0(A_55))
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_14890,plain,(
    ! [A_850,B_851] :
      ( ~ v7_struct_0(A_850)
      | ~ l1_struct_0(A_850)
      | v2_struct_0(A_850)
      | k6_domain_1(u1_struct_0(A_850),B_851) = u1_struct_0(A_850)
      | ~ m1_subset_1(B_851,u1_struct_0(A_850))
      | v1_xboole_0(u1_struct_0(A_850)) ) ),
    inference(resolution,[status(thm)],[c_8862,c_78])).

tff(c_16190,plain,(
    ! [A_897] :
      ( ~ v7_struct_0(A_897)
      | ~ l1_struct_0(A_897)
      | v2_struct_0(A_897)
      | k6_domain_1(u1_struct_0(A_897),'#skF_1'(u1_struct_0(A_897))) = u1_struct_0(A_897)
      | v1_xboole_0(u1_struct_0(A_897)) ) ),
    inference(resolution,[status(thm)],[c_6963,c_14890])).

tff(c_16244,plain,(
    ! [A_897] :
      ( ~ v7_struct_0(A_897)
      | ~ l1_struct_0(A_897)
      | v2_struct_0(A_897)
      | k1_tarski('#skF_1'(u1_struct_0(A_897))) = u1_struct_0(A_897)
      | v1_xboole_0(u1_struct_0(A_897))
      | v1_xboole_0(u1_struct_0(A_897)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7049,c_16190])).

tff(c_41253,plain,
    ( ~ v7_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_41136,c_16244])).

tff(c_41493,plain,
    ( v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6')
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41114,c_7674,c_41253])).

tff(c_41494,plain,(
    u1_struct_0(k1_tex_2('#skF_5','#skF_6')) = k1_tarski('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_41130,c_7612,c_41493])).

tff(c_8731,plain,(
    ! [B_608,A_609] :
      ( v1_subset_1(u1_struct_0(B_608),u1_struct_0(A_609))
      | ~ m1_subset_1(u1_struct_0(B_608),k1_zfmisc_1(u1_struct_0(A_609)))
      | ~ v1_tex_2(B_608,A_609)
      | ~ m1_pre_topc(B_608,A_609)
      | ~ l1_pre_topc(A_609) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8767,plain,(
    ! [B_612,A_613] :
      ( v1_subset_1(u1_struct_0(B_612),u1_struct_0(A_613))
      | ~ v1_tex_2(B_612,A_613)
      | ~ m1_pre_topc(B_612,A_613)
      | ~ l1_pre_topc(A_613) ) ),
    inference(resolution,[status(thm)],[c_48,c_8731])).

tff(c_8777,plain,(
    ! [B_612] :
      ( v1_subset_1(u1_struct_0(B_612),k1_tarski('#skF_6'))
      | ~ v1_tex_2(B_612,'#skF_5')
      | ~ m1_pre_topc(B_612,'#skF_5')
      | ~ l1_pre_topc('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7153,c_8767])).

tff(c_8780,plain,(
    ! [B_612] :
      ( v1_subset_1(u1_struct_0(B_612),k1_tarski('#skF_6'))
      | ~ v1_tex_2(B_612,'#skF_5')
      | ~ m1_pre_topc(B_612,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_8777])).

tff(c_41946,plain,
    ( v1_subset_1(k1_tarski('#skF_6'),k1_tarski('#skF_6'))
    | ~ v1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_5')
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_41494,c_8780])).

tff(c_42311,plain,(
    v1_subset_1(k1_tarski('#skF_6'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7964,c_6803,c_41946])).

tff(c_42313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_42311])).

tff(c_42314,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_41113])).

tff(c_42337,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42314,c_42])).

tff(c_42367,plain,(
    v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41114,c_42337])).

tff(c_42369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7612,c_42367])).

tff(c_42371,plain,(
    ~ r2_hidden('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_19968])).

tff(c_42462,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')))
    | ~ m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'),k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_18567,c_42371])).

tff(c_42649,plain,(
    ~ m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'),k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_42462])).

tff(c_42652,plain,
    ( ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_10320,c_42649])).

tff(c_42661,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7964,c_7972,c_42652])).

tff(c_42662,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_7612,c_42661])).

tff(c_42671,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_42662])).

tff(c_42674,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_42671])).

tff(c_42678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7972,c_42674])).

tff(c_42680,plain,(
    l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_42662])).

tff(c_42679,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_42662])).

tff(c_42700,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42679,c_42])).

tff(c_42727,plain,(
    v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42680,c_42700])).

tff(c_42729,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7612,c_42727])).

tff(c_42731,plain,(
    m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'),k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_42462])).

tff(c_42816,plain,
    ( l1_pre_topc(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))
    | ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_42731,c_40])).

tff(c_42824,plain,(
    l1_pre_topc(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7972,c_42816])).

tff(c_42730,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_42462])).

tff(c_42808,plain,
    ( ~ l1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6'))
    | v2_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_42730,c_42])).

tff(c_42859,plain,(
    ~ l1_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_42808])).

tff(c_42862,plain,(
    ~ l1_pre_topc(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_42859])).

tff(c_42866,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42824,c_42862])).

tff(c_42867,plain,(
    v2_struct_0(k1_tex_2(k1_tex_2('#skF_5','#skF_6'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_42808])).

tff(c_42871,plain,
    ( ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6'))
    | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | ~ m1_pre_topc(k1_tex_2('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_42867,c_10322])).

tff(c_42880,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7964,c_7972,c_42871])).

tff(c_42881,plain,
    ( v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6')))
    | ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_7612,c_42880])).

tff(c_42890,plain,(
    ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_42881])).

tff(c_42996,plain,(
    ~ l1_pre_topc(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_42890])).

tff(c_43000,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7972,c_42996])).

tff(c_43002,plain,(
    l1_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_42881])).

tff(c_43001,plain,(
    v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_42881])).

tff(c_43022,plain,
    ( ~ l1_struct_0(k1_tex_2('#skF_5','#skF_6'))
    | v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_43001,c_42])).

tff(c_43049,plain,(
    v2_struct_0(k1_tex_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43002,c_43022])).

tff(c_43051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7612,c_43049])).

tff(c_43053,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_6924])).

tff(c_43056,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_43053,c_42])).

tff(c_43059,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_43056])).

tff(c_43062,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_43059])).

tff(c_43066,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_43062])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n020.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 14:20:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.36/10.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.52/10.63  
% 19.52/10.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.52/10.63  %$ v1_tex_2 > v1_subset_1 > r2_hidden > m1_subset_1 > m1_pre_topc > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > v1_pre_topc > l1_struct_0 > l1_pre_topc > k6_domain_1 > k2_tarski > k1_tex_2 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 19.52/10.63  
% 19.52/10.63  %Foreground sorts:
% 19.52/10.63  
% 19.52/10.63  
% 19.52/10.63  %Background operators:
% 19.52/10.63  
% 19.52/10.63  
% 19.52/10.63  %Foreground operators:
% 19.52/10.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 19.52/10.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.52/10.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.52/10.63  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 19.52/10.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 19.52/10.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 19.52/10.63  tff(v1_tex_2, type, v1_tex_2: ($i * $i) > $o).
% 19.52/10.63  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 19.52/10.63  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 19.52/10.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 19.52/10.63  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 19.52/10.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.52/10.63  tff('#skF_5', type, '#skF_5': $i).
% 19.52/10.63  tff('#skF_6', type, '#skF_6': $i).
% 19.52/10.63  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 19.52/10.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.52/10.63  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 19.52/10.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.52/10.63  tff(k1_tex_2, type, k1_tex_2: ($i * $i) > $i).
% 19.52/10.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.52/10.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.52/10.63  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 19.52/10.63  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 19.52/10.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 19.52/10.63  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 19.52/10.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.52/10.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 19.52/10.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.52/10.63  
% 19.52/10.67  tff(f_208, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (v1_tex_2(k1_tex_2(A, B), A) <=> v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tex_2)).
% 19.52/10.67  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 19.52/10.67  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 19.52/10.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 19.52/10.67  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 19.52/10.67  tff(f_104, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 19.52/10.67  tff(f_171, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 19.52/10.67  tff(f_146, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v1_pre_topc(k1_tex_2(A, B))) & m1_pre_topc(k1_tex_2(A, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tex_2)).
% 19.52/10.67  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_tex_2(B, A) <=> (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => v1_subset_1(C, u1_struct_0(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tex_2)).
% 19.52/10.67  tff(f_132, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 19.52/10.67  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 19.52/10.67  tff(f_160, axiom, (![A, B]: (((~v2_struct_0(A) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => ((~v2_struct_0(k1_tex_2(A, B)) & v7_struct_0(k1_tex_2(A, B))) & v1_pre_topc(k1_tex_2(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_tex_2)).
% 19.52/10.67  tff(f_90, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 19.52/10.67  tff(f_182, axiom, (![A]: ((~v1_xboole_0(A) & ~v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, A) => v1_subset_1(k6_domain_1(A, B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tex_2)).
% 19.52/10.67  tff(f_195, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_tex_2)).
% 19.52/10.67  tff(f_97, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 19.52/10.67  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 19.52/10.67  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 19.52/10.67  tff(f_59, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 19.52/10.67  tff(f_71, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 19.52/10.67  tff(c_82, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 19.52/10.67  tff(c_38, plain, (![A_21]: (l1_struct_0(A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.52/10.67  tff(c_84, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 19.52/10.67  tff(c_8, plain, (![C_9]: (r2_hidden(C_9, k1_tarski(C_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 19.52/10.67  tff(c_6804, plain, (![B_437, A_438]: (~r2_hidden(B_437, A_438) | ~v1_xboole_0(A_438))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.52/10.67  tff(c_6808, plain, (![C_9]: (~v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_8, c_6804])).
% 19.52/10.67  tff(c_6890, plain, (![A_457]: (v1_xboole_0(A_457) | r2_hidden('#skF_1'(A_457), A_457))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.52/10.67  tff(c_6, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 19.52/10.67  tff(c_6894, plain, (![A_5]: ('#skF_1'(k1_tarski(A_5))=A_5 | v1_xboole_0(k1_tarski(A_5)))), inference(resolution, [status(thm)], [c_6890, c_6])).
% 19.52/10.67  tff(c_6900, plain, (![A_5]: ('#skF_1'(k1_tarski(A_5))=A_5)), inference(negUnitSimplification, [status(thm)], [c_6808, c_6894])).
% 19.52/10.67  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.52/10.67  tff(c_6952, plain, (![B_471, A_472]: (m1_subset_1(B_471, A_472) | ~r2_hidden(B_471, A_472) | v1_xboole_0(A_472))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.52/10.67  tff(c_6963, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_6952])).
% 19.52/10.67  tff(c_80, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 19.52/10.67  tff(c_6917, plain, (![B_460, A_461]: (v1_xboole_0(B_460) | ~m1_subset_1(B_460, A_461) | ~v1_xboole_0(A_461))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.52/10.67  tff(c_6924, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_6917])).
% 19.52/10.67  tff(c_6926, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_6924])).
% 19.52/10.67  tff(c_7033, plain, (![A_482, B_483]: (k6_domain_1(A_482, B_483)=k1_tarski(B_483) | ~m1_subset_1(B_483, A_482) | v1_xboole_0(A_482))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.52/10.67  tff(c_7045, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_7033])).
% 19.52/10.67  tff(c_7056, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_6926, c_7045])).
% 19.52/10.67  tff(c_158, plain, (![B_75, A_76]: (v1_xboole_0(B_75) | ~m1_subset_1(B_75, A_76) | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.52/10.67  tff(c_169, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_158])).
% 19.52/10.67  tff(c_172, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_169])).
% 19.52/10.67  tff(c_275, plain, (![A_96, B_97]: (k6_domain_1(A_96, B_97)=k1_tarski(B_97) | ~m1_subset_1(B_97, A_96) | v1_xboole_0(A_96))), inference(cnfTransformation, [status(thm)], [f_104])).
% 19.52/10.67  tff(c_287, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_80, c_275])).
% 19.52/10.67  tff(c_298, plain, (k6_domain_1(u1_struct_0('#skF_5'), '#skF_6')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_172, c_287])).
% 19.52/10.67  tff(c_86, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5')) | ~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_208])).
% 19.52/10.67  tff(c_109, plain, (~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 19.52/10.67  tff(c_92, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 19.52/10.67  tff(c_171, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_109, c_92])).
% 19.52/10.67  tff(c_300, plain, (v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_298, c_171])).
% 19.52/10.67  tff(c_1921, plain, (![A_202, B_203]: (~v1_zfmisc_1(A_202) | ~v1_subset_1(k6_domain_1(A_202, B_203), A_202) | ~m1_subset_1(B_203, A_202) | v1_xboole_0(A_202))), inference(cnfTransformation, [status(thm)], [f_171])).
% 19.52/10.67  tff(c_1942, plain, (~v1_zfmisc_1(u1_struct_0('#skF_5')) | ~v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_298, c_1921])).
% 19.52/10.67  tff(c_1955, plain, (~v1_zfmisc_1(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_300, c_1942])).
% 19.52/10.67  tff(c_1956, plain, (~v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_172, c_1955])).
% 19.52/10.67  tff(c_2226, plain, (![A_226, B_227]: (m1_pre_topc(k1_tex_2(A_226, B_227), A_226) | ~m1_subset_1(B_227, u1_struct_0(A_226)) | ~l1_pre_topc(A_226) | v2_struct_0(A_226))), inference(cnfTransformation, [status(thm)], [f_146])).
% 19.52/10.67  tff(c_2238, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_80, c_2226])).
% 19.52/10.67  tff(c_2248, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2238])).
% 19.52/10.67  tff(c_2249, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_2248])).
% 19.52/10.67  tff(c_2772, plain, (![A_257, B_258]: (m1_subset_1('#skF_4'(A_257, B_258), k1_zfmisc_1(u1_struct_0(A_257))) | v1_tex_2(B_258, A_257) | ~m1_pre_topc(B_258, A_257) | ~l1_pre_topc(A_257))), inference(cnfTransformation, [status(thm)], [f_125])).
% 19.52/10.67  tff(c_58, plain, (![B_44, A_43]: (v1_subset_1(B_44, A_43) | B_44=A_43 | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_132])).
% 19.52/10.67  tff(c_6596, plain, (![A_429, B_430]: (v1_subset_1('#skF_4'(A_429, B_430), u1_struct_0(A_429)) | u1_struct_0(A_429)='#skF_4'(A_429, B_430) | v1_tex_2(B_430, A_429) | ~m1_pre_topc(B_430, A_429) | ~l1_pre_topc(A_429))), inference(resolution, [status(thm)], [c_2772, c_58])).
% 19.52/10.67  tff(c_52, plain, (![A_33, B_39]: (~v1_subset_1('#skF_4'(A_33, B_39), u1_struct_0(A_33)) | v1_tex_2(B_39, A_33) | ~m1_pre_topc(B_39, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_125])).
% 19.52/10.67  tff(c_6756, plain, (![A_434, B_435]: (u1_struct_0(A_434)='#skF_4'(A_434, B_435) | v1_tex_2(B_435, A_434) | ~m1_pre_topc(B_435, A_434) | ~l1_pre_topc(A_434))), inference(resolution, [status(thm)], [c_6596, c_52])).
% 19.52/10.67  tff(c_6763, plain, ('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_6756, c_109])).
% 19.52/10.67  tff(c_6767, plain, ('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))=u1_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2249, c_6763])).
% 19.52/10.67  tff(c_40, plain, (![B_24, A_22]: (l1_pre_topc(B_24) | ~m1_pre_topc(B_24, A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 19.52/10.67  tff(c_2252, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2249, c_40])).
% 19.52/10.67  tff(c_2255, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2252])).
% 19.52/10.67  tff(c_1897, plain, (![A_198, B_199]: (~v2_struct_0(k1_tex_2(A_198, B_199)) | ~m1_subset_1(B_199, u1_struct_0(A_198)) | ~l1_pre_topc(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_160])).
% 19.52/10.67  tff(c_1908, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_80, c_1897])).
% 19.52/10.67  tff(c_1913, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1908])).
% 19.52/10.67  tff(c_1914, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_84, c_1913])).
% 19.52/10.67  tff(c_2419, plain, (![B_239, A_240]: (u1_struct_0(B_239)='#skF_4'(A_240, B_239) | v1_tex_2(B_239, A_240) | ~m1_pre_topc(B_239, A_240) | ~l1_pre_topc(A_240))), inference(cnfTransformation, [status(thm)], [f_125])).
% 19.52/10.67  tff(c_2422, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2419, c_109])).
% 19.52/10.67  tff(c_2425, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))='#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2249, c_2422])).
% 19.52/10.67  tff(c_42, plain, (![A_25]: (~v1_xboole_0(u1_struct_0(A_25)) | ~l1_struct_0(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_90])).
% 19.52/10.67  tff(c_2459, plain, (~v1_xboole_0('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2425, c_42])).
% 19.52/10.67  tff(c_2486, plain, (~v1_xboole_0('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_1914, c_2459])).
% 19.52/10.67  tff(c_2488, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_2486])).
% 19.52/10.67  tff(c_2491, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_2488])).
% 19.52/10.67  tff(c_2495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2255, c_2491])).
% 19.52/10.67  tff(c_2496, plain, (~v1_xboole_0('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_2486])).
% 19.52/10.67  tff(c_194, plain, (![B_85, A_86]: (m1_subset_1(B_85, A_86) | ~r2_hidden(B_85, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.52/10.67  tff(c_205, plain, (![A_1]: (m1_subset_1('#skF_1'(A_1), A_1) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_194])).
% 19.52/10.67  tff(c_76, plain, (![A_52, B_54]: (v1_subset_1(k6_domain_1(A_52, B_54), A_52) | ~m1_subset_1(B_54, A_52) | v1_zfmisc_1(A_52) | v1_xboole_0(A_52))), inference(cnfTransformation, [status(thm)], [f_182])).
% 19.52/10.67  tff(c_2497, plain, (l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_2486])).
% 19.52/10.67  tff(c_584, plain, (![A_116, B_117]: (v7_struct_0(k1_tex_2(A_116, B_117)) | ~m1_subset_1(B_117, u1_struct_0(A_116)) | ~l1_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_160])).
% 19.52/10.67  tff(c_595, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_80, c_584])).
% 19.52/10.67  tff(c_600, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_595])).
% 19.52/10.67  tff(c_601, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_84, c_600])).
% 19.52/10.67  tff(c_2941, plain, (![A_264, B_265]: (~v7_struct_0(A_264) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_264), B_265), u1_struct_0(A_264)) | ~m1_subset_1(B_265, u1_struct_0(A_264)) | ~l1_struct_0(A_264) | v2_struct_0(A_264))), inference(cnfTransformation, [status(thm)], [f_195])).
% 19.52/10.67  tff(c_2944, plain, (![B_265]: (~v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~v1_subset_1(k6_domain_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')), B_265), u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~m1_subset_1(B_265, u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2425, c_2941])).
% 19.52/10.67  tff(c_2960, plain, (![B_265]: (~v1_subset_1(k6_domain_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')), B_265), '#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~m1_subset_1(B_265, '#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2497, c_2425, c_2425, c_601, c_2944])).
% 19.52/10.67  tff(c_3177, plain, (![B_287]: (~v1_subset_1(k6_domain_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')), B_287), '#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | ~m1_subset_1(B_287, '#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_1914, c_2960])).
% 19.52/10.67  tff(c_3184, plain, (![B_54]: (~m1_subset_1(B_54, '#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | v1_zfmisc_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_76, c_3177])).
% 19.52/10.67  tff(c_3192, plain, (![B_54]: (~m1_subset_1(B_54, '#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))) | v1_zfmisc_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_2496, c_3184])).
% 19.52/10.67  tff(c_3195, plain, (![B_288]: (~m1_subset_1(B_288, '#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6'))))), inference(splitLeft, [status(thm)], [c_3192])).
% 19.52/10.67  tff(c_3203, plain, (v1_xboole_0('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_205, c_3195])).
% 19.52/10.67  tff(c_3214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2496, c_3203])).
% 19.52/10.67  tff(c_3215, plain, (v1_zfmisc_1('#skF_4'('#skF_5', k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_3192])).
% 19.52/10.67  tff(c_6771, plain, (v1_zfmisc_1(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_6767, c_3215])).
% 19.52/10.67  tff(c_6785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1956, c_6771])).
% 19.52/10.67  tff(c_6787, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_169])).
% 19.52/10.67  tff(c_6791, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_6787, c_42])).
% 19.52/10.67  tff(c_6794, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_6791])).
% 19.52/10.67  tff(c_6797, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_38, c_6794])).
% 19.52/10.67  tff(c_6801, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_6797])).
% 19.52/10.67  tff(c_6802, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_5'), '#skF_6'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_86])).
% 19.52/10.67  tff(c_7058, plain, (~v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_7056, c_6802])).
% 19.52/10.67  tff(c_7102, plain, (![A_487, B_488]: (m1_subset_1(k6_domain_1(A_487, B_488), k1_zfmisc_1(A_487)) | ~m1_subset_1(B_488, A_487) | v1_xboole_0(A_487))), inference(cnfTransformation, [status(thm)], [f_97])).
% 19.52/10.67  tff(c_7123, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7056, c_7102])).
% 19.52/10.67  tff(c_7135, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_7123])).
% 19.52/10.67  tff(c_7136, plain, (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_6926, c_7135])).
% 19.52/10.67  tff(c_7145, plain, (v1_subset_1(k1_tarski('#skF_6'), u1_struct_0('#skF_5')) | u1_struct_0('#skF_5')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_7136, c_58])).
% 19.52/10.67  tff(c_7153, plain, (u1_struct_0('#skF_5')=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_7058, c_7145])).
% 19.52/10.67  tff(c_7580, plain, (![A_528, B_529]: (~v2_struct_0(k1_tex_2(A_528, B_529)) | ~m1_subset_1(B_529, u1_struct_0(A_528)) | ~l1_pre_topc(A_528) | v2_struct_0(A_528))), inference(cnfTransformation, [status(thm)], [f_160])).
% 19.52/10.67  tff(c_7583, plain, (![B_529]: (~v2_struct_0(k1_tex_2('#skF_5', B_529)) | ~m1_subset_1(B_529, k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7153, c_7580])).
% 19.52/10.67  tff(c_7593, plain, (![B_529]: (~v2_struct_0(k1_tex_2('#skF_5', B_529)) | ~m1_subset_1(B_529, k1_tarski('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7583])).
% 19.52/10.67  tff(c_7597, plain, (![B_530]: (~v2_struct_0(k1_tex_2('#skF_5', B_530)) | ~m1_subset_1(B_530, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_84, c_7593])).
% 19.52/10.67  tff(c_7601, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_6')))) | v1_xboole_0(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_6963, c_7597])).
% 19.52/10.67  tff(c_7611, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6900, c_7601])).
% 19.52/10.67  tff(c_7612, plain, (~v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_6808, c_7611])).
% 19.52/10.67  tff(c_7924, plain, (![A_561, B_562]: (m1_pre_topc(k1_tex_2(A_561, B_562), A_561) | ~m1_subset_1(B_562, u1_struct_0(A_561)) | ~l1_pre_topc(A_561) | v2_struct_0(A_561))), inference(cnfTransformation, [status(thm)], [f_146])).
% 19.52/10.67  tff(c_7929, plain, (![B_562]: (m1_pre_topc(k1_tex_2('#skF_5', B_562), '#skF_5') | ~m1_subset_1(B_562, k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7153, c_7924])).
% 19.52/10.67  tff(c_7938, plain, (![B_562]: (m1_pre_topc(k1_tex_2('#skF_5', B_562), '#skF_5') | ~m1_subset_1(B_562, k1_tarski('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7929])).
% 19.52/10.67  tff(c_7942, plain, (![B_563]: (m1_pre_topc(k1_tex_2('#skF_5', B_563), '#skF_5') | ~m1_subset_1(B_563, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_84, c_7938])).
% 19.52/10.67  tff(c_7950, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_6'))), '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_6963, c_7942])).
% 19.52/10.67  tff(c_7963, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6900, c_7950])).
% 19.52/10.67  tff(c_7964, plain, (m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_6808, c_7963])).
% 19.52/10.67  tff(c_7969, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_7964, c_40])).
% 19.52/10.67  tff(c_7972, plain, (l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7969])).
% 19.52/10.67  tff(c_7291, plain, (![B_500, A_501]: (m1_subset_1(u1_struct_0(B_500), k1_zfmisc_1(u1_struct_0(A_501))) | ~m1_pre_topc(B_500, A_501) | ~l1_pre_topc(A_501))), inference(cnfTransformation, [status(thm)], [f_111])).
% 19.52/10.67  tff(c_7309, plain, (![B_500]: (m1_subset_1(u1_struct_0(B_500), k1_zfmisc_1(k1_tarski('#skF_6'))) | ~m1_pre_topc(B_500, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7153, c_7291])).
% 19.52/10.67  tff(c_7315, plain, (![B_500]: (m1_subset_1(u1_struct_0(B_500), k1_zfmisc_1(k1_tarski('#skF_6'))) | ~m1_pre_topc(B_500, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7309])).
% 19.52/10.67  tff(c_7012, plain, (![C_477, A_478, B_479]: (r2_hidden(C_477, A_478) | ~r2_hidden(C_477, B_479) | ~m1_subset_1(B_479, k1_zfmisc_1(A_478)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 19.52/10.67  tff(c_7245, plain, (![A_496, A_497]: (r2_hidden('#skF_1'(A_496), A_497) | ~m1_subset_1(A_496, k1_zfmisc_1(A_497)) | v1_xboole_0(A_496))), inference(resolution, [status(thm)], [c_4, c_7012])).
% 19.52/10.67  tff(c_7340, plain, (![A_504, A_505]: (A_504='#skF_1'(A_505) | ~m1_subset_1(A_505, k1_zfmisc_1(k1_tarski(A_504))) | v1_xboole_0(A_505))), inference(resolution, [status(thm)], [c_7245, c_6])).
% 19.52/10.67  tff(c_7369, plain, (![B_506]: ('#skF_1'(u1_struct_0(B_506))='#skF_6' | v1_xboole_0(u1_struct_0(B_506)) | ~m1_pre_topc(B_506, '#skF_5'))), inference(resolution, [status(thm)], [c_7315, c_7340])).
% 19.52/10.67  tff(c_7482, plain, (![B_518]: (~l1_struct_0(B_518) | v2_struct_0(B_518) | '#skF_1'(u1_struct_0(B_518))='#skF_6' | ~m1_pre_topc(B_518, '#skF_5'))), inference(resolution, [status(thm)], [c_7369, c_42])).
% 19.52/10.67  tff(c_10287, plain, (![B_697]: (m1_subset_1('#skF_6', u1_struct_0(B_697)) | v1_xboole_0(u1_struct_0(B_697)) | ~l1_struct_0(B_697) | v2_struct_0(B_697) | ~m1_pre_topc(B_697, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7482, c_6963])).
% 19.52/10.67  tff(c_62, plain, (![A_45, B_46]: (m1_pre_topc(k1_tex_2(A_45, B_46), A_45) | ~m1_subset_1(B_46, u1_struct_0(A_45)) | ~l1_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_146])).
% 19.52/10.67  tff(c_10320, plain, (![B_697]: (m1_pre_topc(k1_tex_2(B_697, '#skF_6'), B_697) | ~l1_pre_topc(B_697) | v1_xboole_0(u1_struct_0(B_697)) | ~l1_struct_0(B_697) | v2_struct_0(B_697) | ~m1_pre_topc(B_697, '#skF_5'))), inference(resolution, [status(thm)], [c_10287, c_62])).
% 19.52/10.67  tff(c_7940, plain, (![A_561]: (m1_pre_topc(k1_tex_2(A_561, '#skF_1'(u1_struct_0(A_561))), A_561) | ~l1_pre_topc(A_561) | v2_struct_0(A_561) | v1_xboole_0(u1_struct_0(A_561)))), inference(resolution, [status(thm)], [c_6963, c_7924])).
% 19.52/10.67  tff(c_48, plain, (![B_32, A_30]: (m1_subset_1(u1_struct_0(B_32), k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_111])).
% 19.52/10.67  tff(c_34, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 19.52/10.67  tff(c_9488, plain, (![A_649, A_650, A_651]: (r2_hidden('#skF_1'(A_649), A_650) | ~m1_subset_1(A_651, k1_zfmisc_1(A_650)) | ~m1_subset_1(A_649, k1_zfmisc_1(A_651)) | v1_xboole_0(A_649))), inference(resolution, [status(thm)], [c_7245, c_34])).
% 19.52/10.67  tff(c_11972, plain, (![A_758, B_759]: (r2_hidden('#skF_1'(A_758), k1_tarski('#skF_6')) | ~m1_subset_1(A_758, k1_zfmisc_1(u1_struct_0(B_759))) | v1_xboole_0(A_758) | ~m1_pre_topc(B_759, '#skF_5'))), inference(resolution, [status(thm)], [c_7315, c_9488])).
% 19.52/10.67  tff(c_18527, plain, (![B_988, A_989]: (r2_hidden('#skF_1'(u1_struct_0(B_988)), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(B_988)) | ~m1_pre_topc(A_989, '#skF_5') | ~m1_pre_topc(B_988, A_989) | ~l1_pre_topc(A_989))), inference(resolution, [status(thm)], [c_48, c_11972])).
% 19.52/10.67  tff(c_18544, plain, (![B_988]: (r2_hidden('#skF_1'(u1_struct_0(B_988)), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(B_988)) | ~m1_pre_topc(B_988, k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc(k1_tex_2('#skF_5', '#skF_1'(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_7940, c_18527])).
% 19.52/10.67  tff(c_18566, plain, (![B_988]: (r2_hidden('#skF_1'(u1_struct_0(B_988)), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(B_988)) | ~m1_pre_topc(B_988, k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_82, c_7972, c_6900, c_7153, c_6900, c_7153, c_18544])).
% 19.52/10.67  tff(c_18567, plain, (![B_988]: (r2_hidden('#skF_1'(u1_struct_0(B_988)), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(B_988)) | ~m1_pre_topc(B_988, k1_tex_2('#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_6808, c_84, c_18566])).
% 19.52/10.67  tff(c_20337, plain, (![B_1030]: (m1_pre_topc(k1_tex_2(B_1030, '#skF_6'), B_1030) | ~l1_pre_topc(B_1030) | v1_xboole_0(u1_struct_0(B_1030)) | ~l1_struct_0(B_1030) | v2_struct_0(B_1030) | ~m1_pre_topc(B_1030, '#skF_5'))), inference(resolution, [status(thm)], [c_10287, c_62])).
% 19.52/10.67  tff(c_20364, plain, (![B_1031]: (l1_pre_topc(k1_tex_2(B_1031, '#skF_6')) | ~l1_pre_topc(B_1031) | v1_xboole_0(u1_struct_0(B_1031)) | ~l1_struct_0(B_1031) | v2_struct_0(B_1031) | ~m1_pre_topc(B_1031, '#skF_5'))), inference(resolution, [status(thm)], [c_20337, c_40])).
% 19.52/10.67  tff(c_20396, plain, (![B_1031]: (l1_pre_topc(k1_tex_2(B_1031, '#skF_6')) | ~l1_pre_topc(B_1031) | ~l1_struct_0(B_1031) | v2_struct_0(B_1031) | ~m1_pre_topc(B_1031, '#skF_5'))), inference(resolution, [status(thm)], [c_20364, c_42])).
% 19.52/10.67  tff(c_30, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_59])).
% 19.52/10.67  tff(c_36, plain, (![A_20]: (~v1_subset_1(k2_subset_1(A_20), A_20))), inference(cnfTransformation, [status(thm)], [f_71])).
% 19.52/10.67  tff(c_93, plain, (![A_20]: (~v1_subset_1(A_20, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_36])).
% 19.52/10.67  tff(c_6961, plain, (![C_9]: (m1_subset_1(C_9, k1_tarski(C_9)) | v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_8, c_6952])).
% 19.52/10.67  tff(c_6966, plain, (![C_9]: (m1_subset_1(C_9, k1_tarski(C_9)))), inference(negUnitSimplification, [status(thm)], [c_6808, c_6961])).
% 19.52/10.67  tff(c_7039, plain, (![C_9]: (k6_domain_1(k1_tarski(C_9), C_9)=k1_tarski(C_9) | v1_xboole_0(k1_tarski(C_9)))), inference(resolution, [status(thm)], [c_6966, c_7033])).
% 19.52/10.67  tff(c_7052, plain, (![C_9]: (k6_domain_1(k1_tarski(C_9), C_9)=k1_tarski(C_9))), inference(negUnitSimplification, [status(thm)], [c_6808, c_7039])).
% 19.52/10.67  tff(c_7525, plain, (![A_521, B_522]: (v1_subset_1(k6_domain_1(A_521, B_522), A_521) | ~m1_subset_1(B_522, A_521) | v1_zfmisc_1(A_521) | v1_xboole_0(A_521))), inference(cnfTransformation, [status(thm)], [f_182])).
% 19.52/10.67  tff(c_7540, plain, (![C_9]: (v1_subset_1(k1_tarski(C_9), k1_tarski(C_9)) | ~m1_subset_1(C_9, k1_tarski(C_9)) | v1_zfmisc_1(k1_tarski(C_9)) | v1_xboole_0(k1_tarski(C_9)))), inference(superposition, [status(thm), theory('equality')], [c_7052, c_7525])).
% 19.52/10.67  tff(c_7547, plain, (![C_9]: (v1_subset_1(k1_tarski(C_9), k1_tarski(C_9)) | v1_zfmisc_1(k1_tarski(C_9)) | v1_xboole_0(k1_tarski(C_9)))), inference(demodulation, [status(thm), theory('equality')], [c_6966, c_7540])).
% 19.52/10.67  tff(c_7548, plain, (![C_9]: (v1_zfmisc_1(k1_tarski(C_9)))), inference(negUnitSimplification, [status(thm)], [c_6808, c_93, c_7547])).
% 19.52/10.67  tff(c_7615, plain, (![A_531, B_532]: ('#skF_2'(A_531, B_532)=A_531 | r2_hidden('#skF_3'(A_531, B_532), B_532) | k1_tarski(A_531)=B_532)), inference(cnfTransformation, [status(thm)], [f_38])).
% 19.52/10.67  tff(c_7630, plain, (![A_531, A_5]: ('#skF_3'(A_531, k1_tarski(A_5))=A_5 | '#skF_2'(A_531, k1_tarski(A_5))=A_531 | k1_tarski(A_531)=k1_tarski(A_5))), inference(resolution, [status(thm)], [c_7615, c_6])).
% 19.52/10.67  tff(c_7306, plain, (![A_501]: (m1_subset_1(k1_tarski('#skF_6'), k1_zfmisc_1(u1_struct_0(A_501))) | ~m1_pre_topc('#skF_5', A_501) | ~l1_pre_topc(A_501))), inference(superposition, [status(thm), theory('equality')], [c_7153, c_7291])).
% 19.52/10.67  tff(c_22, plain, (![B_13, A_12]: (m1_subset_1(B_13, A_12) | ~r2_hidden(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.52/10.67  tff(c_7803, plain, (![A_554, A_555]: (m1_subset_1('#skF_1'(A_554), A_555) | v1_xboole_0(A_555) | ~m1_subset_1(A_554, k1_zfmisc_1(A_555)) | v1_xboole_0(A_554))), inference(resolution, [status(thm)], [c_7245, c_22])).
% 19.52/10.67  tff(c_7862, plain, (![A_5, A_555]: (m1_subset_1(A_5, A_555) | v1_xboole_0(A_555) | ~m1_subset_1(k1_tarski(A_5), k1_zfmisc_1(A_555)) | v1_xboole_0(k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6900, c_7803])).
% 19.52/10.67  tff(c_7887, plain, (![A_556, A_557]: (m1_subset_1(A_556, A_557) | v1_xboole_0(A_557) | ~m1_subset_1(k1_tarski(A_556), k1_zfmisc_1(A_557)))), inference(negUnitSimplification, [status(thm)], [c_6808, c_7862])).
% 19.52/10.67  tff(c_8095, plain, (![A_568]: (m1_subset_1('#skF_6', u1_struct_0(A_568)) | v1_xboole_0(u1_struct_0(A_568)) | ~m1_pre_topc('#skF_5', A_568) | ~l1_pre_topc(A_568))), inference(resolution, [status(thm)], [c_7306, c_7887])).
% 19.52/10.67  tff(c_8116, plain, (![A_568]: (m1_pre_topc(k1_tex_2(A_568, '#skF_6'), A_568) | v2_struct_0(A_568) | v1_xboole_0(u1_struct_0(A_568)) | ~m1_pre_topc('#skF_5', A_568) | ~l1_pre_topc(A_568))), inference(resolution, [status(thm)], [c_8095, c_62])).
% 19.52/10.67  tff(c_9168, plain, (![A_631, B_632]: (m1_subset_1('#skF_3'(A_631, B_632), B_632) | v1_xboole_0(B_632) | '#skF_2'(A_631, B_632)=A_631 | k1_tarski(A_631)=B_632)), inference(resolution, [status(thm)], [c_7615, c_22])).
% 19.52/10.67  tff(c_9306, plain, (![A_45, A_631]: (m1_pre_topc(k1_tex_2(A_45, '#skF_3'(A_631, u1_struct_0(A_45))), A_45) | ~l1_pre_topc(A_45) | v2_struct_0(A_45) | v1_xboole_0(u1_struct_0(A_45)) | '#skF_2'(A_631, u1_struct_0(A_45))=A_631 | u1_struct_0(A_45)=k1_tarski(A_631))), inference(resolution, [status(thm)], [c_9168, c_62])).
% 19.52/10.67  tff(c_18530, plain, (![B_988, A_631]: (r2_hidden('#skF_1'(u1_struct_0(B_988)), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(B_988)) | ~m1_pre_topc(B_988, k1_tex_2('#skF_5', '#skF_3'(A_631, u1_struct_0('#skF_5')))) | ~l1_pre_topc(k1_tex_2('#skF_5', '#skF_3'(A_631, u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0('#skF_5')) | '#skF_2'(A_631, u1_struct_0('#skF_5'))=A_631 | u1_struct_0('#skF_5')=k1_tarski(A_631))), inference(resolution, [status(thm)], [c_9306, c_18527])).
% 19.52/10.67  tff(c_18554, plain, (![B_988, A_631]: (r2_hidden('#skF_1'(u1_struct_0(B_988)), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(B_988)) | ~m1_pre_topc(B_988, k1_tex_2('#skF_5', '#skF_3'(A_631, k1_tarski('#skF_6')))) | ~l1_pre_topc(k1_tex_2('#skF_5', '#skF_3'(A_631, k1_tarski('#skF_6')))) | v2_struct_0('#skF_5') | v1_xboole_0(k1_tarski('#skF_6')) | '#skF_2'(A_631, k1_tarski('#skF_6'))=A_631 | k1_tarski(A_631)=k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7153, c_7153, c_7153, c_82, c_7153, c_7153, c_18530])).
% 19.52/10.67  tff(c_18618, plain, (![B_991, A_992]: (r2_hidden('#skF_1'(u1_struct_0(B_991)), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(B_991)) | ~m1_pre_topc(B_991, k1_tex_2('#skF_5', '#skF_3'(A_992, k1_tarski('#skF_6')))) | ~l1_pre_topc(k1_tex_2('#skF_5', '#skF_3'(A_992, k1_tarski('#skF_6')))) | '#skF_2'(A_992, k1_tarski('#skF_6'))=A_992 | k1_tarski(A_992)=k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_6808, c_84, c_18554])).
% 19.52/10.67  tff(c_19947, plain, (![A_1020]: (r2_hidden('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_3'(A_1020, k1_tarski('#skF_6'))), '#skF_6'))), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_3'(A_1020, k1_tarski('#skF_6'))), '#skF_6'))) | '#skF_2'(A_1020, k1_tarski('#skF_6'))=A_1020 | k1_tarski(A_1020)=k1_tarski('#skF_6') | v2_struct_0(k1_tex_2('#skF_5', '#skF_3'(A_1020, k1_tarski('#skF_6')))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_3'(A_1020, k1_tarski('#skF_6'))))) | ~m1_pre_topc('#skF_5', k1_tex_2('#skF_5', '#skF_3'(A_1020, k1_tarski('#skF_6')))) | ~l1_pre_topc(k1_tex_2('#skF_5', '#skF_3'(A_1020, k1_tarski('#skF_6')))))), inference(resolution, [status(thm)], [c_8116, c_18618])).
% 19.52/10.67  tff(c_19968, plain, (![A_531]: (r2_hidden('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), k1_tarski('#skF_6')) | v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_3'(A_531, k1_tarski('#skF_6'))), '#skF_6'))) | '#skF_2'(A_531, k1_tarski('#skF_6'))=A_531 | k1_tarski(A_531)=k1_tarski('#skF_6') | v2_struct_0(k1_tex_2('#skF_5', '#skF_3'(A_531, k1_tarski('#skF_6')))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_3'(A_531, k1_tarski('#skF_6'))))) | ~m1_pre_topc('#skF_5', k1_tex_2('#skF_5', '#skF_3'(A_531, k1_tarski('#skF_6')))) | ~l1_pre_topc(k1_tex_2('#skF_5', '#skF_3'(A_531, k1_tarski('#skF_6')))) | '#skF_2'(A_531, k1_tarski('#skF_6'))=A_531 | k1_tarski(A_531)=k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7630, c_19947])).
% 19.52/10.67  tff(c_26896, plain, (r2_hidden('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_19968])).
% 19.52/10.67  tff(c_8862, plain, (![A_621, B_622]: (v1_subset_1(k6_domain_1(A_621, B_622), A_621) | k6_domain_1(A_621, B_622)=A_621 | ~m1_subset_1(B_622, A_621) | v1_xboole_0(A_621))), inference(resolution, [status(thm)], [c_7102, c_58])).
% 19.52/10.67  tff(c_74, plain, (![A_49, B_51]: (~v1_zfmisc_1(A_49) | ~v1_subset_1(k6_domain_1(A_49, B_51), A_49) | ~m1_subset_1(B_51, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_171])).
% 19.52/10.67  tff(c_8900, plain, (![A_623, B_624]: (~v1_zfmisc_1(A_623) | k6_domain_1(A_623, B_624)=A_623 | ~m1_subset_1(B_624, A_623) | v1_xboole_0(A_623))), inference(resolution, [status(thm)], [c_8862, c_74])).
% 19.52/10.67  tff(c_8965, plain, (![A_626]: (~v1_zfmisc_1(A_626) | k6_domain_1(A_626, '#skF_1'(A_626))=A_626 | v1_xboole_0(A_626))), inference(resolution, [status(thm)], [c_6963, c_8900])).
% 19.52/10.67  tff(c_7049, plain, (![A_1]: (k6_domain_1(A_1, '#skF_1'(A_1))=k1_tarski('#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_6963, c_7033])).
% 19.52/10.67  tff(c_9011, plain, (![A_627]: (k1_tarski('#skF_1'(A_627))=A_627 | v1_xboole_0(A_627) | ~v1_zfmisc_1(A_627) | v1_xboole_0(A_627))), inference(superposition, [status(thm), theory('equality')], [c_8965, c_7049])).
% 19.52/10.67  tff(c_9073, plain, (![C_9, A_627]: (C_9='#skF_1'(A_627) | ~r2_hidden(C_9, A_627) | v1_xboole_0(A_627) | ~v1_zfmisc_1(A_627) | v1_xboole_0(A_627))), inference(superposition, [status(thm), theory('equality')], [c_9011, c_6])).
% 19.52/10.67  tff(c_26899, plain, ('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')))='#skF_1'(k1_tarski('#skF_6')) | ~v1_zfmisc_1(k1_tarski('#skF_6')) | v1_xboole_0(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_26896, c_9073])).
% 19.52/10.67  tff(c_26922, plain, ('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')))='#skF_6' | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7548, c_6900, c_26899])).
% 19.52/10.67  tff(c_26923, plain, ('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_6808, c_26922])).
% 19.52/10.67  tff(c_27145, plain, (m1_subset_1('#skF_6', u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))) | v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_26923, c_6963])).
% 19.52/10.67  tff(c_38272, plain, (v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')))), inference(splitLeft, [status(thm)], [c_27145])).
% 19.52/10.67  tff(c_38497, plain, (~l1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')) | v2_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_38272, c_42])).
% 19.52/10.67  tff(c_38498, plain, (~l1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_38497])).
% 19.52/10.67  tff(c_38502, plain, (~l1_pre_topc(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_38498])).
% 19.52/10.67  tff(c_38544, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_20396, c_38502])).
% 19.52/10.67  tff(c_38553, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7964, c_7972, c_38544])).
% 19.52/10.67  tff(c_38554, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_7612, c_38553])).
% 19.52/10.67  tff(c_38565, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_38554])).
% 19.52/10.67  tff(c_38569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7972, c_38565])).
% 19.52/10.67  tff(c_38570, plain, (v2_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), inference(splitRight, [status(thm)], [c_38497])).
% 19.52/10.67  tff(c_72, plain, (![A_47, B_48]: (~v2_struct_0(k1_tex_2(A_47, B_48)) | ~m1_subset_1(B_48, u1_struct_0(A_47)) | ~l1_pre_topc(A_47) | v2_struct_0(A_47))), inference(cnfTransformation, [status(thm)], [f_160])).
% 19.52/10.67  tff(c_10322, plain, (![B_697]: (~v2_struct_0(k1_tex_2(B_697, '#skF_6')) | ~l1_pre_topc(B_697) | v1_xboole_0(u1_struct_0(B_697)) | ~l1_struct_0(B_697) | v2_struct_0(B_697) | ~m1_pre_topc(B_697, '#skF_5'))), inference(resolution, [status(thm)], [c_10287, c_72])).
% 19.52/10.67  tff(c_38574, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_38570, c_10322])).
% 19.52/10.67  tff(c_38583, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7964, c_7972, c_38574])).
% 19.52/10.67  tff(c_38584, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_7612, c_38583])).
% 19.52/10.67  tff(c_38593, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_38584])).
% 19.52/10.67  tff(c_38731, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_38593])).
% 19.52/10.67  tff(c_38735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7972, c_38731])).
% 19.52/10.67  tff(c_38737, plain, (l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_38584])).
% 19.52/10.67  tff(c_38736, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_38584])).
% 19.52/10.67  tff(c_38759, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_38736, c_42])).
% 19.52/10.67  tff(c_38789, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38737, c_38759])).
% 19.52/10.67  tff(c_38791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7612, c_38789])).
% 19.52/10.67  tff(c_38793, plain, (~v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')))), inference(splitRight, [status(thm)], [c_27145])).
% 19.52/10.67  tff(c_38792, plain, (m1_subset_1('#skF_6', u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')))), inference(splitRight, [status(thm)], [c_27145])).
% 19.52/10.67  tff(c_24, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 19.52/10.67  tff(c_7678, plain, (![B_538, A_539, A_540]: (r2_hidden(B_538, A_539) | ~m1_subset_1(A_540, k1_zfmisc_1(A_539)) | ~m1_subset_1(B_538, A_540) | v1_xboole_0(A_540))), inference(resolution, [status(thm)], [c_24, c_7012])).
% 19.52/10.67  tff(c_7701, plain, (![B_538, A_30, B_32]: (r2_hidden(B_538, u1_struct_0(A_30)) | ~m1_subset_1(B_538, u1_struct_0(B_32)) | v1_xboole_0(u1_struct_0(B_32)) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_48, c_7678])).
% 19.52/10.67  tff(c_38810, plain, (![A_30]: (r2_hidden('#skF_6', u1_struct_0(A_30)) | v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))) | ~m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'), A_30) | ~l1_pre_topc(A_30))), inference(resolution, [status(thm)], [c_38792, c_7701])).
% 19.52/10.67  tff(c_39763, plain, (![A_1347]: (r2_hidden('#skF_6', u1_struct_0(A_1347)) | ~m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'), A_1347) | ~l1_pre_topc(A_1347))), inference(negUnitSimplification, [status(thm)], [c_38793, c_38810])).
% 19.52/10.67  tff(c_39767, plain, (r2_hidden('#skF_6', u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_10320, c_39763])).
% 19.52/10.67  tff(c_39778, plain, (r2_hidden('#skF_6', u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7964, c_7972, c_39767])).
% 19.52/10.67  tff(c_39779, plain, (r2_hidden('#skF_6', u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_7612, c_39778])).
% 19.52/10.67  tff(c_41105, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_39779])).
% 19.52/10.67  tff(c_41108, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_41105])).
% 19.52/10.67  tff(c_41112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7972, c_41108])).
% 19.52/10.67  tff(c_41114, plain, (l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_39779])).
% 19.52/10.67  tff(c_6803, plain, (v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 19.52/10.67  tff(c_41113, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | r2_hidden('#skF_6', u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_39779])).
% 19.52/10.67  tff(c_41115, plain, (r2_hidden('#skF_6', u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_41113])).
% 19.52/10.67  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 19.52/10.67  tff(c_41130, plain, (~v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_41115, c_2])).
% 19.52/10.67  tff(c_7642, plain, (![A_535, B_536]: (v7_struct_0(k1_tex_2(A_535, B_536)) | ~m1_subset_1(B_536, u1_struct_0(A_535)) | ~l1_pre_topc(A_535) | v2_struct_0(A_535))), inference(cnfTransformation, [status(thm)], [f_160])).
% 19.52/10.67  tff(c_7645, plain, (![B_536]: (v7_struct_0(k1_tex_2('#skF_5', B_536)) | ~m1_subset_1(B_536, k1_tarski('#skF_6')) | ~l1_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7153, c_7642])).
% 19.52/10.67  tff(c_7655, plain, (![B_536]: (v7_struct_0(k1_tex_2('#skF_5', B_536)) | ~m1_subset_1(B_536, k1_tarski('#skF_6')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_7645])).
% 19.52/10.67  tff(c_7659, plain, (![B_537]: (v7_struct_0(k1_tex_2('#skF_5', B_537)) | ~m1_subset_1(B_537, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_84, c_7655])).
% 19.52/10.67  tff(c_7663, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_1'(k1_tarski('#skF_6')))) | v1_xboole_0(k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_6963, c_7659])).
% 19.52/10.67  tff(c_7673, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v1_xboole_0(k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6900, c_7663])).
% 19.52/10.67  tff(c_7674, plain, (v7_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_6808, c_7673])).
% 19.52/10.67  tff(c_7360, plain, (![B_500]: ('#skF_1'(u1_struct_0(B_500))='#skF_6' | v1_xboole_0(u1_struct_0(B_500)) | ~m1_pre_topc(B_500, '#skF_5'))), inference(resolution, [status(thm)], [c_7315, c_7340])).
% 19.52/10.67  tff(c_41133, plain, ('#skF_1'(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))='#skF_6' | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_7360, c_41130])).
% 19.52/10.67  tff(c_41136, plain, ('#skF_1'(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_7964, c_41133])).
% 19.52/10.67  tff(c_78, plain, (![A_55, B_57]: (~v7_struct_0(A_55) | ~v1_subset_1(k6_domain_1(u1_struct_0(A_55), B_57), u1_struct_0(A_55)) | ~m1_subset_1(B_57, u1_struct_0(A_55)) | ~l1_struct_0(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_195])).
% 19.52/10.67  tff(c_14890, plain, (![A_850, B_851]: (~v7_struct_0(A_850) | ~l1_struct_0(A_850) | v2_struct_0(A_850) | k6_domain_1(u1_struct_0(A_850), B_851)=u1_struct_0(A_850) | ~m1_subset_1(B_851, u1_struct_0(A_850)) | v1_xboole_0(u1_struct_0(A_850)))), inference(resolution, [status(thm)], [c_8862, c_78])).
% 19.52/10.67  tff(c_16190, plain, (![A_897]: (~v7_struct_0(A_897) | ~l1_struct_0(A_897) | v2_struct_0(A_897) | k6_domain_1(u1_struct_0(A_897), '#skF_1'(u1_struct_0(A_897)))=u1_struct_0(A_897) | v1_xboole_0(u1_struct_0(A_897)))), inference(resolution, [status(thm)], [c_6963, c_14890])).
% 19.52/10.67  tff(c_16244, plain, (![A_897]: (~v7_struct_0(A_897) | ~l1_struct_0(A_897) | v2_struct_0(A_897) | k1_tarski('#skF_1'(u1_struct_0(A_897)))=u1_struct_0(A_897) | v1_xboole_0(u1_struct_0(A_897)) | v1_xboole_0(u1_struct_0(A_897)))), inference(superposition, [status(thm), theory('equality')], [c_7049, c_16190])).
% 19.52/10.67  tff(c_41253, plain, (~v7_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_41136, c_16244])).
% 19.52/10.67  tff(c_41493, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6') | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_41114, c_7674, c_41253])).
% 19.52/10.67  tff(c_41494, plain, (u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))=k1_tarski('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_41130, c_7612, c_41493])).
% 19.52/10.67  tff(c_8731, plain, (![B_608, A_609]: (v1_subset_1(u1_struct_0(B_608), u1_struct_0(A_609)) | ~m1_subset_1(u1_struct_0(B_608), k1_zfmisc_1(u1_struct_0(A_609))) | ~v1_tex_2(B_608, A_609) | ~m1_pre_topc(B_608, A_609) | ~l1_pre_topc(A_609))), inference(cnfTransformation, [status(thm)], [f_125])).
% 19.52/10.67  tff(c_8767, plain, (![B_612, A_613]: (v1_subset_1(u1_struct_0(B_612), u1_struct_0(A_613)) | ~v1_tex_2(B_612, A_613) | ~m1_pre_topc(B_612, A_613) | ~l1_pre_topc(A_613))), inference(resolution, [status(thm)], [c_48, c_8731])).
% 19.52/10.67  tff(c_8777, plain, (![B_612]: (v1_subset_1(u1_struct_0(B_612), k1_tarski('#skF_6')) | ~v1_tex_2(B_612, '#skF_5') | ~m1_pre_topc(B_612, '#skF_5') | ~l1_pre_topc('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7153, c_8767])).
% 19.52/10.67  tff(c_8780, plain, (![B_612]: (v1_subset_1(u1_struct_0(B_612), k1_tarski('#skF_6')) | ~v1_tex_2(B_612, '#skF_5') | ~m1_pre_topc(B_612, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_8777])).
% 19.52/10.67  tff(c_41946, plain, (v1_subset_1(k1_tarski('#skF_6'), k1_tarski('#skF_6')) | ~v1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_5') | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_41494, c_8780])).
% 19.52/10.67  tff(c_42311, plain, (v1_subset_1(k1_tarski('#skF_6'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7964, c_6803, c_41946])).
% 19.52/10.67  tff(c_42313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_42311])).
% 19.52/10.67  tff(c_42314, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_41113])).
% 19.52/10.67  tff(c_42337, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_42314, c_42])).
% 19.52/10.67  tff(c_42367, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_41114, c_42337])).
% 19.52/10.67  tff(c_42369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7612, c_42367])).
% 19.52/10.67  tff(c_42371, plain, (~r2_hidden('#skF_1'(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_19968])).
% 19.52/10.67  tff(c_42462, plain, (v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))) | ~m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'), k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_18567, c_42371])).
% 19.52/10.67  tff(c_42649, plain, (~m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'), k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_42462])).
% 19.52/10.67  tff(c_42652, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_10320, c_42649])).
% 19.52/10.67  tff(c_42661, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7964, c_7972, c_42652])).
% 19.52/10.67  tff(c_42662, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_7612, c_42661])).
% 19.52/10.67  tff(c_42671, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_42662])).
% 19.52/10.67  tff(c_42674, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_42671])).
% 19.52/10.67  tff(c_42678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7972, c_42674])).
% 19.52/10.67  tff(c_42680, plain, (l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_42662])).
% 19.52/10.67  tff(c_42679, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_42662])).
% 19.52/10.67  tff(c_42700, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_42679, c_42])).
% 19.52/10.67  tff(c_42727, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42680, c_42700])).
% 19.52/10.67  tff(c_42729, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7612, c_42727])).
% 19.52/10.67  tff(c_42731, plain, (m1_pre_topc(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'), k1_tex_2('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_42462])).
% 19.52/10.67  tff(c_42816, plain, (l1_pre_topc(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')) | ~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_42731, c_40])).
% 19.52/10.67  tff(c_42824, plain, (l1_pre_topc(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7972, c_42816])).
% 19.52/10.67  tff(c_42730, plain, (v1_xboole_0(u1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')))), inference(splitRight, [status(thm)], [c_42462])).
% 19.52/10.67  tff(c_42808, plain, (~l1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6')) | v2_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_42730, c_42])).
% 19.52/10.67  tff(c_42859, plain, (~l1_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_42808])).
% 19.52/10.67  tff(c_42862, plain, (~l1_pre_topc(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_42859])).
% 19.52/10.67  tff(c_42866, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42824, c_42862])).
% 19.52/10.67  tff(c_42867, plain, (v2_struct_0(k1_tex_2(k1_tex_2('#skF_5', '#skF_6'), '#skF_6'))), inference(splitRight, [status(thm)], [c_42808])).
% 19.52/10.67  tff(c_42871, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6')) | v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6')) | ~m1_pre_topc(k1_tex_2('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_42867, c_10322])).
% 19.52/10.67  tff(c_42880, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7964, c_7972, c_42871])).
% 19.52/10.67  tff(c_42881, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6'))) | ~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_7612, c_42880])).
% 19.52/10.67  tff(c_42890, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_42881])).
% 19.52/10.67  tff(c_42996, plain, (~l1_pre_topc(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_42890])).
% 19.52/10.67  tff(c_43000, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7972, c_42996])).
% 19.52/10.67  tff(c_43002, plain, (l1_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_42881])).
% 19.52/10.67  tff(c_43001, plain, (v1_xboole_0(u1_struct_0(k1_tex_2('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_42881])).
% 19.52/10.67  tff(c_43022, plain, (~l1_struct_0(k1_tex_2('#skF_5', '#skF_6')) | v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_43001, c_42])).
% 19.52/10.67  tff(c_43049, plain, (v2_struct_0(k1_tex_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_43002, c_43022])).
% 19.52/10.67  tff(c_43051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7612, c_43049])).
% 19.52/10.67  tff(c_43053, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_6924])).
% 19.52/10.67  tff(c_43056, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_43053, c_42])).
% 19.52/10.67  tff(c_43059, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_84, c_43056])).
% 19.52/10.67  tff(c_43062, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_38, c_43059])).
% 19.52/10.67  tff(c_43066, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_43062])).
% 19.52/10.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.52/10.67  
% 19.52/10.67  Inference rules
% 19.52/10.67  ----------------------
% 19.52/10.67  #Ref     : 0
% 19.52/10.67  #Sup     : 9071
% 19.52/10.67  #Fact    : 0
% 19.52/10.67  #Define  : 0
% 19.52/10.67  #Split   : 77
% 19.52/10.67  #Chain   : 0
% 19.52/10.67  #Close   : 0
% 19.52/10.67  
% 19.52/10.67  Ordering : KBO
% 19.52/10.67  
% 19.52/10.67  Simplification rules
% 19.52/10.67  ----------------------
% 19.52/10.67  #Subsume      : 2330
% 19.52/10.67  #Demod        : 3810
% 19.52/10.67  #Tautology    : 1262
% 19.52/10.67  #SimpNegUnit  : 3074
% 19.52/10.67  #BackRed      : 56
% 19.52/10.67  
% 19.52/10.67  #Partial instantiations: 0
% 19.52/10.67  #Strategies tried      : 1
% 19.52/10.67  
% 19.52/10.67  Timing (in seconds)
% 19.52/10.67  ----------------------
% 19.52/10.68  Preprocessing        : 0.37
% 19.52/10.68  Parsing              : 0.19
% 19.52/10.68  CNF conversion       : 0.03
% 19.52/10.68  Main loop            : 9.48
% 19.52/10.68  Inferencing          : 1.98
% 19.52/10.68  Reduction            : 2.44
% 19.52/10.68  Demodulation         : 1.49
% 19.52/10.68  BG Simplification    : 0.18
% 19.52/10.68  Subsumption          : 4.20
% 19.52/10.68  Abstraction          : 0.37
% 19.52/10.68  MUC search           : 0.00
% 19.52/10.68  Cooper               : 0.00
% 19.52/10.68  Total                : 9.95
% 19.52/10.68  Index Insertion      : 0.00
% 19.52/10.68  Index Deletion       : 0.00
% 19.52/10.68  Index Matching       : 0.00
% 19.52/10.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
