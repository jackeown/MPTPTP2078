%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:13 EST 2020

% Result     : Theorem 32.46s
% Output     : CNFRefutation 33.15s
% Verified   : 
% Statistics : Number of formulae       :  513 (17814 expanded)
%              Number of leaves         :   51 (5785 expanded)
%              Depth                    :   19
%              Number of atoms          : 1441 (59498 expanded)
%              Number of equality atoms :   79 (7817 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_240,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                   => ( C = D
                     => ( v5_pre_topc(C,A,B)
                      <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_152,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_144,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_140,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_62,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_210,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

tff(f_181,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))),u1_struct_0(B)))) )
                 => ( C = D
                   => ( v5_pre_topc(C,A,B)
                    <=> v5_pre_topc(D,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_134,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_113,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & ~ v1_xboole_0(C)
              & v1_funct_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_102,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_100,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_82,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_104,plain,
    ( ~ v5_pre_topc('#skF_7',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_112,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_104])).

tff(c_421,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_303,plain,(
    ! [A_128,B_129] :
      ( ~ r2_hidden('#skF_2'(A_128,B_129),B_129)
      | r1_tarski(A_128,B_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_308,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_94,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_98,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_96,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_70,plain,(
    ! [A_44] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_44),u1_pre_topc(A_44)))
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_320,plain,(
    ! [A_133] :
      ( m1_subset_1(u1_pre_topc(A_133),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_133))))
      | ~ l1_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_64,plain,(
    ! [A_41,B_42] :
      ( l1_pre_topc(g1_pre_topc(A_41,B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_330,plain,(
    ! [A_133] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_133),u1_pre_topc(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_320,c_64])).

tff(c_90,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_554,plain,(
    ! [C_188,B_189,A_190] :
      ( v1_xboole_0(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(B_189,A_190)))
      | ~ v1_xboole_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_577,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_90,c_554])).

tff(c_580,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_577])).

tff(c_28,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_219,plain,(
    ! [B_121,A_122] :
      ( v1_relat_1(B_121)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_122))
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_234,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_90,c_219])).

tff(c_247,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_234])).

tff(c_363,plain,(
    ! [C_144,A_145,B_146] :
      ( v4_relat_1(C_144,A_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_383,plain,(
    v4_relat_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_363])).

tff(c_856,plain,(
    ! [B_210,A_211] :
      ( k1_relat_1(B_210) = A_211
      | ~ v1_partfun1(B_210,A_211)
      | ~ v4_relat_1(B_210,A_211)
      | ~ v1_relat_1(B_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_874,plain,
    ( u1_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_383,c_856])).

tff(c_891,plain,
    ( u1_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_874])).

tff(c_927,plain,(
    ~ v1_partfun1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_891])).

tff(c_92,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_937,plain,(
    ! [C_218,A_219,B_220] :
      ( v1_partfun1(C_218,A_219)
      | ~ v1_funct_2(C_218,A_219,B_220)
      | ~ v1_funct_1(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | v1_xboole_0(B_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_950,plain,
    ( v1_partfun1('#skF_6',u1_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_90,c_937])).

tff(c_967,plain,
    ( v1_partfun1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_950])).

tff(c_969,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_580,c_927,c_967])).

tff(c_970,plain,(
    u1_struct_0('#skF_4') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_891])).

tff(c_171,plain,(
    ! [A_105,B_106] :
      ( r1_tarski(A_105,B_106)
      | ~ m1_subset_1(A_105,k1_zfmisc_1(B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_175,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_90,c_171])).

tff(c_978,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_175])).

tff(c_980,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_92])).

tff(c_84,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_115,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_84])).

tff(c_574,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_115,c_554])).

tff(c_807,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_574])).

tff(c_86,plain,(
    v1_funct_2('#skF_7',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_114,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_86])).

tff(c_977,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_114])).

tff(c_974,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_115])).

tff(c_38,plain,(
    ! [C_31,A_28,B_29] :
      ( v1_partfun1(C_31,A_28)
      | ~ v1_funct_2(C_31,A_28,B_29)
      | ~ v1_funct_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | v1_xboole_0(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1386,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_974,c_38])).

tff(c_1411,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_977,c_1386])).

tff(c_1412,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_807,c_1411])).

tff(c_34,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_512,plain,(
    v4_relat_1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_115,c_34])).

tff(c_859,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_512,c_856])).

tff(c_880,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_859])).

tff(c_2575,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_970,c_970,c_880])).

tff(c_979,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_90])).

tff(c_987,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_70])).

tff(c_1002,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_987])).

tff(c_993,plain,
    ( l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_330])).

tff(c_1006,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_993])).

tff(c_110,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v5_pre_topc('#skF_7',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_111,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_110])).

tff(c_464,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_111])).

tff(c_975,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_970,c_464])).

tff(c_2084,plain,(
    ! [D_290,A_291,B_292] :
      ( v5_pre_topc(D_290,A_291,B_292)
      | ~ v5_pre_topc(D_290,A_291,g1_pre_topc(u1_struct_0(B_292),u1_pre_topc(B_292)))
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291),u1_struct_0(g1_pre_topc(u1_struct_0(B_292),u1_pre_topc(B_292))))))
      | ~ v1_funct_2(D_290,u1_struct_0(A_291),u1_struct_0(g1_pre_topc(u1_struct_0(B_292),u1_pre_topc(B_292))))
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291),u1_struct_0(B_292))))
      | ~ v1_funct_2(D_290,u1_struct_0(A_291),u1_struct_0(B_292))
      | ~ v1_funct_1(D_290)
      | ~ l1_pre_topc(B_292)
      | ~ v2_pre_topc(B_292)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_2087,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_974,c_2084])).

tff(c_2104,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_1006,c_98,c_96,c_94,c_977,c_975,c_2087])).

tff(c_5336,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_980,c_2575,c_979,c_2575,c_2104])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1604,plain,(
    ! [D_257,A_258,B_259] :
      ( v5_pre_topc(D_257,A_258,B_259)
      | ~ v5_pre_topc(D_257,g1_pre_topc(u1_struct_0(A_258),u1_pre_topc(A_258)),B_259)
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_258),u1_pre_topc(A_258))),u1_struct_0(B_259))))
      | ~ v1_funct_2(D_257,u1_struct_0(g1_pre_topc(u1_struct_0(A_258),u1_pre_topc(A_258))),u1_struct_0(B_259))
      | ~ m1_subset_1(D_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_258),u1_struct_0(B_259))))
      | ~ v1_funct_2(D_257,u1_struct_0(A_258),u1_struct_0(B_259))
      | ~ v1_funct_1(D_257)
      | ~ l1_pre_topc(B_259)
      | ~ v2_pre_topc(B_259)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_4966,plain,(
    ! [A_447,A_448,B_449] :
      ( v5_pre_topc(A_447,A_448,B_449)
      | ~ v5_pre_topc(A_447,g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(A_448)),B_449)
      | ~ v1_funct_2(A_447,u1_struct_0(g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(A_448))),u1_struct_0(B_449))
      | ~ m1_subset_1(A_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_448),u1_struct_0(B_449))))
      | ~ v1_funct_2(A_447,u1_struct_0(A_448),u1_struct_0(B_449))
      | ~ v1_funct_1(A_447)
      | ~ l1_pre_topc(B_449)
      | ~ v2_pre_topc(B_449)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448)
      | ~ r1_tarski(A_447,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_448),u1_pre_topc(A_448))),u1_struct_0(B_449))) ) ),
    inference(resolution,[status(thm)],[c_24,c_1604])).

tff(c_4991,plain,(
    ! [A_447,B_449] :
      ( v5_pre_topc(A_447,'#skF_4',B_449)
      | ~ v5_pre_topc(A_447,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),B_449)
      | ~ v1_funct_2(A_447,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(B_449))
      | ~ m1_subset_1(A_447,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_449))))
      | ~ v1_funct_2(A_447,u1_struct_0('#skF_4'),u1_struct_0(B_449))
      | ~ v1_funct_1(A_447)
      | ~ l1_pre_topc(B_449)
      | ~ v2_pre_topc(B_449)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ r1_tarski(A_447,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(B_449))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_4966])).

tff(c_35338,plain,(
    ! [A_1499,B_1500] :
      ( v5_pre_topc(A_1499,'#skF_4',B_1500)
      | ~ v5_pre_topc(A_1499,g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),B_1500)
      | ~ m1_subset_1(A_1499,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(B_1500))))
      | ~ v1_funct_2(A_1499,k1_relat_1('#skF_6'),u1_struct_0(B_1500))
      | ~ v1_funct_1(A_1499)
      | ~ l1_pre_topc(B_1500)
      | ~ v2_pre_topc(B_1500)
      | ~ r1_tarski(A_1499,k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(B_1500))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2575,c_102,c_100,c_970,c_970,c_2575,c_970,c_970,c_4991])).

tff(c_35347,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | ~ r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_979,c_35338])).

tff(c_35366,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_978,c_98,c_96,c_94,c_980,c_5336,c_35347])).

tff(c_35368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_35366])).

tff(c_35370,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_35369,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_574])).

tff(c_14,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_35382,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_35369,c_14])).

tff(c_35400,plain,(
    ! [A_10] :
      ( A_10 = '#skF_6'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35382,c_14])).

tff(c_35644,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_35370,c_35400])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_332,plain,(
    ! [A_133] :
      ( r1_tarski(u1_pre_topc(A_133),k1_zfmisc_1(u1_struct_0(A_133)))
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_320,c_22])).

tff(c_36089,plain,
    ( r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))),k1_zfmisc_1('#skF_6'))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_35644,c_332])).

tff(c_36822,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_36089])).

tff(c_36825,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_330,c_36822])).

tff(c_36832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_36825])).

tff(c_36834,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_36089])).

tff(c_36086,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_35644,c_70])).

tff(c_38397,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36834,c_36086])).

tff(c_38398,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_38397])).

tff(c_38401,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_38398])).

tff(c_38405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_38401])).

tff(c_38407,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_38397])).

tff(c_20,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_181,plain,(
    ! [A_109,B_110] : m1_subset_1('#skF_3'(A_109,B_110),k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_190,plain,(
    ! [B_12] : m1_subset_1('#skF_3'(k1_xboole_0,B_12),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_181])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_570,plain,(
    ! [C_188] :
      ( v1_xboole_0(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_554])).

tff(c_596,plain,(
    ! [C_193] :
      ( v1_xboole_0(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_570])).

tff(c_610,plain,(
    ! [B_194] : v1_xboole_0('#skF_3'(k1_xboole_0,B_194)) ),
    inference(resolution,[status(thm)],[c_190,c_596])).

tff(c_622,plain,(
    ! [B_194] : '#skF_3'(k1_xboole_0,B_194) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_610,c_14])).

tff(c_35520,plain,(
    ! [B_1506] : '#skF_3'('#skF_6',B_1506) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35382,c_35382,c_622])).

tff(c_52,plain,(
    ! [A_38,B_39] : v1_funct_2('#skF_3'(A_38,B_39),A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_35534,plain,(
    ! [B_1506] : v1_funct_2('#skF_6','#skF_6',B_1506) ),
    inference(superposition,[status(thm),theory(equality)],[c_35520,c_52])).

tff(c_35391,plain,(
    ! [B_194] : '#skF_3'('#skF_6',B_194) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35382,c_35382,c_622])).

tff(c_35723,plain,(
    ! [C_1522,A_1523,B_1524] :
      ( ~ v1_xboole_0(C_1522)
      | ~ v1_funct_2(C_1522,A_1523,B_1524)
      | ~ v1_funct_1(C_1522)
      | ~ m1_subset_1(C_1522,k1_zfmisc_1(k2_zfmisc_1(A_1523,B_1524)))
      | v1_xboole_0(B_1524)
      | v1_xboole_0(A_1523) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_35742,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_90,c_35723])).

tff(c_35754,plain,
    ( v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_35369,c_35742])).

tff(c_35755,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_580,c_35754])).

tff(c_35768,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_35755,c_35400])).

tff(c_644,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_622,c_190])).

tff(c_35388,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35382,c_35382,c_644])).

tff(c_35402,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_6',B_12) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35382,c_35382,c_20])).

tff(c_54,plain,(
    ! [A_38,B_39] : v1_funct_1('#skF_3'(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_62,plain,(
    ! [A_38,B_39] : m1_subset_1('#skF_3'(A_38,B_39),k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_35904,plain,(
    ! [D_1529,A_1530,B_1531] :
      ( v5_pre_topc(D_1529,A_1530,g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531)))
      | ~ v5_pre_topc(D_1529,A_1530,B_1531)
      | ~ m1_subset_1(D_1529,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1530),u1_struct_0(g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531))))))
      | ~ v1_funct_2(D_1529,u1_struct_0(A_1530),u1_struct_0(g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531))))
      | ~ m1_subset_1(D_1529,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1530),u1_struct_0(B_1531))))
      | ~ v1_funct_2(D_1529,u1_struct_0(A_1530),u1_struct_0(B_1531))
      | ~ v1_funct_1(D_1529)
      | ~ l1_pre_topc(B_1531)
      | ~ v2_pre_topc(B_1531)
      | ~ l1_pre_topc(A_1530)
      | ~ v2_pre_topc(A_1530) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_35917,plain,(
    ! [A_1530,B_1531] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_1530),u1_struct_0(g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531)))),A_1530,g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_1530),u1_struct_0(g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531)))),A_1530,B_1531)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_1530),u1_struct_0(g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531)))),u1_struct_0(A_1530),u1_struct_0(g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531))))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_1530),u1_struct_0(g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1530),u1_struct_0(B_1531))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_1530),u1_struct_0(g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531)))),u1_struct_0(A_1530),u1_struct_0(B_1531))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(A_1530),u1_struct_0(g1_pre_topc(u1_struct_0(B_1531),u1_pre_topc(B_1531)))))
      | ~ l1_pre_topc(B_1531)
      | ~ v2_pre_topc(B_1531)
      | ~ l1_pre_topc(A_1530)
      | ~ v2_pre_topc(A_1530) ) ),
    inference(resolution,[status(thm)],[c_62,c_35904])).

tff(c_41956,plain,(
    ! [A_1856,B_1857] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_1856),u1_struct_0(g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))),A_1856,g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_1856),u1_struct_0(g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))),A_1856,B_1857)
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_1856),u1_struct_0(g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1856),u1_struct_0(B_1857))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_1856),u1_struct_0(g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))),u1_struct_0(A_1856),u1_struct_0(B_1857))
      | ~ l1_pre_topc(B_1857)
      | ~ v2_pre_topc(B_1857)
      | ~ l1_pre_topc(A_1856)
      | ~ v2_pre_topc(A_1856) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_35917])).

tff(c_41972,plain,(
    ! [B_1857] :
      ( v5_pre_topc('#skF_3'(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))),'#skF_4',g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))),'#skF_4',B_1857)
      | ~ m1_subset_1('#skF_3'(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))),k1_zfmisc_1(k2_zfmisc_1('#skF_6',u1_struct_0(B_1857))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1857),u1_pre_topc(B_1857)))),u1_struct_0('#skF_4'),u1_struct_0(B_1857))
      | ~ l1_pre_topc(B_1857)
      | ~ v2_pre_topc(B_1857)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35768,c_41956])).

tff(c_43137,plain,(
    ! [B_1909] :
      ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0(B_1909),u1_pre_topc(B_1909)))
      | ~ v5_pre_topc('#skF_6','#skF_4',B_1909)
      | ~ l1_pre_topc(B_1909)
      | ~ v2_pre_topc(B_1909) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_35534,c_35391,c_35768,c_35768,c_35388,c_35402,c_35391,c_35768,c_35391,c_35768,c_35391,c_35768,c_41972])).

tff(c_43143,plain,
    ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_35644,c_43137])).

tff(c_43149,plain,
    ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38407,c_36834,c_43143])).

tff(c_45520,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_43149])).

tff(c_35776,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35768,c_464])).

tff(c_187,plain,(
    ! [A_11] : m1_subset_1('#skF_3'(A_11,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_181])).

tff(c_625,plain,(
    ! [A_195] : v1_xboole_0('#skF_3'(A_195,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_187,c_596])).

tff(c_637,plain,(
    ! [A_195] : '#skF_3'(A_195,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_625,c_14])).

tff(c_35590,plain,(
    ! [A_1509] : '#skF_3'(A_1509,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35382,c_35382,c_637])).

tff(c_35607,plain,(
    ! [A_1509] : v1_funct_2('#skF_6',A_1509,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_35590,c_52])).

tff(c_35389,plain,(
    ! [A_195] : '#skF_3'(A_195,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35382,c_35382,c_637])).

tff(c_35399,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35382,c_35382,c_18])).

tff(c_35982,plain,(
    ! [D_1534,A_1535,B_1536] :
      ( v5_pre_topc(D_1534,A_1535,B_1536)
      | ~ v5_pre_topc(D_1534,g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535)),B_1536)
      | ~ m1_subset_1(D_1534,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535))),u1_struct_0(B_1536))))
      | ~ v1_funct_2(D_1534,u1_struct_0(g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535))),u1_struct_0(B_1536))
      | ~ m1_subset_1(D_1534,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1535),u1_struct_0(B_1536))))
      | ~ v1_funct_2(D_1534,u1_struct_0(A_1535),u1_struct_0(B_1536))
      | ~ v1_funct_1(D_1534)
      | ~ l1_pre_topc(B_1536)
      | ~ v2_pre_topc(B_1536)
      | ~ l1_pre_topc(A_1535)
      | ~ v2_pre_topc(A_1535) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_35992,plain,(
    ! [A_1535,B_1536] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535))),u1_struct_0(B_1536)),A_1535,B_1536)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535))),u1_struct_0(B_1536)),g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535)),B_1536)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535))),u1_struct_0(B_1536)),u1_struct_0(g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535))),u1_struct_0(B_1536))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535))),u1_struct_0(B_1536)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1535),u1_struct_0(B_1536))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535))),u1_struct_0(B_1536)),u1_struct_0(A_1535),u1_struct_0(B_1536))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535),u1_pre_topc(A_1535))),u1_struct_0(B_1536)))
      | ~ l1_pre_topc(B_1536)
      | ~ v2_pre_topc(B_1536)
      | ~ l1_pre_topc(A_1535)
      | ~ v2_pre_topc(A_1535) ) ),
    inference(resolution,[status(thm)],[c_62,c_35982])).

tff(c_42889,plain,(
    ! [A_1894,B_1895] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894))),u1_struct_0(B_1895)),A_1894,B_1895)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894))),u1_struct_0(B_1895)),g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894)),B_1895)
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894))),u1_struct_0(B_1895)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1894),u1_struct_0(B_1895))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894))),u1_struct_0(B_1895)),u1_struct_0(A_1894),u1_struct_0(B_1895))
      | ~ l1_pre_topc(B_1895)
      | ~ v2_pre_topc(B_1895)
      | ~ l1_pre_topc(A_1894)
      | ~ v2_pre_topc(A_1894) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_35992])).

tff(c_42898,plain,(
    ! [A_1894] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),A_1894,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894))),'#skF_6'),g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894)),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1894),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894),u1_pre_topc(A_1894))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),u1_struct_0(A_1894),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(A_1894)
      | ~ v2_pre_topc(A_1894) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35644,c_42889])).

tff(c_53693,plain,(
    ! [A_2301] :
      ( v5_pre_topc('#skF_6',A_2301,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2301),u1_pre_topc(A_2301)),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(A_2301)
      | ~ v2_pre_topc(A_2301) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38407,c_36834,c_35607,c_35389,c_35644,c_35644,c_35388,c_35399,c_35389,c_35644,c_35644,c_35389,c_35389,c_35644,c_42898])).

tff(c_53713,plain,
    ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_35768,c_53693])).

tff(c_53725,plain,(
    v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_35776,c_53713])).

tff(c_53727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45520,c_53725])).

tff(c_53729,plain,(
    v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_43149])).

tff(c_36112,plain,(
    ! [D_1543,A_1544,B_1545] :
      ( v5_pre_topc(D_1543,A_1544,B_1545)
      | ~ v5_pre_topc(D_1543,A_1544,g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545)))
      | ~ m1_subset_1(D_1543,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1544),u1_struct_0(g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545))))))
      | ~ v1_funct_2(D_1543,u1_struct_0(A_1544),u1_struct_0(g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545))))
      | ~ m1_subset_1(D_1543,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1544),u1_struct_0(B_1545))))
      | ~ v1_funct_2(D_1543,u1_struct_0(A_1544),u1_struct_0(B_1545))
      | ~ v1_funct_1(D_1543)
      | ~ l1_pre_topc(B_1545)
      | ~ v2_pre_topc(B_1545)
      | ~ l1_pre_topc(A_1544)
      | ~ v2_pre_topc(A_1544) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_36131,plain,(
    ! [A_1544,B_1545] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_1544),u1_struct_0(g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545)))),A_1544,B_1545)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_1544),u1_struct_0(g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545)))),A_1544,g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545)))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_1544),u1_struct_0(g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545)))),u1_struct_0(A_1544),u1_struct_0(g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545))))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_1544),u1_struct_0(g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1544),u1_struct_0(B_1545))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_1544),u1_struct_0(g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545)))),u1_struct_0(A_1544),u1_struct_0(B_1545))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(A_1544),u1_struct_0(g1_pre_topc(u1_struct_0(B_1545),u1_pre_topc(B_1545)))))
      | ~ l1_pre_topc(B_1545)
      | ~ v2_pre_topc(B_1545)
      | ~ l1_pre_topc(A_1544)
      | ~ v2_pre_topc(A_1544) ) ),
    inference(resolution,[status(thm)],[c_62,c_36112])).

tff(c_40694,plain,(
    ! [A_1820,B_1821] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_1820),u1_struct_0(g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))),A_1820,B_1821)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_1820),u1_struct_0(g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))),A_1820,g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_1820),u1_struct_0(g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1820),u1_struct_0(B_1821))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_1820),u1_struct_0(g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))),u1_struct_0(A_1820),u1_struct_0(B_1821))
      | ~ l1_pre_topc(B_1821)
      | ~ v2_pre_topc(B_1821)
      | ~ l1_pre_topc(A_1820)
      | ~ v2_pre_topc(A_1820) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_36131])).

tff(c_40704,plain,(
    ! [B_1821] :
      ( v5_pre_topc('#skF_3'(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))),'#skF_4',B_1821)
      | ~ v5_pre_topc('#skF_3'('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))),'#skF_4',g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))
      | ~ m1_subset_1('#skF_3'(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_1821))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))),u1_struct_0('#skF_4'),u1_struct_0(B_1821))
      | ~ l1_pre_topc(B_1821)
      | ~ v2_pre_topc(B_1821)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35768,c_40694])).

tff(c_40718,plain,(
    ! [B_1821] :
      ( v5_pre_topc('#skF_6','#skF_4',B_1821)
      | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0(B_1821),u1_pre_topc(B_1821)))
      | ~ l1_pre_topc(B_1821)
      | ~ v2_pre_topc(B_1821) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_35534,c_35391,c_35768,c_35768,c_35388,c_35402,c_35391,c_35768,c_35768,c_35391,c_35391,c_35768,c_40704])).

tff(c_53732,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_53729,c_40718])).

tff(c_53735,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_53732])).

tff(c_53737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_53735])).

tff(c_53738,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_53751,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_53738,c_14])).

tff(c_192,plain,(
    ! [A_111] : m1_subset_1('#skF_3'(A_111,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_181])).

tff(c_196,plain,(
    ! [A_111] : r1_tarski('#skF_3'(A_111,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_192,c_22])).

tff(c_53766,plain,(
    ! [A_111] : r1_tarski('#skF_3'(A_111,'#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53751,c_53751,c_196])).

tff(c_579,plain,(
    ! [C_188] :
      ( v1_xboole_0(C_188)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_570])).

tff(c_54030,plain,(
    ! [C_2320] :
      ( v1_xboole_0(C_2320)
      | ~ m1_subset_1(C_2320,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53751,c_579])).

tff(c_54041,plain,(
    ! [A_2321] :
      ( v1_xboole_0(A_2321)
      | ~ r1_tarski(A_2321,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_54030])).

tff(c_54061,plain,(
    ! [A_2322] : v1_xboole_0('#skF_3'(A_2322,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_53766,c_54041])).

tff(c_53769,plain,(
    ! [A_10] :
      ( A_10 = '#skF_6'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53751,c_14])).

tff(c_54117,plain,(
    ! [A_2327] : '#skF_3'(A_2327,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54061,c_53769])).

tff(c_54140,plain,(
    ! [A_2327] : v1_funct_2('#skF_6',A_2327,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_54117,c_52])).

tff(c_53768,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_53751,c_53751,c_18])).

tff(c_53739,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_577])).

tff(c_53879,plain,(
    ! [A_2306] :
      ( A_2306 = '#skF_6'
      | ~ v1_xboole_0(A_2306) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53751,c_14])).

tff(c_53886,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_53739,c_53879])).

tff(c_53897,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),'#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53886,c_90])).

tff(c_53903,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53768,c_53897])).

tff(c_53895,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53886,c_114])).

tff(c_53892,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53886,c_115])).

tff(c_44,plain,(
    ! [C_35,A_32,B_33] :
      ( ~ v1_xboole_0(C_35)
      | ~ v1_funct_2(C_35,A_32,B_33)
      | ~ v1_funct_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | v1_xboole_0(B_33)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54401,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_53892,c_44])).

tff(c_54425,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_53895,c_53738,c_54401])).

tff(c_54599,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_54425])).

tff(c_54612,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54599,c_53769])).

tff(c_68,plain,(
    ! [A_43] :
      ( m1_subset_1(u1_pre_topc(A_43),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_43))))
      | ~ l1_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_440,plain,(
    ! [A_156,B_157] :
      ( v1_pre_topc(g1_pre_topc(A_156,B_157))
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k1_zfmisc_1(A_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_448,plain,(
    ! [A_43] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_43),u1_pre_topc(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_68,c_440])).

tff(c_54639,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_54612,c_448])).

tff(c_69816,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_54639])).

tff(c_69907,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_330,c_69816])).

tff(c_69914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_69907])).

tff(c_69916,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_54639])).

tff(c_198,plain,(
    ! [B_113] : m1_subset_1('#skF_3'(k1_xboole_0,B_113),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_181])).

tff(c_202,plain,(
    ! [B_113] : r1_tarski('#skF_3'(k1_xboole_0,B_113),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_198,c_22])).

tff(c_53764,plain,(
    ! [B_113] : r1_tarski('#skF_3'('#skF_6',B_113),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53751,c_53751,c_202])).

tff(c_54095,plain,(
    ! [B_2326] : v1_xboole_0('#skF_3'('#skF_6',B_2326)) ),
    inference(resolution,[status(thm)],[c_53764,c_54041])).

tff(c_54177,plain,(
    ! [B_2329] : '#skF_3'('#skF_6',B_2329) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54095,c_53769])).

tff(c_54191,plain,(
    ! [B_2329] : v1_funct_2('#skF_6','#skF_6',B_2329) ),
    inference(superposition,[status(thm),theory(equality)],[c_54177,c_52])).

tff(c_54105,plain,(
    ! [B_2326] : '#skF_3'('#skF_6',B_2326) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54095,c_53769])).

tff(c_53893,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53886,c_464])).

tff(c_54356,plain,(
    ! [D_2349,A_2350,B_2351] :
      ( v5_pre_topc(D_2349,A_2350,B_2351)
      | ~ v5_pre_topc(D_2349,A_2350,g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351)))
      | ~ m1_subset_1(D_2349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2350),u1_struct_0(g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351))))))
      | ~ v1_funct_2(D_2349,u1_struct_0(A_2350),u1_struct_0(g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351))))
      | ~ m1_subset_1(D_2349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2350),u1_struct_0(B_2351))))
      | ~ v1_funct_2(D_2349,u1_struct_0(A_2350),u1_struct_0(B_2351))
      | ~ v1_funct_1(D_2349)
      | ~ l1_pre_topc(B_2351)
      | ~ v2_pre_topc(B_2351)
      | ~ l1_pre_topc(A_2350)
      | ~ v2_pre_topc(A_2350) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_54366,plain,(
    ! [A_2350,B_2351] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_2350),u1_struct_0(g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351)))),A_2350,B_2351)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_2350),u1_struct_0(g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351)))),A_2350,g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351)))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_2350),u1_struct_0(g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351)))),u1_struct_0(A_2350),u1_struct_0(g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351))))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_2350),u1_struct_0(g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2350),u1_struct_0(B_2351))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_2350),u1_struct_0(g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351)))),u1_struct_0(A_2350),u1_struct_0(B_2351))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(A_2350),u1_struct_0(g1_pre_topc(u1_struct_0(B_2351),u1_pre_topc(B_2351)))))
      | ~ l1_pre_topc(B_2351)
      | ~ v2_pre_topc(B_2351)
      | ~ l1_pre_topc(A_2350)
      | ~ v2_pre_topc(A_2350) ) ),
    inference(resolution,[status(thm)],[c_62,c_54356])).

tff(c_61561,plain,(
    ! [A_2729,B_2730] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_2729),u1_struct_0(g1_pre_topc(u1_struct_0(B_2730),u1_pre_topc(B_2730)))),A_2729,B_2730)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_2729),u1_struct_0(g1_pre_topc(u1_struct_0(B_2730),u1_pre_topc(B_2730)))),A_2729,g1_pre_topc(u1_struct_0(B_2730),u1_pre_topc(B_2730)))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_2729),u1_struct_0(g1_pre_topc(u1_struct_0(B_2730),u1_pre_topc(B_2730)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2729),u1_struct_0(B_2730))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_2729),u1_struct_0(g1_pre_topc(u1_struct_0(B_2730),u1_pre_topc(B_2730)))),u1_struct_0(A_2729),u1_struct_0(B_2730))
      | ~ l1_pre_topc(B_2730)
      | ~ v2_pre_topc(B_2730)
      | ~ l1_pre_topc(A_2729)
      | ~ v2_pre_topc(A_2729) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_54366])).

tff(c_61575,plain,(
    ! [A_2729] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_2729),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),A_2729,'#skF_5')
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_2729),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),A_2729,g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_2729),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2729),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_2729),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),u1_struct_0(A_2729),u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_2729)
      | ~ v2_pre_topc(A_2729) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53886,c_61561])).

tff(c_77718,plain,(
    ! [A_3339] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_3339),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),A_3339,'#skF_5')
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_3339),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),A_3339,g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_3339),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_3339),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),u1_struct_0(A_3339),'#skF_6')
      | ~ l1_pre_topc(A_3339)
      | ~ v2_pre_topc(A_3339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_53886,c_53886,c_53768,c_53886,c_53886,c_53886,c_53886,c_61575])).

tff(c_77732,plain,
    ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ v5_pre_topc('#skF_3'('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),k1_zfmisc_1('#skF_6'))
    | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),'#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_54612,c_77718])).

tff(c_77744,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69916,c_54191,c_54105,c_54612,c_54612,c_53903,c_54105,c_54612,c_53893,c_54105,c_54105,c_54612,c_77732])).

tff(c_77748,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_77744])).

tff(c_77751,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_77748])).

tff(c_77755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_77751])).

tff(c_77756,plain,(
    v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_77744])).

tff(c_54071,plain,(
    ! [A_2322] : '#skF_3'(A_2322,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_54061,c_53769])).

tff(c_54546,plain,(
    ! [D_2370,A_2371,B_2372] :
      ( v5_pre_topc(D_2370,A_2371,B_2372)
      | ~ v5_pre_topc(D_2370,g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371)),B_2372)
      | ~ m1_subset_1(D_2370,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371))),u1_struct_0(B_2372))))
      | ~ v1_funct_2(D_2370,u1_struct_0(g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371))),u1_struct_0(B_2372))
      | ~ m1_subset_1(D_2370,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2371),u1_struct_0(B_2372))))
      | ~ v1_funct_2(D_2370,u1_struct_0(A_2371),u1_struct_0(B_2372))
      | ~ v1_funct_1(D_2370)
      | ~ l1_pre_topc(B_2372)
      | ~ v2_pre_topc(B_2372)
      | ~ l1_pre_topc(A_2371)
      | ~ v2_pre_topc(A_2371) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54559,plain,(
    ! [A_2371,B_2372] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371))),u1_struct_0(B_2372)),A_2371,B_2372)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371))),u1_struct_0(B_2372)),g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371)),B_2372)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371))),u1_struct_0(B_2372)),u1_struct_0(g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371))),u1_struct_0(B_2372))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371))),u1_struct_0(B_2372)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2371),u1_struct_0(B_2372))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371))),u1_struct_0(B_2372)),u1_struct_0(A_2371),u1_struct_0(B_2372))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371),u1_pre_topc(A_2371))),u1_struct_0(B_2372)))
      | ~ l1_pre_topc(B_2372)
      | ~ v2_pre_topc(B_2372)
      | ~ l1_pre_topc(A_2371)
      | ~ v2_pre_topc(A_2371) ) ),
    inference(resolution,[status(thm)],[c_62,c_54546])).

tff(c_58803,plain,(
    ! [A_2624,B_2625] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624))),u1_struct_0(B_2625)),A_2624,B_2625)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624))),u1_struct_0(B_2625)),g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624)),B_2625)
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624))),u1_struct_0(B_2625)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2624),u1_struct_0(B_2625))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624))),u1_struct_0(B_2625)),u1_struct_0(A_2624),u1_struct_0(B_2625))
      | ~ l1_pre_topc(B_2625)
      | ~ v2_pre_topc(B_2625)
      | ~ l1_pre_topc(A_2624)
      | ~ v2_pre_topc(A_2624) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_54559])).

tff(c_58815,plain,(
    ! [A_2624] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624))),u1_struct_0('#skF_5')),A_2624,'#skF_5')
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624))),'#skF_6'),g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624)),'#skF_5')
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624))),u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2624),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624))),u1_struct_0('#skF_5')),u1_struct_0(A_2624),u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_2624)
      | ~ v2_pre_topc(A_2624) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53886,c_58803])).

tff(c_58827,plain,(
    ! [A_2624] :
      ( v5_pre_topc('#skF_6',A_2624,'#skF_5')
      | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_2624),u1_pre_topc(A_2624)),'#skF_5')
      | ~ l1_pre_topc(A_2624)
      | ~ v2_pre_topc(A_2624) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_54140,c_54071,c_53886,c_53886,c_53903,c_54071,c_53768,c_53886,c_53886,c_54071,c_54071,c_53886,c_58815])).

tff(c_77760,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_77756,c_58827])).

tff(c_77763,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_77760])).

tff(c_77765,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_77763])).

tff(c_77766,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_54425])).

tff(c_77780,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_77766,c_53769])).

tff(c_53907,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_53886,c_70])).

tff(c_53920,plain,(
    v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_53907])).

tff(c_53913,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_53886,c_330])).

tff(c_53924,plain,(
    l1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_53913])).

tff(c_54549,plain,
    ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_53892,c_54546])).

tff(c_54566,plain,
    ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_53920,c_53924,c_94,c_53895,c_53893,c_54549])).

tff(c_78035,plain,(
    v5_pre_topc('#skF_6','#skF_4',g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54140,c_77780,c_53903,c_53768,c_77780,c_54566])).

tff(c_79385,plain,(
    ! [A_3454,A_3455,B_3456] :
      ( v5_pre_topc(A_3454,A_3455,B_3456)
      | ~ v5_pre_topc(A_3454,A_3455,g1_pre_topc(u1_struct_0(B_3456),u1_pre_topc(B_3456)))
      | ~ v1_funct_2(A_3454,u1_struct_0(A_3455),u1_struct_0(g1_pre_topc(u1_struct_0(B_3456),u1_pre_topc(B_3456))))
      | ~ m1_subset_1(A_3454,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3455),u1_struct_0(B_3456))))
      | ~ v1_funct_2(A_3454,u1_struct_0(A_3455),u1_struct_0(B_3456))
      | ~ v1_funct_1(A_3454)
      | ~ l1_pre_topc(B_3456)
      | ~ v2_pre_topc(B_3456)
      | ~ l1_pre_topc(A_3455)
      | ~ v2_pre_topc(A_3455)
      | ~ r1_tarski(A_3454,k2_zfmisc_1(u1_struct_0(A_3455),u1_struct_0(g1_pre_topc(u1_struct_0(B_3456),u1_pre_topc(B_3456))))) ) ),
    inference(resolution,[status(thm)],[c_24,c_54356])).

tff(c_79413,plain,(
    ! [A_3454,A_3455] :
      ( v5_pre_topc(A_3454,A_3455,'#skF_5')
      | ~ v5_pre_topc(A_3454,A_3455,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v1_funct_2(A_3454,u1_struct_0(A_3455),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
      | ~ m1_subset_1(A_3454,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3455),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(A_3454,u1_struct_0(A_3455),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(A_3454)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_3455)
      | ~ v2_pre_topc(A_3455)
      | ~ r1_tarski(A_3454,k2_zfmisc_1(u1_struct_0(A_3455),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53886,c_79385])).

tff(c_79516,plain,(
    ! [A_3461,A_3462] :
      ( v5_pre_topc(A_3461,A_3462,'#skF_5')
      | ~ v5_pre_topc(A_3461,A_3462,g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
      | ~ m1_subset_1(A_3461,k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2(A_3461,u1_struct_0(A_3462),'#skF_6')
      | ~ v1_funct_1(A_3461)
      | ~ l1_pre_topc(A_3462)
      | ~ v2_pre_topc(A_3462)
      | ~ r1_tarski(A_3461,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53768,c_77780,c_98,c_96,c_53886,c_53768,c_53886,c_77780,c_53886,c_53886,c_79413])).

tff(c_79519,plain,
    ( v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),'#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_78035,c_79516])).

tff(c_79525,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_102,c_100,c_94,c_54140,c_53903,c_79519])).

tff(c_79527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_421,c_79525])).

tff(c_79529,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_356,plain,(
    ! [C_141,B_142,A_143] :
      ( r2_hidden(C_141,B_142)
      | ~ r2_hidden(C_141,A_143)
      | ~ r1_tarski(A_143,B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82229,plain,(
    ! [A_3661,B_3662,B_3663] :
      ( r2_hidden('#skF_2'(A_3661,B_3662),B_3663)
      | ~ r1_tarski(A_3661,B_3663)
      | r1_tarski(A_3661,B_3662) ) ),
    inference(resolution,[status(thm)],[c_10,c_356])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89102,plain,(
    ! [A_3991,B_3992,B_3993,B_3994] :
      ( r2_hidden('#skF_2'(A_3991,B_3992),B_3993)
      | ~ r1_tarski(B_3994,B_3993)
      | ~ r1_tarski(A_3991,B_3994)
      | r1_tarski(A_3991,B_3992) ) ),
    inference(resolution,[status(thm)],[c_82229,c_6])).

tff(c_98779,plain,(
    ! [A_4344,B_4345,A_4346] :
      ( r2_hidden('#skF_2'(A_4344,B_4345),k1_zfmisc_1(u1_struct_0(A_4346)))
      | ~ r1_tarski(A_4344,u1_pre_topc(A_4346))
      | r1_tarski(A_4344,B_4345)
      | ~ l1_pre_topc(A_4346) ) ),
    inference(resolution,[status(thm)],[c_332,c_89102])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98802,plain,(
    ! [A_4347,A_4348] :
      ( ~ r1_tarski(A_4347,u1_pre_topc(A_4348))
      | r1_tarski(A_4347,k1_zfmisc_1(u1_struct_0(A_4348)))
      | ~ l1_pre_topc(A_4348) ) ),
    inference(resolution,[status(thm)],[c_98779,c_8])).

tff(c_314,plain,(
    ! [A_131,B_132] :
      ( l1_pre_topc(g1_pre_topc(A_131,B_132))
      | ~ m1_subset_1(B_132,k1_zfmisc_1(k1_zfmisc_1(A_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_319,plain,(
    ! [A_131,A_13] :
      ( l1_pre_topc(g1_pre_topc(A_131,A_13))
      | ~ r1_tarski(A_13,k1_zfmisc_1(A_131)) ) ),
    inference(resolution,[status(thm)],[c_24,c_314])).

tff(c_98857,plain,(
    ! [A_4348,A_4347] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_4348),A_4347))
      | ~ r1_tarski(A_4347,u1_pre_topc(A_4348))
      | ~ l1_pre_topc(A_4348) ) ),
    inference(resolution,[status(thm)],[c_98802,c_319])).

tff(c_79680,plain,(
    ! [C_3500,B_3501,A_3502] :
      ( v1_xboole_0(C_3500)
      | ~ m1_subset_1(C_3500,k1_zfmisc_1(k2_zfmisc_1(B_3501,A_3502)))
      | ~ v1_xboole_0(A_3502) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_79703,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_90,c_79680])).

tff(c_79708,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_79703])).

tff(c_79972,plain,(
    ! [B_3524,A_3525] :
      ( k1_relat_1(B_3524) = A_3525
      | ~ v1_partfun1(B_3524,A_3525)
      | ~ v4_relat_1(B_3524,A_3525)
      | ~ v1_relat_1(B_3524) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_79990,plain,
    ( u1_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_4'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_383,c_79972])).

tff(c_80007,plain,
    ( u1_struct_0('#skF_4') = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_79990])).

tff(c_80017,plain,(
    ~ v1_partfun1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_80007])).

tff(c_80458,plain,(
    ! [C_3557,A_3558,B_3559] :
      ( v1_partfun1(C_3557,A_3558)
      | ~ v1_funct_2(C_3557,A_3558,B_3559)
      | ~ v1_funct_1(C_3557)
      | ~ m1_subset_1(C_3557,k1_zfmisc_1(k2_zfmisc_1(A_3558,B_3559)))
      | v1_xboole_0(B_3559) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_80477,plain,
    ( v1_partfun1('#skF_6',u1_struct_0('#skF_4'))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_90,c_80458])).

tff(c_80494,plain,
    ( v1_partfun1('#skF_6',u1_struct_0('#skF_4'))
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_80477])).

tff(c_80496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79708,c_80017,c_80494])).

tff(c_80497,plain,(
    u1_struct_0('#skF_4') = k1_relat_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_80007])).

tff(c_79528,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_80579,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80497,c_79528])).

tff(c_79700,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_115,c_79680])).

tff(c_80757,plain,(
    ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_79700])).

tff(c_80502,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80497,c_114])).

tff(c_80500,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80497,c_115])).

tff(c_81433,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(resolution,[status(thm)],[c_80500,c_38])).

tff(c_81455,plain,
    ( v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_80502,c_81433])).

tff(c_81456,plain,(
    v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')))) ),
    inference(negUnitSimplification,[status(thm)],[c_80757,c_81455])).

tff(c_79638,plain,(
    v4_relat_1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_115,c_34])).

tff(c_79975,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_79638,c_79972])).

tff(c_79996,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = k1_relat_1('#skF_6')
    | ~ v1_partfun1('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_79975])).

tff(c_81725,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))) = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_81456,c_80497,c_80497,c_79996])).

tff(c_79642,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))) ),
    inference(resolution,[status(thm)],[c_115,c_22])).

tff(c_81241,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80497,c_79642])).

tff(c_81728,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81725,c_81241])).

tff(c_81729,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81725,c_80502])).

tff(c_81727,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81725,c_80500])).

tff(c_81165,plain,(
    ! [D_3596,A_3597,B_3598] :
      ( v5_pre_topc(D_3596,g1_pre_topc(u1_struct_0(A_3597),u1_pre_topc(A_3597)),B_3598)
      | ~ v5_pre_topc(D_3596,A_3597,B_3598)
      | ~ m1_subset_1(D_3596,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3597),u1_pre_topc(A_3597))),u1_struct_0(B_3598))))
      | ~ v1_funct_2(D_3596,u1_struct_0(g1_pre_topc(u1_struct_0(A_3597),u1_pre_topc(A_3597))),u1_struct_0(B_3598))
      | ~ m1_subset_1(D_3596,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3597),u1_struct_0(B_3598))))
      | ~ v1_funct_2(D_3596,u1_struct_0(A_3597),u1_struct_0(B_3598))
      | ~ v1_funct_1(D_3596)
      | ~ l1_pre_topc(B_3598)
      | ~ v2_pre_topc(B_3598)
      | ~ l1_pre_topc(A_3597)
      | ~ v2_pre_topc(A_3597) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_85025,plain,(
    ! [A_3821,A_3822,B_3823] :
      ( v5_pre_topc(A_3821,g1_pre_topc(u1_struct_0(A_3822),u1_pre_topc(A_3822)),B_3823)
      | ~ v5_pre_topc(A_3821,A_3822,B_3823)
      | ~ v1_funct_2(A_3821,u1_struct_0(g1_pre_topc(u1_struct_0(A_3822),u1_pre_topc(A_3822))),u1_struct_0(B_3823))
      | ~ m1_subset_1(A_3821,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3822),u1_struct_0(B_3823))))
      | ~ v1_funct_2(A_3821,u1_struct_0(A_3822),u1_struct_0(B_3823))
      | ~ v1_funct_1(A_3821)
      | ~ l1_pre_topc(B_3823)
      | ~ v2_pre_topc(B_3823)
      | ~ l1_pre_topc(A_3822)
      | ~ v2_pre_topc(A_3822)
      | ~ r1_tarski(A_3821,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3822),u1_pre_topc(A_3822))),u1_struct_0(B_3823))) ) ),
    inference(resolution,[status(thm)],[c_24,c_81165])).

tff(c_85058,plain,(
    ! [A_3821,B_3823] :
      ( v5_pre_topc(A_3821,g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),B_3823)
      | ~ v5_pre_topc(A_3821,'#skF_4',B_3823)
      | ~ v1_funct_2(A_3821,u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(B_3823))
      | ~ m1_subset_1(A_3821,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_3823))))
      | ~ v1_funct_2(A_3821,u1_struct_0('#skF_4'),u1_struct_0(B_3823))
      | ~ v1_funct_1(A_3821)
      | ~ l1_pre_topc(B_3823)
      | ~ v2_pre_topc(B_3823)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ r1_tarski(A_3821,k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4'))),u1_struct_0(B_3823))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80497,c_85025])).

tff(c_120419,plain,(
    ! [A_5019,B_5020] :
      ( v5_pre_topc(A_5019,g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),B_5020)
      | ~ v5_pre_topc(A_5019,'#skF_4',B_5020)
      | ~ m1_subset_1(A_5019,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(B_5020))))
      | ~ v1_funct_2(A_5019,k1_relat_1('#skF_6'),u1_struct_0(B_5020))
      | ~ v1_funct_1(A_5019)
      | ~ l1_pre_topc(B_5020)
      | ~ v2_pre_topc(B_5020)
      | ~ r1_tarski(A_5019,k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(B_5020))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81725,c_102,c_100,c_80497,c_80497,c_81725,c_80497,c_80497,c_85058])).

tff(c_120422,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ r1_tarski('#skF_6',k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))) ),
    inference(resolution,[status(thm)],[c_81727,c_120419])).

tff(c_120442,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(k1_relat_1('#skF_6'),u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81728,c_94,c_81729,c_120422])).

tff(c_120443,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_80579,c_120442])).

tff(c_120675,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_120443])).

tff(c_120678,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_120675])).

tff(c_120682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_120678])).

tff(c_120683,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_120443])).

tff(c_120685,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_120683])).

tff(c_80505,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80497,c_92])).

tff(c_80504,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80497,c_90])).

tff(c_81928,plain,(
    ! [D_3645,A_3646,B_3647] :
      ( v5_pre_topc(D_3645,A_3646,g1_pre_topc(u1_struct_0(B_3647),u1_pre_topc(B_3647)))
      | ~ v5_pre_topc(D_3645,A_3646,B_3647)
      | ~ m1_subset_1(D_3645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3646),u1_struct_0(g1_pre_topc(u1_struct_0(B_3647),u1_pre_topc(B_3647))))))
      | ~ v1_funct_2(D_3645,u1_struct_0(A_3646),u1_struct_0(g1_pre_topc(u1_struct_0(B_3647),u1_pre_topc(B_3647))))
      | ~ m1_subset_1(D_3645,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3646),u1_struct_0(B_3647))))
      | ~ v1_funct_2(D_3645,u1_struct_0(A_3646),u1_struct_0(B_3647))
      | ~ v1_funct_1(D_3645)
      | ~ l1_pre_topc(B_3647)
      | ~ v2_pre_topc(B_3647)
      | ~ l1_pre_topc(A_3646)
      | ~ v2_pre_topc(A_3646) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_84353,plain,(
    ! [A_3779,A_3780,B_3781] :
      ( v5_pre_topc(A_3779,A_3780,g1_pre_topc(u1_struct_0(B_3781),u1_pre_topc(B_3781)))
      | ~ v5_pre_topc(A_3779,A_3780,B_3781)
      | ~ v1_funct_2(A_3779,u1_struct_0(A_3780),u1_struct_0(g1_pre_topc(u1_struct_0(B_3781),u1_pre_topc(B_3781))))
      | ~ m1_subset_1(A_3779,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3780),u1_struct_0(B_3781))))
      | ~ v1_funct_2(A_3779,u1_struct_0(A_3780),u1_struct_0(B_3781))
      | ~ v1_funct_1(A_3779)
      | ~ l1_pre_topc(B_3781)
      | ~ v2_pre_topc(B_3781)
      | ~ l1_pre_topc(A_3780)
      | ~ v2_pre_topc(A_3780)
      | ~ r1_tarski(A_3779,k2_zfmisc_1(u1_struct_0(A_3780),u1_struct_0(g1_pre_topc(u1_struct_0(B_3781),u1_pre_topc(B_3781))))) ) ),
    inference(resolution,[status(thm)],[c_24,c_81928])).

tff(c_84378,plain,(
    ! [A_3779,B_3781] :
      ( v5_pre_topc(A_3779,'#skF_4',g1_pre_topc(u1_struct_0(B_3781),u1_pre_topc(B_3781)))
      | ~ v5_pre_topc(A_3779,'#skF_4',B_3781)
      | ~ v1_funct_2(A_3779,u1_struct_0('#skF_4'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3781),u1_pre_topc(B_3781))))
      | ~ m1_subset_1(A_3779,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_3781))))
      | ~ v1_funct_2(A_3779,u1_struct_0('#skF_4'),u1_struct_0(B_3781))
      | ~ v1_funct_1(A_3779)
      | ~ l1_pre_topc(B_3781)
      | ~ v2_pre_topc(B_3781)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ r1_tarski(A_3779,k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(B_3781),u1_pre_topc(B_3781))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80497,c_84353])).

tff(c_127974,plain,(
    ! [A_5257,B_5258] :
      ( v5_pre_topc(A_5257,'#skF_4',g1_pre_topc(u1_struct_0(B_5258),u1_pre_topc(B_5258)))
      | ~ v5_pre_topc(A_5257,'#skF_4',B_5258)
      | ~ v1_funct_2(A_5257,k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(B_5258),u1_pre_topc(B_5258))))
      | ~ m1_subset_1(A_5257,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(B_5258))))
      | ~ v1_funct_2(A_5257,k1_relat_1('#skF_6'),u1_struct_0(B_5258))
      | ~ v1_funct_1(A_5257)
      | ~ l1_pre_topc(B_5258)
      | ~ v2_pre_topc(B_5258)
      | ~ r1_tarski(A_5257,k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0(B_5258),u1_pre_topc(B_5258))))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_80497,c_80497,c_80497,c_84378])).

tff(c_128027,plain,
    ( v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),u1_struct_0('#skF_5'))))
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),u1_struct_0('#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_81728,c_127974])).

tff(c_128092,plain,(
    v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_94,c_80505,c_80504,c_81729,c_79529,c_128027])).

tff(c_128094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120685,c_128092])).

tff(c_128095,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_120683])).

tff(c_128099,plain,
    ( ~ r1_tarski(u1_pre_topc('#skF_5'),u1_pre_topc('#skF_5'))
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_98857,c_128095])).

tff(c_128109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_308,c_128099])).

tff(c_128110,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_79700])).

tff(c_128126,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_128110,c_14])).

tff(c_79696,plain,(
    ! [C_3500] :
      ( v1_xboole_0(C_3500)
      | ~ m1_subset_1(C_3500,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_79680])).

tff(c_79725,plain,(
    ! [C_3508] :
      ( v1_xboole_0(C_3508)
      | ~ m1_subset_1(C_3508,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_79696])).

tff(c_79739,plain,(
    ! [B_3509] : v1_xboole_0('#skF_3'(k1_xboole_0,B_3509)) ),
    inference(resolution,[status(thm)],[c_190,c_79725])).

tff(c_79778,plain,(
    ! [B_3511] : '#skF_3'(k1_xboole_0,B_3511) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79739,c_14])).

tff(c_79807,plain,(
    ! [B_3511] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_3511) ),
    inference(superposition,[status(thm),theory(equality)],[c_79778,c_52])).

tff(c_128136,plain,(
    ! [B_3511] : v1_funct_2('#skF_6','#skF_6',B_3511) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128126,c_128126,c_79807])).

tff(c_79751,plain,(
    ! [B_3509] : '#skF_3'(k1_xboole_0,B_3509) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79739,c_14])).

tff(c_80715,plain,(
    ! [C_3567,A_3568,B_3569] :
      ( v1_partfun1(C_3567,A_3568)
      | ~ v1_funct_2(C_3567,A_3568,B_3569)
      | ~ v1_funct_1(C_3567)
      | ~ m1_subset_1(C_3567,k1_zfmisc_1(k2_zfmisc_1(A_3568,B_3569)))
      | v1_xboole_0(B_3569) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_80721,plain,(
    ! [A_38,B_39] :
      ( v1_partfun1('#skF_3'(A_38,B_39),A_38)
      | ~ v1_funct_2('#skF_3'(A_38,B_39),A_38,B_39)
      | ~ v1_funct_1('#skF_3'(A_38,B_39))
      | v1_xboole_0(B_39) ) ),
    inference(resolution,[status(thm)],[c_62,c_80715])).

tff(c_80741,plain,(
    ! [A_3570,B_3571] :
      ( v1_partfun1('#skF_3'(A_3570,B_3571),A_3570)
      | v1_xboole_0(B_3571) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_80721])).

tff(c_80750,plain,(
    ! [B_3509] :
      ( v1_partfun1(k1_xboole_0,k1_xboole_0)
      | v1_xboole_0(B_3509) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79751,c_80741])).

tff(c_80752,plain,(
    v1_partfun1(k1_xboole_0,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_80750])).

tff(c_127,plain,(
    ! [B_89] : k2_zfmisc_1(k1_xboole_0,B_89) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_28])).

tff(c_79590,plain,(
    ! [A_3486,A_3487,B_3488] :
      ( v4_relat_1(A_3486,A_3487)
      | ~ r1_tarski(A_3486,k2_zfmisc_1(A_3487,B_3488)) ) ),
    inference(resolution,[status(thm)],[c_24,c_363])).

tff(c_79617,plain,(
    ! [A_3489,B_3490] : v4_relat_1(k2_zfmisc_1(A_3489,B_3490),A_3489) ),
    inference(resolution,[status(thm)],[c_308,c_79590])).

tff(c_79620,plain,(
    ! [A_11] : v4_relat_1(k1_xboole_0,A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_79617])).

tff(c_79981,plain,(
    ! [A_11] :
      ( k1_relat_1(k1_xboole_0) = A_11
      | ~ v1_partfun1(k1_xboole_0,A_11)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_79620,c_79972])).

tff(c_80000,plain,(
    ! [A_11] :
      ( k1_relat_1(k1_xboole_0) = A_11
      | ~ v1_partfun1(k1_xboole_0,A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_79981])).

tff(c_80756,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_80752,c_80000])).

tff(c_128182,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128126,c_128126,c_80756])).

tff(c_128195,plain,(
    u1_struct_0('#skF_4') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128182,c_80497])).

tff(c_128152,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_6',B_12) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128126,c_128126,c_20])).

tff(c_128140,plain,(
    ! [B_3509] : '#skF_3'('#skF_6',B_3509) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128126,c_128126,c_79751])).

tff(c_191,plain,(
    ! [A_109,B_110] : r1_tarski('#skF_3'(A_109,B_110),k2_zfmisc_1(A_109,B_110)) ),
    inference(resolution,[status(thm)],[c_181,c_22])).

tff(c_129473,plain,(
    ! [A_5341,B_5342,B_5343] :
      ( r2_hidden('#skF_2'(A_5341,B_5342),B_5343)
      | ~ r1_tarski(A_5341,B_5343)
      | r1_tarski(A_5341,B_5342) ) ),
    inference(resolution,[status(thm)],[c_10,c_356])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129486,plain,(
    ! [B_5344,A_5345,B_5346] :
      ( ~ v1_xboole_0(B_5344)
      | ~ r1_tarski(A_5345,B_5344)
      | r1_tarski(A_5345,B_5346) ) ),
    inference(resolution,[status(thm)],[c_129473,c_2])).

tff(c_129584,plain,(
    ! [A_5351,B_5352,B_5353] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_5351,B_5352))
      | r1_tarski('#skF_3'(A_5351,B_5352),B_5353) ) ),
    inference(resolution,[status(thm)],[c_191,c_129486])).

tff(c_129625,plain,(
    ! [B_3509,B_5353] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6',B_3509))
      | r1_tarski('#skF_6',B_5353) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128140,c_129584])).

tff(c_129640,plain,(
    ! [B_5353] : r1_tarski('#skF_6',B_5353) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128110,c_128152,c_129625])).

tff(c_79710,plain,(
    ! [A_3506,B_3507] :
      ( v1_xboole_0('#skF_3'(A_3506,B_3507))
      | ~ v1_xboole_0(B_3507) ) ),
    inference(resolution,[status(thm)],[c_62,c_79680])).

tff(c_79722,plain,(
    ! [A_3506,B_3507] :
      ( '#skF_3'(A_3506,B_3507) = k1_xboole_0
      | ~ v1_xboole_0(B_3507) ) ),
    inference(resolution,[status(thm)],[c_79710,c_14])).

tff(c_128123,plain,(
    ! [A_3506] : '#skF_3'(A_3506,'#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_128110,c_79722])).

tff(c_128365,plain,(
    ! [A_3506] : '#skF_3'(A_3506,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128126,c_128123])).

tff(c_128111,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_79700])).

tff(c_128150,plain,(
    ! [A_10] :
      ( A_10 = '#skF_6'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128126,c_14])).

tff(c_128727,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_128111,c_128150])).

tff(c_128467,plain,(
    ! [D_5269,A_5270,B_5271] :
      ( v5_pre_topc(D_5269,A_5270,g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271)))
      | ~ v5_pre_topc(D_5269,A_5270,B_5271)
      | ~ m1_subset_1(D_5269,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5270),u1_struct_0(g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271))))))
      | ~ v1_funct_2(D_5269,u1_struct_0(A_5270),u1_struct_0(g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271))))
      | ~ m1_subset_1(D_5269,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5270),u1_struct_0(B_5271))))
      | ~ v1_funct_2(D_5269,u1_struct_0(A_5270),u1_struct_0(B_5271))
      | ~ v1_funct_1(D_5269)
      | ~ l1_pre_topc(B_5271)
      | ~ v2_pre_topc(B_5271)
      | ~ l1_pre_topc(A_5270)
      | ~ v2_pre_topc(A_5270) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_128477,plain,(
    ! [A_5270,B_5271] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_5270),u1_struct_0(g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271)))),A_5270,g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_5270),u1_struct_0(g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271)))),A_5270,B_5271)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_5270),u1_struct_0(g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271)))),u1_struct_0(A_5270),u1_struct_0(g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271))))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_5270),u1_struct_0(g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5270),u1_struct_0(B_5271))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_5270),u1_struct_0(g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271)))),u1_struct_0(A_5270),u1_struct_0(B_5271))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(A_5270),u1_struct_0(g1_pre_topc(u1_struct_0(B_5271),u1_pre_topc(B_5271)))))
      | ~ l1_pre_topc(B_5271)
      | ~ v2_pre_topc(B_5271)
      | ~ l1_pre_topc(A_5270)
      | ~ v2_pre_topc(A_5270) ) ),
    inference(resolution,[status(thm)],[c_62,c_128467])).

tff(c_132639,plain,(
    ! [A_5517,B_5518] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_5517),u1_struct_0(g1_pre_topc(u1_struct_0(B_5518),u1_pre_topc(B_5518)))),A_5517,g1_pre_topc(u1_struct_0(B_5518),u1_pre_topc(B_5518)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_5517),u1_struct_0(g1_pre_topc(u1_struct_0(B_5518),u1_pre_topc(B_5518)))),A_5517,B_5518)
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_5517),u1_struct_0(g1_pre_topc(u1_struct_0(B_5518),u1_pre_topc(B_5518)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5517),u1_struct_0(B_5518))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_5517),u1_struct_0(g1_pre_topc(u1_struct_0(B_5518),u1_pre_topc(B_5518)))),u1_struct_0(A_5517),u1_struct_0(B_5518))
      | ~ l1_pre_topc(B_5518)
      | ~ v2_pre_topc(B_5518)
      | ~ l1_pre_topc(A_5517)
      | ~ v2_pre_topc(A_5517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_128477])).

tff(c_141834,plain,(
    ! [A_5855,B_5856] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_5855),u1_struct_0(g1_pre_topc(u1_struct_0(B_5856),u1_pre_topc(B_5856)))),A_5855,g1_pre_topc(u1_struct_0(B_5856),u1_pre_topc(B_5856)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_5855),u1_struct_0(g1_pre_topc(u1_struct_0(B_5856),u1_pre_topc(B_5856)))),A_5855,B_5856)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_5855),u1_struct_0(g1_pre_topc(u1_struct_0(B_5856),u1_pre_topc(B_5856)))),u1_struct_0(A_5855),u1_struct_0(B_5856))
      | ~ l1_pre_topc(B_5856)
      | ~ v2_pre_topc(B_5856)
      | ~ l1_pre_topc(A_5855)
      | ~ v2_pre_topc(A_5855)
      | ~ r1_tarski('#skF_3'(u1_struct_0(A_5855),u1_struct_0(g1_pre_topc(u1_struct_0(B_5856),u1_pre_topc(B_5856)))),k2_zfmisc_1(u1_struct_0(A_5855),u1_struct_0(B_5856))) ) ),
    inference(resolution,[status(thm)],[c_24,c_132639])).

tff(c_141848,plain,(
    ! [A_5855] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_5855),'#skF_6'),A_5855,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_5855),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),A_5855,'#skF_5')
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_5855),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),u1_struct_0(A_5855),u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_5855)
      | ~ v2_pre_topc(A_5855)
      | ~ r1_tarski('#skF_3'(u1_struct_0(A_5855),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),k2_zfmisc_1(u1_struct_0(A_5855),u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128727,c_141834])).

tff(c_142215,plain,(
    ! [A_5875] :
      ( v5_pre_topc('#skF_6',A_5875,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_6',A_5875,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0(A_5875),u1_struct_0('#skF_5'))
      | ~ l1_pre_topc(A_5875)
      | ~ v2_pre_topc(A_5875) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129640,c_128365,c_128727,c_98,c_96,c_128365,c_128727,c_128365,c_128727,c_128365,c_141848])).

tff(c_128187,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128182,c_80579])).

tff(c_79548,plain,(
    ! [A_3467,B_3468] :
      ( v1_pre_topc(g1_pre_topc(A_3467,B_3468))
      | ~ m1_subset_1(B_3468,k1_zfmisc_1(k1_zfmisc_1(A_3467))) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_79556,plain,(
    ! [A_43] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_43),u1_pre_topc(A_43)))
      | ~ l1_pre_topc(A_43) ) ),
    inference(resolution,[status(thm)],[c_68,c_79548])).

tff(c_128817,plain,
    ( v1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_128727,c_79556])).

tff(c_129552,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_128817])).

tff(c_129555,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_330,c_129552])).

tff(c_129562,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_129555])).

tff(c_129564,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_128817])).

tff(c_128820,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_128727,c_70])).

tff(c_131365,plain,
    ( v2_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129564,c_128820])).

tff(c_131366,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_131365])).

tff(c_131369,plain,
    ( ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_131366])).

tff(c_131373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_131369])).

tff(c_131375,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_131365])).

tff(c_79754,plain,(
    ! [A_3510] : v1_xboole_0('#skF_3'(A_3510,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_187,c_79725])).

tff(c_79842,plain,(
    ! [A_3512] : '#skF_3'(A_3512,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79754,c_14])).

tff(c_79859,plain,(
    ! [A_3512] : v1_funct_2(k1_xboole_0,A_3512,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_79842,c_52])).

tff(c_128137,plain,(
    ! [A_3512] : v1_funct_2('#skF_6',A_3512,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_128126,c_128126,c_79859])).

tff(c_79773,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79751,c_190])).

tff(c_128138,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128126,c_128126,c_79773])).

tff(c_128149,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128126,c_128126,c_18])).

tff(c_128674,plain,(
    ! [D_5288,A_5289,B_5290] :
      ( v5_pre_topc(D_5288,g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289)),B_5290)
      | ~ v5_pre_topc(D_5288,A_5289,B_5290)
      | ~ m1_subset_1(D_5288,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289))),u1_struct_0(B_5290))))
      | ~ v1_funct_2(D_5288,u1_struct_0(g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289))),u1_struct_0(B_5290))
      | ~ m1_subset_1(D_5288,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5289),u1_struct_0(B_5290))))
      | ~ v1_funct_2(D_5288,u1_struct_0(A_5289),u1_struct_0(B_5290))
      | ~ v1_funct_1(D_5288)
      | ~ l1_pre_topc(B_5290)
      | ~ v2_pre_topc(B_5290)
      | ~ l1_pre_topc(A_5289)
      | ~ v2_pre_topc(A_5289) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_128684,plain,(
    ! [A_5289,B_5290] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289))),u1_struct_0(B_5290)),g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289)),B_5290)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289))),u1_struct_0(B_5290)),A_5289,B_5290)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289))),u1_struct_0(B_5290)),u1_struct_0(g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289))),u1_struct_0(B_5290))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289))),u1_struct_0(B_5290)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5289),u1_struct_0(B_5290))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289))),u1_struct_0(B_5290)),u1_struct_0(A_5289),u1_struct_0(B_5290))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289),u1_pre_topc(A_5289))),u1_struct_0(B_5290)))
      | ~ l1_pre_topc(B_5290)
      | ~ v2_pre_topc(B_5290)
      | ~ l1_pre_topc(A_5289)
      | ~ v2_pre_topc(A_5289) ) ),
    inference(resolution,[status(thm)],[c_62,c_128674])).

tff(c_133630,plain,(
    ! [A_5573,B_5574] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573))),u1_struct_0(B_5574)),g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573)),B_5574)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573))),u1_struct_0(B_5574)),A_5573,B_5574)
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573))),u1_struct_0(B_5574)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5573),u1_struct_0(B_5574))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573))),u1_struct_0(B_5574)),u1_struct_0(A_5573),u1_struct_0(B_5574))
      | ~ l1_pre_topc(B_5574)
      | ~ v2_pre_topc(B_5574)
      | ~ l1_pre_topc(A_5573)
      | ~ v2_pre_topc(A_5573) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_128684])).

tff(c_133636,plain,(
    ! [A_5573] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573)),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),A_5573,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573))),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5573),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573),u1_pre_topc(A_5573))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),u1_struct_0(A_5573),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(A_5573)
      | ~ v2_pre_topc(A_5573) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128727,c_133630])).

tff(c_136008,plain,(
    ! [A_5662] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_5662),u1_pre_topc(A_5662)),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_6',A_5662,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ l1_pre_topc(A_5662)
      | ~ v2_pre_topc(A_5662) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131375,c_129564,c_128137,c_128365,c_128727,c_128727,c_128138,c_128149,c_128365,c_128727,c_128365,c_128727,c_128365,c_128727,c_133636])).

tff(c_136017,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_128195,c_136008])).

tff(c_136022,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc('#skF_6',u1_pre_topc('#skF_4')),g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_136017])).

tff(c_136023,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4',g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_128187,c_136022])).

tff(c_142228,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_142215,c_136023])).

tff(c_142248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_128136,c_128195,c_79529,c_142228])).

tff(c_142249,plain,(
    ! [B_3509] : v1_xboole_0(B_3509) ),
    inference(splitRight,[status(thm)],[c_80750])).

tff(c_142289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142249,c_79708])).

tff(c_142290,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_79703])).

tff(c_142303,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_142290,c_14])).

tff(c_142319,plain,(
    ! [A_111] : r1_tarski('#skF_3'(A_111,'#skF_6'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142303,c_142303,c_196])).

tff(c_79705,plain,(
    ! [C_3500] :
      ( v1_xboole_0(C_3500)
      | ~ m1_subset_1(C_3500,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_79696])).

tff(c_142608,plain,(
    ! [C_5898] :
      ( v1_xboole_0(C_5898)
      | ~ m1_subset_1(C_5898,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142303,c_79705])).

tff(c_142619,plain,(
    ! [A_5899] :
      ( v1_xboole_0(A_5899)
      | ~ r1_tarski(A_5899,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_142608])).

tff(c_142639,plain,(
    ! [A_5900] : v1_xboole_0('#skF_3'(A_5900,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_142319,c_142619])).

tff(c_142322,plain,(
    ! [A_10] :
      ( A_10 = '#skF_6'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142303,c_14])).

tff(c_142678,plain,(
    ! [A_5902] : '#skF_3'(A_5902,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_142639,c_142322])).

tff(c_142704,plain,(
    ! [A_5902] : v1_funct_2('#skF_6',A_5902,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_142678,c_52])).

tff(c_142291,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_79703])).

tff(c_142448,plain,(
    ! [A_5881] :
      ( A_5881 = '#skF_6'
      | ~ v1_xboole_0(A_5881) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142303,c_14])).

tff(c_142455,plain,(
    u1_struct_0('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_142291,c_142448])).

tff(c_142649,plain,(
    ! [A_5900] : '#skF_3'(A_5900,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_142639,c_142322])).

tff(c_142321,plain,(
    ! [A_11] : k2_zfmisc_1(A_11,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142303,c_142303,c_18])).

tff(c_142464,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),'#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142455,c_90])).

tff(c_142470,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142321,c_142464])).

tff(c_161087,plain,(
    ! [D_6710,A_6711,B_6712] :
      ( v5_pre_topc(D_6710,g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711)),B_6712)
      | ~ v5_pre_topc(D_6710,A_6711,B_6712)
      | ~ m1_subset_1(D_6710,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711))),u1_struct_0(B_6712))))
      | ~ v1_funct_2(D_6710,u1_struct_0(g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711))),u1_struct_0(B_6712))
      | ~ m1_subset_1(D_6710,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6711),u1_struct_0(B_6712))))
      | ~ v1_funct_2(D_6710,u1_struct_0(A_6711),u1_struct_0(B_6712))
      | ~ v1_funct_1(D_6710)
      | ~ l1_pre_topc(B_6712)
      | ~ v2_pre_topc(B_6712)
      | ~ l1_pre_topc(A_6711)
      | ~ v2_pre_topc(A_6711) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_161103,plain,(
    ! [A_6711,B_6712] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711))),u1_struct_0(B_6712)),g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711)),B_6712)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711))),u1_struct_0(B_6712)),A_6711,B_6712)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711))),u1_struct_0(B_6712)),u1_struct_0(g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711))),u1_struct_0(B_6712))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711))),u1_struct_0(B_6712)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6711),u1_struct_0(B_6712))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711))),u1_struct_0(B_6712)),u1_struct_0(A_6711),u1_struct_0(B_6712))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711),u1_pre_topc(A_6711))),u1_struct_0(B_6712)))
      | ~ l1_pre_topc(B_6712)
      | ~ v2_pre_topc(B_6712)
      | ~ l1_pre_topc(A_6711)
      | ~ v2_pre_topc(A_6711) ) ),
    inference(resolution,[status(thm)],[c_62,c_161087])).

tff(c_165899,plain,(
    ! [A_7003,B_7004] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003))),u1_struct_0(B_7004)),g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003)),B_7004)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003))),u1_struct_0(B_7004)),A_7003,B_7004)
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003))),u1_struct_0(B_7004)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7003),u1_struct_0(B_7004))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003))),u1_struct_0(B_7004)),u1_struct_0(A_7003),u1_struct_0(B_7004))
      | ~ l1_pre_topc(B_7004)
      | ~ v2_pre_topc(B_7004)
      | ~ l1_pre_topc(A_7003)
      | ~ v2_pre_topc(A_7003) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_161103])).

tff(c_165915,plain,(
    ! [A_7003] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003))),u1_struct_0('#skF_5')),g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003)),'#skF_5')
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003))),u1_struct_0('#skF_5')),A_7003,'#skF_5')
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003))),u1_struct_0('#skF_5')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7003),'#skF_6')))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003),u1_pre_topc(A_7003))),u1_struct_0('#skF_5')),u1_struct_0(A_7003),u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_7003)
      | ~ v2_pre_topc(A_7003) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142455,c_165899])).

tff(c_173142,plain,(
    ! [A_7253] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_7253),u1_pre_topc(A_7253)),'#skF_5')
      | ~ v5_pre_topc('#skF_6',A_7253,'#skF_5')
      | ~ l1_pre_topc(A_7253)
      | ~ v2_pre_topc(A_7253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_142704,c_142455,c_142649,c_142455,c_142470,c_142321,c_142649,c_142455,c_142649,c_142455,c_142649,c_142455,c_165915])).

tff(c_143200,plain,(
    ! [D_5945,A_5946,B_5947] :
      ( v5_pre_topc(D_5945,g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946)),B_5947)
      | ~ v5_pre_topc(D_5945,A_5946,B_5947)
      | ~ m1_subset_1(D_5945,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946))),u1_struct_0(B_5947))))
      | ~ v1_funct_2(D_5945,u1_struct_0(g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946))),u1_struct_0(B_5947))
      | ~ m1_subset_1(D_5945,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5946),u1_struct_0(B_5947))))
      | ~ v1_funct_2(D_5945,u1_struct_0(A_5946),u1_struct_0(B_5947))
      | ~ v1_funct_1(D_5945)
      | ~ l1_pre_topc(B_5947)
      | ~ v2_pre_topc(B_5947)
      | ~ l1_pre_topc(A_5946)
      | ~ v2_pre_topc(A_5946) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_143219,plain,(
    ! [A_5946,B_5947] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946))),u1_struct_0(B_5947)),g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946)),B_5947)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946))),u1_struct_0(B_5947)),A_5946,B_5947)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946))),u1_struct_0(B_5947)),u1_struct_0(g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946))),u1_struct_0(B_5947))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946))),u1_struct_0(B_5947)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5946),u1_struct_0(B_5947))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946))),u1_struct_0(B_5947)),u1_struct_0(A_5946),u1_struct_0(B_5947))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946),u1_pre_topc(A_5946))),u1_struct_0(B_5947)))
      | ~ l1_pre_topc(B_5947)
      | ~ v2_pre_topc(B_5947)
      | ~ l1_pre_topc(A_5946)
      | ~ v2_pre_topc(A_5946) ) ),
    inference(resolution,[status(thm)],[c_62,c_143200])).

tff(c_146766,plain,(
    ! [A_6161,B_6162] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161))),u1_struct_0(B_6162)),g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161)),B_6162)
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161))),u1_struct_0(B_6162)),A_6161,B_6162)
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161))),u1_struct_0(B_6162)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6161),u1_struct_0(B_6162))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161))),u1_struct_0(B_6162)),u1_struct_0(A_6161),u1_struct_0(B_6162))
      | ~ l1_pre_topc(B_6162)
      | ~ v2_pre_topc(B_6162)
      | ~ l1_pre_topc(A_6161)
      | ~ v2_pre_topc(A_6161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_143219])).

tff(c_146780,plain,(
    ! [A_6161] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161))),u1_struct_0('#skF_5')),g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161)),'#skF_5')
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161))),u1_struct_0('#skF_5')),A_6161,'#skF_5')
      | ~ m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161))),'#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6161),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161))),u1_struct_0('#skF_5')),u1_struct_0(A_6161),u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_6161)
      | ~ v2_pre_topc(A_6161) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142455,c_146766])).

tff(c_146799,plain,(
    ! [A_6161] :
      ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0(A_6161),u1_pre_topc(A_6161)),'#skF_5')
      | ~ v5_pre_topc('#skF_6',A_6161,'#skF_5')
      | ~ l1_pre_topc(A_6161)
      | ~ v2_pre_topc(A_6161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_142704,c_142649,c_142455,c_142455,c_142470,c_142649,c_142321,c_142455,c_142649,c_142455,c_142649,c_142455,c_146780])).

tff(c_142606,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142455,c_79528])).

tff(c_142324,plain,(
    ! [B_12] : k2_zfmisc_1('#skF_6',B_12) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142303,c_142303,c_20])).

tff(c_142317,plain,(
    ! [B_113] : r1_tarski('#skF_3'('#skF_6',B_113),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142303,c_142303,c_202])).

tff(c_142655,plain,(
    ! [B_5901] : v1_xboole_0('#skF_3'('#skF_6',B_5901)) ),
    inference(resolution,[status(thm)],[c_142317,c_142619])).

tff(c_142665,plain,(
    ! [B_5901] : '#skF_3'('#skF_6',B_5901) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_142655,c_142322])).

tff(c_144035,plain,(
    ! [A_6002,B_6003,B_6004] :
      ( r2_hidden('#skF_2'(A_6002,B_6003),B_6004)
      | ~ r1_tarski(A_6002,B_6004)
      | r1_tarski(A_6002,B_6003) ) ),
    inference(resolution,[status(thm)],[c_10,c_356])).

tff(c_144048,plain,(
    ! [B_6005,A_6006,B_6007] :
      ( ~ v1_xboole_0(B_6005)
      | ~ r1_tarski(A_6006,B_6005)
      | r1_tarski(A_6006,B_6007) ) ),
    inference(resolution,[status(thm)],[c_144035,c_2])).

tff(c_144067,plain,(
    ! [A_6008,B_6009,B_6010] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_6008,B_6009))
      | r1_tarski('#skF_3'(A_6008,B_6009),B_6010) ) ),
    inference(resolution,[status(thm)],[c_191,c_144048])).

tff(c_144108,plain,(
    ! [B_5901,B_6010] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_6',B_5901))
      | r1_tarski('#skF_6',B_6010) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142665,c_144067])).

tff(c_144123,plain,(
    ! [B_6010] : r1_tarski('#skF_6',B_6010) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142290,c_142324,c_144108])).

tff(c_142462,plain,(
    v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142455,c_114])).

tff(c_142461,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142455,c_115])).

tff(c_142928,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))
    | ~ v1_funct_1('#skF_6')
    | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(resolution,[status(thm)],[c_142461,c_44])).

tff(c_142952,plain,
    ( v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_142462,c_142290,c_142928])).

tff(c_143030,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_142952])).

tff(c_143043,plain,(
    u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_143030,c_142322])).

tff(c_143084,plain,
    ( l1_pre_topc(g1_pre_topc('#skF_6',u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_143043,c_330])).

tff(c_158426,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_143084])).

tff(c_158451,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_330,c_158426])).

tff(c_158458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_158451])).

tff(c_158460,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_143084])).

tff(c_142739,plain,(
    ! [B_5903] : '#skF_3'('#skF_6',B_5903) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_142655,c_142322])).

tff(c_142756,plain,(
    ! [B_5903] : v1_funct_2('#skF_6','#skF_6',B_5903) ),
    inference(superposition,[status(thm),theory(equality)],[c_142739,c_52])).

tff(c_143101,plain,(
    ! [D_5932,A_5933,B_5934] :
      ( v5_pre_topc(D_5932,A_5933,g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934)))
      | ~ v5_pre_topc(D_5932,A_5933,B_5934)
      | ~ m1_subset_1(D_5932,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5933),u1_struct_0(g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934))))))
      | ~ v1_funct_2(D_5932,u1_struct_0(A_5933),u1_struct_0(g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934))))
      | ~ m1_subset_1(D_5932,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5933),u1_struct_0(B_5934))))
      | ~ v1_funct_2(D_5932,u1_struct_0(A_5933),u1_struct_0(B_5934))
      | ~ v1_funct_1(D_5932)
      | ~ l1_pre_topc(B_5934)
      | ~ v2_pre_topc(B_5934)
      | ~ l1_pre_topc(A_5933)
      | ~ v2_pre_topc(A_5933) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_143120,plain,(
    ! [A_5933,B_5934] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_5933),u1_struct_0(g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934)))),A_5933,g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_5933),u1_struct_0(g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934)))),A_5933,B_5934)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_5933),u1_struct_0(g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934)))),u1_struct_0(A_5933),u1_struct_0(g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934))))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_5933),u1_struct_0(g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5933),u1_struct_0(B_5934))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_5933),u1_struct_0(g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934)))),u1_struct_0(A_5933),u1_struct_0(B_5934))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(A_5933),u1_struct_0(g1_pre_topc(u1_struct_0(B_5934),u1_pre_topc(B_5934)))))
      | ~ l1_pre_topc(B_5934)
      | ~ v2_pre_topc(B_5934)
      | ~ l1_pre_topc(A_5933)
      | ~ v2_pre_topc(A_5933) ) ),
    inference(resolution,[status(thm)],[c_62,c_143101])).

tff(c_147793,plain,(
    ! [A_6219,B_6220] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_6219),u1_struct_0(g1_pre_topc(u1_struct_0(B_6220),u1_pre_topc(B_6220)))),A_6219,g1_pre_topc(u1_struct_0(B_6220),u1_pre_topc(B_6220)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_6219),u1_struct_0(g1_pre_topc(u1_struct_0(B_6220),u1_pre_topc(B_6220)))),A_6219,B_6220)
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_6219),u1_struct_0(g1_pre_topc(u1_struct_0(B_6220),u1_pre_topc(B_6220)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6219),u1_struct_0(B_6220))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_6219),u1_struct_0(g1_pre_topc(u1_struct_0(B_6220),u1_pre_topc(B_6220)))),u1_struct_0(A_6219),u1_struct_0(B_6220))
      | ~ l1_pre_topc(B_6220)
      | ~ v2_pre_topc(B_6220)
      | ~ l1_pre_topc(A_6219)
      | ~ v2_pre_topc(A_6219) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_143120])).

tff(c_157163,plain,(
    ! [A_6560,B_6561] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_6560),u1_struct_0(g1_pre_topc(u1_struct_0(B_6561),u1_pre_topc(B_6561)))),A_6560,g1_pre_topc(u1_struct_0(B_6561),u1_pre_topc(B_6561)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_6560),u1_struct_0(g1_pre_topc(u1_struct_0(B_6561),u1_pre_topc(B_6561)))),A_6560,B_6561)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_6560),u1_struct_0(g1_pre_topc(u1_struct_0(B_6561),u1_pre_topc(B_6561)))),u1_struct_0(A_6560),u1_struct_0(B_6561))
      | ~ l1_pre_topc(B_6561)
      | ~ v2_pre_topc(B_6561)
      | ~ l1_pre_topc(A_6560)
      | ~ v2_pre_topc(A_6560)
      | ~ r1_tarski('#skF_3'(u1_struct_0(A_6560),u1_struct_0(g1_pre_topc(u1_struct_0(B_6561),u1_pre_topc(B_6561)))),k2_zfmisc_1(u1_struct_0(A_6560),u1_struct_0(B_6561))) ) ),
    inference(resolution,[status(thm)],[c_24,c_147793])).

tff(c_157189,plain,(
    ! [A_6560] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_6560),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),A_6560,g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_6560),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),A_6560,'#skF_5')
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_6560),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),u1_struct_0(A_6560),u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_6560)
      | ~ v2_pre_topc(A_6560)
      | ~ r1_tarski('#skF_3'(u1_struct_0(A_6560),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),k2_zfmisc_1(u1_struct_0(A_6560),u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142455,c_157163])).

tff(c_160905,plain,(
    ! [A_6701] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_6701),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),A_6701,g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_6701),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),A_6701,'#skF_5')
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_6701),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),u1_struct_0(A_6701),'#skF_6')
      | ~ l1_pre_topc(A_6701)
      | ~ v2_pre_topc(A_6701)
      | ~ r1_tarski('#skF_3'(u1_struct_0(A_6701),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142321,c_142455,c_142455,c_98,c_96,c_142455,c_142455,c_142455,c_142455,c_157189])).

tff(c_160911,plain,
    ( v5_pre_topc('#skF_3'('#skF_6',u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),'#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ r1_tarski('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_143043,c_160905])).

tff(c_160919,plain,
    ( v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
    | ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144123,c_142665,c_143043,c_158460,c_142756,c_142665,c_143043,c_143043,c_142665,c_143043,c_142665,c_160911])).

tff(c_160920,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_142606,c_160919])).

tff(c_160924,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_160920])).

tff(c_160927,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_160924])).

tff(c_160931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_160927])).

tff(c_160932,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_160920])).

tff(c_160936,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_146799,c_160932])).

tff(c_160940,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_79529,c_160936])).

tff(c_160941,plain,(
    v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_142952])).

tff(c_160955,plain,(
    u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_160941,c_142322])).

tff(c_160958,plain,(
    ! [D_6702,A_6703,B_6704] :
      ( v5_pre_topc(D_6702,A_6703,g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704)))
      | ~ v5_pre_topc(D_6702,A_6703,B_6704)
      | ~ m1_subset_1(D_6702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6703),u1_struct_0(g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704))))))
      | ~ v1_funct_2(D_6702,u1_struct_0(A_6703),u1_struct_0(g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704))))
      | ~ m1_subset_1(D_6702,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6703),u1_struct_0(B_6704))))
      | ~ v1_funct_2(D_6702,u1_struct_0(A_6703),u1_struct_0(B_6704))
      | ~ v1_funct_1(D_6702)
      | ~ l1_pre_topc(B_6704)
      | ~ v2_pre_topc(B_6704)
      | ~ l1_pre_topc(A_6703)
      | ~ v2_pre_topc(A_6703) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_162883,plain,(
    ! [A_6852,A_6853,B_6854] :
      ( v5_pre_topc(A_6852,A_6853,g1_pre_topc(u1_struct_0(B_6854),u1_pre_topc(B_6854)))
      | ~ v5_pre_topc(A_6852,A_6853,B_6854)
      | ~ v1_funct_2(A_6852,u1_struct_0(A_6853),u1_struct_0(g1_pre_topc(u1_struct_0(B_6854),u1_pre_topc(B_6854))))
      | ~ m1_subset_1(A_6852,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6853),u1_struct_0(B_6854))))
      | ~ v1_funct_2(A_6852,u1_struct_0(A_6853),u1_struct_0(B_6854))
      | ~ v1_funct_1(A_6852)
      | ~ l1_pre_topc(B_6854)
      | ~ v2_pre_topc(B_6854)
      | ~ l1_pre_topc(A_6853)
      | ~ v2_pre_topc(A_6853)
      | ~ r1_tarski(A_6852,k2_zfmisc_1(u1_struct_0(A_6853),u1_struct_0(g1_pre_topc(u1_struct_0(B_6854),u1_pre_topc(B_6854))))) ) ),
    inference(resolution,[status(thm)],[c_24,c_160958])).

tff(c_162911,plain,(
    ! [A_6852,A_6853] :
      ( v5_pre_topc(A_6852,A_6853,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc(A_6852,A_6853,'#skF_5')
      | ~ v1_funct_2(A_6852,u1_struct_0(A_6853),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5'))))
      | ~ m1_subset_1(A_6852,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6853),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2(A_6852,u1_struct_0(A_6853),u1_struct_0('#skF_5'))
      | ~ v1_funct_1(A_6852)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_6853)
      | ~ v2_pre_topc(A_6853)
      | ~ r1_tarski(A_6852,k2_zfmisc_1(u1_struct_0(A_6853),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5'))))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142455,c_162883])).

tff(c_164133,plain,(
    ! [A_6899,A_6900] :
      ( v5_pre_topc(A_6899,A_6900,g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc(A_6899,A_6900,'#skF_5')
      | ~ m1_subset_1(A_6899,k1_zfmisc_1('#skF_6'))
      | ~ v1_funct_2(A_6899,u1_struct_0(A_6900),'#skF_6')
      | ~ v1_funct_1(A_6899)
      | ~ l1_pre_topc(A_6900)
      | ~ v2_pre_topc(A_6900)
      | ~ r1_tarski(A_6899,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142321,c_160955,c_98,c_96,c_142455,c_142321,c_142455,c_160955,c_142455,c_142455,c_162911])).

tff(c_164140,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6'))
    | ~ v1_funct_2('#skF_6',u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))),'#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_164133,c_142606])).

tff(c_164146,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_94,c_142704,c_142470,c_164140])).

tff(c_164476,plain,(
    ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_164146])).

tff(c_164479,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_164476])).

tff(c_164483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_164479])).

tff(c_164485,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_164146])).

tff(c_160968,plain,(
    ! [A_6703,B_6704] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_6703),u1_struct_0(g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704)))),A_6703,g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_6703),u1_struct_0(g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704)))),A_6703,B_6704)
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_6703),u1_struct_0(g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704)))),u1_struct_0(A_6703),u1_struct_0(g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704))))
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_6703),u1_struct_0(g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6703),u1_struct_0(B_6704))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_6703),u1_struct_0(g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704)))),u1_struct_0(A_6703),u1_struct_0(B_6704))
      | ~ v1_funct_1('#skF_3'(u1_struct_0(A_6703),u1_struct_0(g1_pre_topc(u1_struct_0(B_6704),u1_pre_topc(B_6704)))))
      | ~ l1_pre_topc(B_6704)
      | ~ v2_pre_topc(B_6704)
      | ~ l1_pre_topc(A_6703)
      | ~ v2_pre_topc(A_6703) ) ),
    inference(resolution,[status(thm)],[c_62,c_160958])).

tff(c_165271,plain,(
    ! [A_6974,B_6975] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_6974),u1_struct_0(g1_pre_topc(u1_struct_0(B_6975),u1_pre_topc(B_6975)))),A_6974,g1_pre_topc(u1_struct_0(B_6975),u1_pre_topc(B_6975)))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_6974),u1_struct_0(g1_pre_topc(u1_struct_0(B_6975),u1_pre_topc(B_6975)))),A_6974,B_6975)
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_6974),u1_struct_0(g1_pre_topc(u1_struct_0(B_6975),u1_pre_topc(B_6975)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6974),u1_struct_0(B_6975))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_6974),u1_struct_0(g1_pre_topc(u1_struct_0(B_6975),u1_pre_topc(B_6975)))),u1_struct_0(A_6974),u1_struct_0(B_6975))
      | ~ l1_pre_topc(B_6975)
      | ~ v2_pre_topc(B_6975)
      | ~ l1_pre_topc(A_6974)
      | ~ v2_pre_topc(A_6974) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_160968])).

tff(c_165283,plain,(
    ! [A_6974] :
      ( v5_pre_topc('#skF_3'(u1_struct_0(A_6974),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),A_6974,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_3'(u1_struct_0(A_6974),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),A_6974,'#skF_5')
      | ~ m1_subset_1('#skF_3'(u1_struct_0(A_6974),u1_struct_0(g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6974),u1_struct_0('#skF_5'))))
      | ~ v1_funct_2('#skF_3'(u1_struct_0(A_6974),u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))),u1_struct_0(A_6974),u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_6974)
      | ~ v2_pre_topc(A_6974) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142455,c_165271])).

tff(c_165526,plain,(
    ! [A_6984] :
      ( v5_pre_topc('#skF_6',A_6984,g1_pre_topc('#skF_6',u1_pre_topc('#skF_5')))
      | ~ v5_pre_topc('#skF_6',A_6984,'#skF_5')
      | ~ l1_pre_topc(A_6984)
      | ~ v2_pre_topc(A_6984) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_142704,c_142455,c_142649,c_160955,c_142455,c_142470,c_142321,c_142455,c_142649,c_160955,c_142649,c_160955,c_142455,c_142455,c_142649,c_160955,c_142455,c_165283])).

tff(c_165536,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_165526,c_142606])).

tff(c_165543,plain,
    ( ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164485,c_165536])).

tff(c_166631,plain,(
    ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_165543])).

tff(c_166634,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_330,c_166631])).

tff(c_166641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_166634])).

tff(c_166642,plain,(
    ~ v5_pre_topc('#skF_6',g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_165543])).

tff(c_173145,plain,
    ( ~ v5_pre_topc('#skF_6','#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_173142,c_166642])).

tff(c_173155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_79529,c_173145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:45:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.46/21.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.73/21.40  
% 32.73/21.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 32.73/21.40  %$ v5_pre_topc > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_pre_topc > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 32.73/21.40  
% 32.73/21.40  %Foreground sorts:
% 32.73/21.40  
% 32.73/21.40  
% 32.73/21.40  %Background operators:
% 32.73/21.40  
% 32.73/21.40  
% 32.73/21.40  %Foreground operators:
% 32.73/21.40  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 32.73/21.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 32.73/21.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.73/21.40  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 32.73/21.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 32.73/21.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 32.73/21.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 32.73/21.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 32.73/21.40  tff('#skF_7', type, '#skF_7': $i).
% 32.73/21.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 32.73/21.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.73/21.40  tff('#skF_5', type, '#skF_5': $i).
% 32.73/21.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 32.73/21.40  tff('#skF_6', type, '#skF_6': $i).
% 32.73/21.40  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 32.73/21.40  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 32.73/21.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 32.73/21.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 32.73/21.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.73/21.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 32.73/21.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 32.73/21.40  tff('#skF_4', type, '#skF_4': $i).
% 32.73/21.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.73/21.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 32.73/21.40  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 32.73/21.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 32.73/21.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 32.73/21.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 32.73/21.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 32.73/21.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 32.73/21.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 32.73/21.40  
% 32.95/21.46  tff(f_240, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 32.95/21.46  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 32.95/21.46  tff(f_152, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 32.95/21.46  tff(f_144, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 32.95/21.46  tff(f_140, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 32.95/21.46  tff(f_79, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 32.95/21.46  tff(f_62, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 32.95/21.46  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 32.95/21.46  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 32.95/21.46  tff(f_121, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 32.95/21.46  tff(f_93, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 32.95/21.46  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 32.95/21.46  tff(f_210, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 32.95/21.46  tff(f_181, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))), u1_struct_0(B))))) => ((C = D) => (v5_pre_topc(C, A, B) <=> v5_pre_topc(D, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)), B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 32.95/21.46  tff(f_43, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 32.95/21.46  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 32.95/21.46  tff(f_134, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 32.95/21.46  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 32.95/21.46  tff(f_113, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => ((v1_funct_1(C) & ~v1_xboole_0(C)) & v1_funct_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc6_funct_2)).
% 32.95/21.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 32.95/21.46  tff(c_102, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_100, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_82, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_104, plain, (~v5_pre_topc('#skF_7', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_112, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_104])).
% 32.95/21.46  tff(c_421, plain, (~v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_112])).
% 32.95/21.46  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 32.95/21.46  tff(c_303, plain, (![A_128, B_129]: (~r2_hidden('#skF_2'(A_128, B_129), B_129) | r1_tarski(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_38])).
% 32.95/21.46  tff(c_308, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_10, c_303])).
% 32.95/21.46  tff(c_94, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_98, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_96, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_70, plain, (![A_44]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_44), u1_pre_topc(A_44))) | ~l1_pre_topc(A_44) | ~v2_pre_topc(A_44))), inference(cnfTransformation, [status(thm)], [f_152])).
% 32.95/21.46  tff(c_320, plain, (![A_133]: (m1_subset_1(u1_pre_topc(A_133), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_133)))) | ~l1_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_144])).
% 32.95/21.46  tff(c_64, plain, (![A_41, B_42]: (l1_pre_topc(g1_pre_topc(A_41, B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 32.95/21.46  tff(c_330, plain, (![A_133]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_133), u1_pre_topc(A_133))) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_320, c_64])).
% 32.95/21.46  tff(c_90, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_554, plain, (![C_188, B_189, A_190]: (v1_xboole_0(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(B_189, A_190))) | ~v1_xboole_0(A_190))), inference(cnfTransformation, [status(thm)], [f_79])).
% 32.95/21.46  tff(c_577, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_90, c_554])).
% 32.95/21.46  tff(c_580, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_577])).
% 32.95/21.46  tff(c_28, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 32.95/21.46  tff(c_219, plain, (![B_121, A_122]: (v1_relat_1(B_121) | ~m1_subset_1(B_121, k1_zfmisc_1(A_122)) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_60])).
% 32.95/21.46  tff(c_234, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_90, c_219])).
% 32.95/21.46  tff(c_247, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_234])).
% 32.95/21.46  tff(c_363, plain, (![C_144, A_145, B_146]: (v4_relat_1(C_144, A_145) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.95/21.46  tff(c_383, plain, (v4_relat_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_90, c_363])).
% 32.95/21.46  tff(c_856, plain, (![B_210, A_211]: (k1_relat_1(B_210)=A_211 | ~v1_partfun1(B_210, A_211) | ~v4_relat_1(B_210, A_211) | ~v1_relat_1(B_210))), inference(cnfTransformation, [status(thm)], [f_121])).
% 32.95/21.46  tff(c_874, plain, (u1_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_383, c_856])).
% 32.95/21.46  tff(c_891, plain, (u1_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_874])).
% 32.95/21.46  tff(c_927, plain, (~v1_partfun1('#skF_6', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_891])).
% 32.95/21.46  tff(c_92, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_937, plain, (![C_218, A_219, B_220]: (v1_partfun1(C_218, A_219) | ~v1_funct_2(C_218, A_219, B_220) | ~v1_funct_1(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | v1_xboole_0(B_220))), inference(cnfTransformation, [status(thm)], [f_93])).
% 32.95/21.46  tff(c_950, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_90, c_937])).
% 32.95/21.46  tff(c_967, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_950])).
% 32.95/21.46  tff(c_969, plain, $false, inference(negUnitSimplification, [status(thm)], [c_580, c_927, c_967])).
% 32.95/21.46  tff(c_970, plain, (u1_struct_0('#skF_4')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_891])).
% 32.95/21.46  tff(c_171, plain, (![A_105, B_106]: (r1_tarski(A_105, B_106) | ~m1_subset_1(A_105, k1_zfmisc_1(B_106)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.95/21.46  tff(c_175, plain, (r1_tarski('#skF_6', k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_90, c_171])).
% 32.95/21.46  tff(c_978, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_970, c_175])).
% 32.95/21.46  tff(c_980, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_970, c_92])).
% 32.95/21.46  tff(c_84, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_115, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_84])).
% 32.95/21.46  tff(c_574, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(resolution, [status(thm)], [c_115, c_554])).
% 32.95/21.46  tff(c_807, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(splitLeft, [status(thm)], [c_574])).
% 32.95/21.46  tff(c_86, plain, (v1_funct_2('#skF_7', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_114, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_86])).
% 32.95/21.46  tff(c_977, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_970, c_114])).
% 32.95/21.46  tff(c_974, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(demodulation, [status(thm), theory('equality')], [c_970, c_115])).
% 32.95/21.46  tff(c_38, plain, (![C_31, A_28, B_29]: (v1_partfun1(C_31, A_28) | ~v1_funct_2(C_31, A_28, B_29) | ~v1_funct_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | v1_xboole_0(B_29))), inference(cnfTransformation, [status(thm)], [f_93])).
% 32.95/21.46  tff(c_1386, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(resolution, [status(thm)], [c_974, c_38])).
% 32.95/21.46  tff(c_1411, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_977, c_1386])).
% 32.95/21.46  tff(c_1412, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_807, c_1411])).
% 32.95/21.46  tff(c_34, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 32.95/21.46  tff(c_512, plain, (v4_relat_1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_115, c_34])).
% 32.95/21.46  tff(c_859, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_512, c_856])).
% 32.95/21.46  tff(c_880, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_859])).
% 32.95/21.46  tff(c_2575, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_970, c_970, c_880])).
% 32.95/21.46  tff(c_979, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_970, c_90])).
% 32.95/21.46  tff(c_987, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_970, c_70])).
% 32.95/21.46  tff(c_1002, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_987])).
% 32.95/21.46  tff(c_993, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_970, c_330])).
% 32.95/21.46  tff(c_1006, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_993])).
% 32.95/21.46  tff(c_110, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | v5_pre_topc('#skF_7', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_240])).
% 32.95/21.46  tff(c_111, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_110])).
% 32.95/21.46  tff(c_464, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_421, c_111])).
% 32.95/21.46  tff(c_975, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_970, c_464])).
% 32.95/21.46  tff(c_2084, plain, (![D_290, A_291, B_292]: (v5_pre_topc(D_290, A_291, B_292) | ~v5_pre_topc(D_290, A_291, g1_pre_topc(u1_struct_0(B_292), u1_pre_topc(B_292))) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291), u1_struct_0(g1_pre_topc(u1_struct_0(B_292), u1_pre_topc(B_292)))))) | ~v1_funct_2(D_290, u1_struct_0(A_291), u1_struct_0(g1_pre_topc(u1_struct_0(B_292), u1_pre_topc(B_292)))) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_291), u1_struct_0(B_292)))) | ~v1_funct_2(D_290, u1_struct_0(A_291), u1_struct_0(B_292)) | ~v1_funct_1(D_290) | ~l1_pre_topc(B_292) | ~v2_pre_topc(B_292) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_210])).
% 32.95/21.46  tff(c_2087, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), '#skF_5') | ~v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_974, c_2084])).
% 32.95/21.46  tff(c_2104, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1002, c_1006, c_98, c_96, c_94, c_977, c_975, c_2087])).
% 32.95/21.46  tff(c_5336, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_980, c_2575, c_979, c_2575, c_2104])).
% 32.95/21.46  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.95/21.46  tff(c_1604, plain, (![D_257, A_258, B_259]: (v5_pre_topc(D_257, A_258, B_259) | ~v5_pre_topc(D_257, g1_pre_topc(u1_struct_0(A_258), u1_pre_topc(A_258)), B_259) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_258), u1_pre_topc(A_258))), u1_struct_0(B_259)))) | ~v1_funct_2(D_257, u1_struct_0(g1_pre_topc(u1_struct_0(A_258), u1_pre_topc(A_258))), u1_struct_0(B_259)) | ~m1_subset_1(D_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_258), u1_struct_0(B_259)))) | ~v1_funct_2(D_257, u1_struct_0(A_258), u1_struct_0(B_259)) | ~v1_funct_1(D_257) | ~l1_pre_topc(B_259) | ~v2_pre_topc(B_259) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_181])).
% 32.95/21.46  tff(c_4966, plain, (![A_447, A_448, B_449]: (v5_pre_topc(A_447, A_448, B_449) | ~v5_pre_topc(A_447, g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(A_448)), B_449) | ~v1_funct_2(A_447, u1_struct_0(g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(A_448))), u1_struct_0(B_449)) | ~m1_subset_1(A_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_448), u1_struct_0(B_449)))) | ~v1_funct_2(A_447, u1_struct_0(A_448), u1_struct_0(B_449)) | ~v1_funct_1(A_447) | ~l1_pre_topc(B_449) | ~v2_pre_topc(B_449) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448) | ~r1_tarski(A_447, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_448), u1_pre_topc(A_448))), u1_struct_0(B_449))))), inference(resolution, [status(thm)], [c_24, c_1604])).
% 32.95/21.46  tff(c_4991, plain, (![A_447, B_449]: (v5_pre_topc(A_447, '#skF_4', B_449) | ~v5_pre_topc(A_447, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), B_449) | ~v1_funct_2(A_447, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(B_449)) | ~m1_subset_1(A_447, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_449)))) | ~v1_funct_2(A_447, u1_struct_0('#skF_4'), u1_struct_0(B_449)) | ~v1_funct_1(A_447) | ~l1_pre_topc(B_449) | ~v2_pre_topc(B_449) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~r1_tarski(A_447, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(B_449))))), inference(superposition, [status(thm), theory('equality')], [c_970, c_4966])).
% 32.95/21.46  tff(c_35338, plain, (![A_1499, B_1500]: (v5_pre_topc(A_1499, '#skF_4', B_1500) | ~v5_pre_topc(A_1499, g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), B_1500) | ~m1_subset_1(A_1499, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(B_1500)))) | ~v1_funct_2(A_1499, k1_relat_1('#skF_6'), u1_struct_0(B_1500)) | ~v1_funct_1(A_1499) | ~l1_pre_topc(B_1500) | ~v2_pre_topc(B_1500) | ~r1_tarski(A_1499, k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(B_1500))))), inference(demodulation, [status(thm), theory('equality')], [c_2575, c_102, c_100, c_970, c_970, c_2575, c_970, c_970, c_4991])).
% 32.95/21.46  tff(c_35347, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), '#skF_5') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_979, c_35338])).
% 32.95/21.46  tff(c_35366, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_978, c_98, c_96, c_94, c_980, c_5336, c_35347])).
% 32.95/21.46  tff(c_35368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_421, c_35366])).
% 32.95/21.46  tff(c_35370, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(splitRight, [status(thm)], [c_574])).
% 32.95/21.46  tff(c_35369, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_574])).
% 32.95/21.46  tff(c_14, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.95/21.46  tff(c_35382, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_35369, c_14])).
% 32.95/21.46  tff(c_35400, plain, (![A_10]: (A_10='#skF_6' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_35382, c_14])).
% 32.95/21.46  tff(c_35644, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))='#skF_6'), inference(resolution, [status(thm)], [c_35370, c_35400])).
% 32.95/21.46  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 32.95/21.46  tff(c_332, plain, (![A_133]: (r1_tarski(u1_pre_topc(A_133), k1_zfmisc_1(u1_struct_0(A_133))) | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_320, c_22])).
% 32.95/21.46  tff(c_36089, plain, (r1_tarski(u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))), k1_zfmisc_1('#skF_6')) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_35644, c_332])).
% 32.95/21.46  tff(c_36822, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_36089])).
% 32.95/21.46  tff(c_36825, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_330, c_36822])).
% 32.95/21.46  tff(c_36832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_36825])).
% 32.95/21.46  tff(c_36834, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_36089])).
% 32.95/21.46  tff(c_36086, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_35644, c_70])).
% 32.95/21.46  tff(c_38397, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_36834, c_36086])).
% 32.95/21.46  tff(c_38398, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_38397])).
% 32.95/21.46  tff(c_38401, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_38398])).
% 32.95/21.46  tff(c_38405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_38401])).
% 32.95/21.46  tff(c_38407, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_38397])).
% 32.95/21.46  tff(c_20, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 32.95/21.46  tff(c_181, plain, (![A_109, B_110]: (m1_subset_1('#skF_3'(A_109, B_110), k1_zfmisc_1(k2_zfmisc_1(A_109, B_110))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 32.95/21.46  tff(c_190, plain, (![B_12]: (m1_subset_1('#skF_3'(k1_xboole_0, B_12), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_181])).
% 32.95/21.46  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 32.95/21.46  tff(c_18, plain, (![A_11]: (k2_zfmisc_1(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 32.95/21.46  tff(c_570, plain, (![C_188]: (v1_xboole_0(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_554])).
% 32.95/21.46  tff(c_596, plain, (![C_193]: (v1_xboole_0(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_570])).
% 32.95/21.46  tff(c_610, plain, (![B_194]: (v1_xboole_0('#skF_3'(k1_xboole_0, B_194)))), inference(resolution, [status(thm)], [c_190, c_596])).
% 32.95/21.46  tff(c_622, plain, (![B_194]: ('#skF_3'(k1_xboole_0, B_194)=k1_xboole_0)), inference(resolution, [status(thm)], [c_610, c_14])).
% 32.95/21.46  tff(c_35520, plain, (![B_1506]: ('#skF_3'('#skF_6', B_1506)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35382, c_35382, c_622])).
% 32.95/21.46  tff(c_52, plain, (![A_38, B_39]: (v1_funct_2('#skF_3'(A_38, B_39), A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_134])).
% 32.95/21.46  tff(c_35534, plain, (![B_1506]: (v1_funct_2('#skF_6', '#skF_6', B_1506))), inference(superposition, [status(thm), theory('equality')], [c_35520, c_52])).
% 32.95/21.46  tff(c_35391, plain, (![B_194]: ('#skF_3'('#skF_6', B_194)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35382, c_35382, c_622])).
% 32.95/21.46  tff(c_35723, plain, (![C_1522, A_1523, B_1524]: (~v1_xboole_0(C_1522) | ~v1_funct_2(C_1522, A_1523, B_1524) | ~v1_funct_1(C_1522) | ~m1_subset_1(C_1522, k1_zfmisc_1(k2_zfmisc_1(A_1523, B_1524))) | v1_xboole_0(B_1524) | v1_xboole_0(A_1523))), inference(cnfTransformation, [status(thm)], [f_113])).
% 32.95/21.46  tff(c_35742, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_90, c_35723])).
% 32.95/21.46  tff(c_35754, plain, (v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_35369, c_35742])).
% 32.95/21.46  tff(c_35755, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_580, c_35754])).
% 32.95/21.46  tff(c_35768, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_35755, c_35400])).
% 32.95/21.46  tff(c_644, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_622, c_190])).
% 32.95/21.46  tff(c_35388, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_35382, c_35382, c_644])).
% 32.95/21.46  tff(c_35402, plain, (![B_12]: (k2_zfmisc_1('#skF_6', B_12)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35382, c_35382, c_20])).
% 32.95/21.46  tff(c_54, plain, (![A_38, B_39]: (v1_funct_1('#skF_3'(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_134])).
% 32.95/21.46  tff(c_62, plain, (![A_38, B_39]: (m1_subset_1('#skF_3'(A_38, B_39), k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 33.15/21.46  tff(c_35904, plain, (![D_1529, A_1530, B_1531]: (v5_pre_topc(D_1529, A_1530, g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531))) | ~v5_pre_topc(D_1529, A_1530, B_1531) | ~m1_subset_1(D_1529, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1530), u1_struct_0(g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531)))))) | ~v1_funct_2(D_1529, u1_struct_0(A_1530), u1_struct_0(g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531)))) | ~m1_subset_1(D_1529, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1530), u1_struct_0(B_1531)))) | ~v1_funct_2(D_1529, u1_struct_0(A_1530), u1_struct_0(B_1531)) | ~v1_funct_1(D_1529) | ~l1_pre_topc(B_1531) | ~v2_pre_topc(B_1531) | ~l1_pre_topc(A_1530) | ~v2_pre_topc(A_1530))), inference(cnfTransformation, [status(thm)], [f_210])).
% 33.15/21.46  tff(c_35917, plain, (![A_1530, B_1531]: (v5_pre_topc('#skF_3'(u1_struct_0(A_1530), u1_struct_0(g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531)))), A_1530, g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_1530), u1_struct_0(g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531)))), A_1530, B_1531) | ~v1_funct_2('#skF_3'(u1_struct_0(A_1530), u1_struct_0(g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531)))), u1_struct_0(A_1530), u1_struct_0(g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531)))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_1530), u1_struct_0(g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1530), u1_struct_0(B_1531)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_1530), u1_struct_0(g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531)))), u1_struct_0(A_1530), u1_struct_0(B_1531)) | ~v1_funct_1('#skF_3'(u1_struct_0(A_1530), u1_struct_0(g1_pre_topc(u1_struct_0(B_1531), u1_pre_topc(B_1531))))) | ~l1_pre_topc(B_1531) | ~v2_pre_topc(B_1531) | ~l1_pre_topc(A_1530) | ~v2_pre_topc(A_1530))), inference(resolution, [status(thm)], [c_62, c_35904])).
% 33.15/21.46  tff(c_41956, plain, (![A_1856, B_1857]: (v5_pre_topc('#skF_3'(u1_struct_0(A_1856), u1_struct_0(g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857)))), A_1856, g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_1856), u1_struct_0(g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857)))), A_1856, B_1857) | ~m1_subset_1('#skF_3'(u1_struct_0(A_1856), u1_struct_0(g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1856), u1_struct_0(B_1857)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_1856), u1_struct_0(g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857)))), u1_struct_0(A_1856), u1_struct_0(B_1857)) | ~l1_pre_topc(B_1857) | ~v2_pre_topc(B_1857) | ~l1_pre_topc(A_1856) | ~v2_pre_topc(A_1856))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_35917])).
% 33.15/21.46  tff(c_41972, plain, (![B_1857]: (v5_pre_topc('#skF_3'(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857)))), '#skF_4', g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857))) | ~v5_pre_topc('#skF_3'(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857)))), '#skF_4', B_1857) | ~m1_subset_1('#skF_3'(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857)))), k1_zfmisc_1(k2_zfmisc_1('#skF_6', u1_struct_0(B_1857)))) | ~v1_funct_2('#skF_3'(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1857), u1_pre_topc(B_1857)))), u1_struct_0('#skF_4'), u1_struct_0(B_1857)) | ~l1_pre_topc(B_1857) | ~v2_pre_topc(B_1857) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_35768, c_41956])).
% 33.15/21.46  tff(c_43137, plain, (![B_1909]: (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0(B_1909), u1_pre_topc(B_1909))) | ~v5_pre_topc('#skF_6', '#skF_4', B_1909) | ~l1_pre_topc(B_1909) | ~v2_pre_topc(B_1909))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_35534, c_35391, c_35768, c_35768, c_35388, c_35402, c_35391, c_35768, c_35391, c_35768, c_35391, c_35768, c_41972])).
% 33.15/21.46  tff(c_43143, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_35644, c_43137])).
% 33.15/21.46  tff(c_43149, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_38407, c_36834, c_43143])).
% 33.15/21.46  tff(c_45520, plain, (~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_43149])).
% 33.15/21.46  tff(c_35776, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_35768, c_464])).
% 33.15/21.46  tff(c_187, plain, (![A_11]: (m1_subset_1('#skF_3'(A_11, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_181])).
% 33.15/21.46  tff(c_625, plain, (![A_195]: (v1_xboole_0('#skF_3'(A_195, k1_xboole_0)))), inference(resolution, [status(thm)], [c_187, c_596])).
% 33.15/21.46  tff(c_637, plain, (![A_195]: ('#skF_3'(A_195, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_625, c_14])).
% 33.15/21.46  tff(c_35590, plain, (![A_1509]: ('#skF_3'(A_1509, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35382, c_35382, c_637])).
% 33.15/21.46  tff(c_35607, plain, (![A_1509]: (v1_funct_2('#skF_6', A_1509, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_35590, c_52])).
% 33.15/21.46  tff(c_35389, plain, (![A_195]: ('#skF_3'(A_195, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35382, c_35382, c_637])).
% 33.15/21.46  tff(c_35399, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_35382, c_35382, c_18])).
% 33.15/21.46  tff(c_35982, plain, (![D_1534, A_1535, B_1536]: (v5_pre_topc(D_1534, A_1535, B_1536) | ~v5_pre_topc(D_1534, g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535)), B_1536) | ~m1_subset_1(D_1534, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535))), u1_struct_0(B_1536)))) | ~v1_funct_2(D_1534, u1_struct_0(g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535))), u1_struct_0(B_1536)) | ~m1_subset_1(D_1534, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1535), u1_struct_0(B_1536)))) | ~v1_funct_2(D_1534, u1_struct_0(A_1535), u1_struct_0(B_1536)) | ~v1_funct_1(D_1534) | ~l1_pre_topc(B_1536) | ~v2_pre_topc(B_1536) | ~l1_pre_topc(A_1535) | ~v2_pre_topc(A_1535))), inference(cnfTransformation, [status(thm)], [f_181])).
% 33.15/21.46  tff(c_35992, plain, (![A_1535, B_1536]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535))), u1_struct_0(B_1536)), A_1535, B_1536) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535))), u1_struct_0(B_1536)), g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535)), B_1536) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535))), u1_struct_0(B_1536)), u1_struct_0(g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535))), u1_struct_0(B_1536)) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535))), u1_struct_0(B_1536)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1535), u1_struct_0(B_1536)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535))), u1_struct_0(B_1536)), u1_struct_0(A_1535), u1_struct_0(B_1536)) | ~v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1535), u1_pre_topc(A_1535))), u1_struct_0(B_1536))) | ~l1_pre_topc(B_1536) | ~v2_pre_topc(B_1536) | ~l1_pre_topc(A_1535) | ~v2_pre_topc(A_1535))), inference(resolution, [status(thm)], [c_62, c_35982])).
% 33.15/21.46  tff(c_42889, plain, (![A_1894, B_1895]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894))), u1_struct_0(B_1895)), A_1894, B_1895) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894))), u1_struct_0(B_1895)), g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894)), B_1895) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894))), u1_struct_0(B_1895)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1894), u1_struct_0(B_1895)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894))), u1_struct_0(B_1895)), u1_struct_0(A_1894), u1_struct_0(B_1895)) | ~l1_pre_topc(B_1895) | ~v2_pre_topc(B_1895) | ~l1_pre_topc(A_1894) | ~v2_pre_topc(A_1894))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_35992])).
% 33.15/21.46  tff(c_42898, plain, (![A_1894]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), A_1894, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894))), '#skF_6'), g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894)), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1894), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_1894), u1_pre_topc(A_1894))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), u1_struct_0(A_1894), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(A_1894) | ~v2_pre_topc(A_1894))), inference(superposition, [status(thm), theory('equality')], [c_35644, c_42889])).
% 33.15/21.46  tff(c_53693, plain, (![A_2301]: (v5_pre_topc('#skF_6', A_2301, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2301), u1_pre_topc(A_2301)), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(A_2301) | ~v2_pre_topc(A_2301))), inference(demodulation, [status(thm), theory('equality')], [c_38407, c_36834, c_35607, c_35389, c_35644, c_35644, c_35388, c_35399, c_35389, c_35644, c_35644, c_35389, c_35389, c_35644, c_42898])).
% 33.15/21.46  tff(c_53713, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_35768, c_53693])).
% 33.15/21.46  tff(c_53725, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_35776, c_53713])).
% 33.15/21.46  tff(c_53727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45520, c_53725])).
% 33.15/21.46  tff(c_53729, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_43149])).
% 33.15/21.46  tff(c_36112, plain, (![D_1543, A_1544, B_1545]: (v5_pre_topc(D_1543, A_1544, B_1545) | ~v5_pre_topc(D_1543, A_1544, g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545))) | ~m1_subset_1(D_1543, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1544), u1_struct_0(g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545)))))) | ~v1_funct_2(D_1543, u1_struct_0(A_1544), u1_struct_0(g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545)))) | ~m1_subset_1(D_1543, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1544), u1_struct_0(B_1545)))) | ~v1_funct_2(D_1543, u1_struct_0(A_1544), u1_struct_0(B_1545)) | ~v1_funct_1(D_1543) | ~l1_pre_topc(B_1545) | ~v2_pre_topc(B_1545) | ~l1_pre_topc(A_1544) | ~v2_pre_topc(A_1544))), inference(cnfTransformation, [status(thm)], [f_210])).
% 33.15/21.46  tff(c_36131, plain, (![A_1544, B_1545]: (v5_pre_topc('#skF_3'(u1_struct_0(A_1544), u1_struct_0(g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545)))), A_1544, B_1545) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_1544), u1_struct_0(g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545)))), A_1544, g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_1544), u1_struct_0(g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545)))), u1_struct_0(A_1544), u1_struct_0(g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545)))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_1544), u1_struct_0(g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1544), u1_struct_0(B_1545)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_1544), u1_struct_0(g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545)))), u1_struct_0(A_1544), u1_struct_0(B_1545)) | ~v1_funct_1('#skF_3'(u1_struct_0(A_1544), u1_struct_0(g1_pre_topc(u1_struct_0(B_1545), u1_pre_topc(B_1545))))) | ~l1_pre_topc(B_1545) | ~v2_pre_topc(B_1545) | ~l1_pre_topc(A_1544) | ~v2_pre_topc(A_1544))), inference(resolution, [status(thm)], [c_62, c_36112])).
% 33.15/21.46  tff(c_40694, plain, (![A_1820, B_1821]: (v5_pre_topc('#skF_3'(u1_struct_0(A_1820), u1_struct_0(g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821)))), A_1820, B_1821) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_1820), u1_struct_0(g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821)))), A_1820, g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_1820), u1_struct_0(g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_1820), u1_struct_0(B_1821)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_1820), u1_struct_0(g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821)))), u1_struct_0(A_1820), u1_struct_0(B_1821)) | ~l1_pre_topc(B_1821) | ~v2_pre_topc(B_1821) | ~l1_pre_topc(A_1820) | ~v2_pre_topc(A_1820))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_36131])).
% 33.15/21.46  tff(c_40704, plain, (![B_1821]: (v5_pre_topc('#skF_3'(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821)))), '#skF_4', B_1821) | ~v5_pre_topc('#skF_3'('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821)))), '#skF_4', g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821))) | ~m1_subset_1('#skF_3'(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_1821)))) | ~v1_funct_2('#skF_3'(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821)))), u1_struct_0('#skF_4'), u1_struct_0(B_1821)) | ~l1_pre_topc(B_1821) | ~v2_pre_topc(B_1821) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_35768, c_40694])).
% 33.15/21.46  tff(c_40718, plain, (![B_1821]: (v5_pre_topc('#skF_6', '#skF_4', B_1821) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0(B_1821), u1_pre_topc(B_1821))) | ~l1_pre_topc(B_1821) | ~v2_pre_topc(B_1821))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_35534, c_35391, c_35768, c_35768, c_35388, c_35402, c_35391, c_35768, c_35768, c_35391, c_35391, c_35768, c_40704])).
% 33.15/21.46  tff(c_53732, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_53729, c_40718])).
% 33.15/21.46  tff(c_53735, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_53732])).
% 33.15/21.46  tff(c_53737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_421, c_53735])).
% 33.15/21.46  tff(c_53738, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_577])).
% 33.15/21.46  tff(c_53751, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_53738, c_14])).
% 33.15/21.46  tff(c_192, plain, (![A_111]: (m1_subset_1('#skF_3'(A_111, k1_xboole_0), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_181])).
% 33.15/21.46  tff(c_196, plain, (![A_111]: (r1_tarski('#skF_3'(A_111, k1_xboole_0), k1_xboole_0))), inference(resolution, [status(thm)], [c_192, c_22])).
% 33.15/21.46  tff(c_53766, plain, (![A_111]: (r1_tarski('#skF_3'(A_111, '#skF_6'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_53751, c_53751, c_196])).
% 33.15/21.46  tff(c_579, plain, (![C_188]: (v1_xboole_0(C_188) | ~m1_subset_1(C_188, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_570])).
% 33.15/21.46  tff(c_54030, plain, (![C_2320]: (v1_xboole_0(C_2320) | ~m1_subset_1(C_2320, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_53751, c_579])).
% 33.15/21.46  tff(c_54041, plain, (![A_2321]: (v1_xboole_0(A_2321) | ~r1_tarski(A_2321, '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_54030])).
% 33.15/21.46  tff(c_54061, plain, (![A_2322]: (v1_xboole_0('#skF_3'(A_2322, '#skF_6')))), inference(resolution, [status(thm)], [c_53766, c_54041])).
% 33.15/21.46  tff(c_53769, plain, (![A_10]: (A_10='#skF_6' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_53751, c_14])).
% 33.15/21.46  tff(c_54117, plain, (![A_2327]: ('#skF_3'(A_2327, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_54061, c_53769])).
% 33.15/21.46  tff(c_54140, plain, (![A_2327]: (v1_funct_2('#skF_6', A_2327, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_54117, c_52])).
% 33.15/21.46  tff(c_53768, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_53751, c_53751, c_18])).
% 33.15/21.46  tff(c_53739, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_577])).
% 33.15/21.46  tff(c_53879, plain, (![A_2306]: (A_2306='#skF_6' | ~v1_xboole_0(A_2306))), inference(demodulation, [status(thm), theory('equality')], [c_53751, c_14])).
% 33.15/21.46  tff(c_53886, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_53739, c_53879])).
% 33.15/21.46  tff(c_53897, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_53886, c_90])).
% 33.15/21.46  tff(c_53903, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_53768, c_53897])).
% 33.15/21.46  tff(c_53895, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_53886, c_114])).
% 33.15/21.46  tff(c_53892, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))))))), inference(demodulation, [status(thm), theory('equality')], [c_53886, c_115])).
% 33.15/21.46  tff(c_44, plain, (![C_35, A_32, B_33]: (~v1_xboole_0(C_35) | ~v1_funct_2(C_35, A_32, B_33) | ~v1_funct_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | v1_xboole_0(B_33) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_113])).
% 33.15/21.46  tff(c_54401, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_53892, c_44])).
% 33.15/21.46  tff(c_54425, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_53895, c_53738, c_54401])).
% 33.15/21.46  tff(c_54599, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(splitLeft, [status(thm)], [c_54425])).
% 33.15/21.46  tff(c_54612, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6'), inference(resolution, [status(thm)], [c_54599, c_53769])).
% 33.15/21.46  tff(c_68, plain, (![A_43]: (m1_subset_1(u1_pre_topc(A_43), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_43)))) | ~l1_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_144])).
% 33.15/21.46  tff(c_440, plain, (![A_156, B_157]: (v1_pre_topc(g1_pre_topc(A_156, B_157)) | ~m1_subset_1(B_157, k1_zfmisc_1(k1_zfmisc_1(A_156))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 33.15/21.46  tff(c_448, plain, (![A_43]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_43), u1_pre_topc(A_43))) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_68, c_440])).
% 33.15/21.46  tff(c_54639, plain, (v1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_54612, c_448])).
% 33.15/21.46  tff(c_69816, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_54639])).
% 33.15/21.46  tff(c_69907, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_330, c_69816])).
% 33.15/21.46  tff(c_69914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_69907])).
% 33.15/21.46  tff(c_69916, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_54639])).
% 33.15/21.46  tff(c_198, plain, (![B_113]: (m1_subset_1('#skF_3'(k1_xboole_0, B_113), k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_181])).
% 33.15/21.46  tff(c_202, plain, (![B_113]: (r1_tarski('#skF_3'(k1_xboole_0, B_113), k1_xboole_0))), inference(resolution, [status(thm)], [c_198, c_22])).
% 33.15/21.46  tff(c_53764, plain, (![B_113]: (r1_tarski('#skF_3'('#skF_6', B_113), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_53751, c_53751, c_202])).
% 33.15/21.46  tff(c_54095, plain, (![B_2326]: (v1_xboole_0('#skF_3'('#skF_6', B_2326)))), inference(resolution, [status(thm)], [c_53764, c_54041])).
% 33.15/21.46  tff(c_54177, plain, (![B_2329]: ('#skF_3'('#skF_6', B_2329)='#skF_6')), inference(resolution, [status(thm)], [c_54095, c_53769])).
% 33.15/21.46  tff(c_54191, plain, (![B_2329]: (v1_funct_2('#skF_6', '#skF_6', B_2329))), inference(superposition, [status(thm), theory('equality')], [c_54177, c_52])).
% 33.15/21.46  tff(c_54105, plain, (![B_2326]: ('#skF_3'('#skF_6', B_2326)='#skF_6')), inference(resolution, [status(thm)], [c_54095, c_53769])).
% 33.15/21.46  tff(c_53893, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_53886, c_464])).
% 33.15/21.46  tff(c_54356, plain, (![D_2349, A_2350, B_2351]: (v5_pre_topc(D_2349, A_2350, B_2351) | ~v5_pre_topc(D_2349, A_2350, g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351))) | ~m1_subset_1(D_2349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2350), u1_struct_0(g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351)))))) | ~v1_funct_2(D_2349, u1_struct_0(A_2350), u1_struct_0(g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351)))) | ~m1_subset_1(D_2349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2350), u1_struct_0(B_2351)))) | ~v1_funct_2(D_2349, u1_struct_0(A_2350), u1_struct_0(B_2351)) | ~v1_funct_1(D_2349) | ~l1_pre_topc(B_2351) | ~v2_pre_topc(B_2351) | ~l1_pre_topc(A_2350) | ~v2_pre_topc(A_2350))), inference(cnfTransformation, [status(thm)], [f_210])).
% 33.15/21.46  tff(c_54366, plain, (![A_2350, B_2351]: (v5_pre_topc('#skF_3'(u1_struct_0(A_2350), u1_struct_0(g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351)))), A_2350, B_2351) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_2350), u1_struct_0(g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351)))), A_2350, g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_2350), u1_struct_0(g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351)))), u1_struct_0(A_2350), u1_struct_0(g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351)))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_2350), u1_struct_0(g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2350), u1_struct_0(B_2351)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_2350), u1_struct_0(g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351)))), u1_struct_0(A_2350), u1_struct_0(B_2351)) | ~v1_funct_1('#skF_3'(u1_struct_0(A_2350), u1_struct_0(g1_pre_topc(u1_struct_0(B_2351), u1_pre_topc(B_2351))))) | ~l1_pre_topc(B_2351) | ~v2_pre_topc(B_2351) | ~l1_pre_topc(A_2350) | ~v2_pre_topc(A_2350))), inference(resolution, [status(thm)], [c_62, c_54356])).
% 33.15/21.46  tff(c_61561, plain, (![A_2729, B_2730]: (v5_pre_topc('#skF_3'(u1_struct_0(A_2729), u1_struct_0(g1_pre_topc(u1_struct_0(B_2730), u1_pre_topc(B_2730)))), A_2729, B_2730) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_2729), u1_struct_0(g1_pre_topc(u1_struct_0(B_2730), u1_pre_topc(B_2730)))), A_2729, g1_pre_topc(u1_struct_0(B_2730), u1_pre_topc(B_2730))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_2729), u1_struct_0(g1_pre_topc(u1_struct_0(B_2730), u1_pre_topc(B_2730)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2729), u1_struct_0(B_2730)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_2729), u1_struct_0(g1_pre_topc(u1_struct_0(B_2730), u1_pre_topc(B_2730)))), u1_struct_0(A_2729), u1_struct_0(B_2730)) | ~l1_pre_topc(B_2730) | ~v2_pre_topc(B_2730) | ~l1_pre_topc(A_2729) | ~v2_pre_topc(A_2729))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_54366])).
% 33.15/21.46  tff(c_61575, plain, (![A_2729]: (v5_pre_topc('#skF_3'(u1_struct_0(A_2729), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), A_2729, '#skF_5') | ~v5_pre_topc('#skF_3'(u1_struct_0(A_2729), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), A_2729, g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_2729), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2729), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_2729), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), u1_struct_0(A_2729), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_2729) | ~v2_pre_topc(A_2729))), inference(superposition, [status(thm), theory('equality')], [c_53886, c_61561])).
% 33.15/21.46  tff(c_77718, plain, (![A_3339]: (v5_pre_topc('#skF_3'(u1_struct_0(A_3339), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), A_3339, '#skF_5') | ~v5_pre_topc('#skF_3'(u1_struct_0(A_3339), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), A_3339, g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_3339), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_3'(u1_struct_0(A_3339), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), u1_struct_0(A_3339), '#skF_6') | ~l1_pre_topc(A_3339) | ~v2_pre_topc(A_3339))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_53886, c_53886, c_53768, c_53886, c_53886, c_53886, c_53886, c_61575])).
% 33.15/21.46  tff(c_77732, plain, (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~v5_pre_topc('#skF_3'('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), '#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_54612, c_77718])).
% 33.15/21.46  tff(c_77744, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_69916, c_54191, c_54105, c_54612, c_54612, c_53903, c_54105, c_54612, c_53893, c_54105, c_54105, c_54612, c_77732])).
% 33.15/21.46  tff(c_77748, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_77744])).
% 33.15/21.46  tff(c_77751, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_70, c_77748])).
% 33.15/21.46  tff(c_77755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_77751])).
% 33.15/21.46  tff(c_77756, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5')), inference(splitRight, [status(thm)], [c_77744])).
% 33.15/21.46  tff(c_54071, plain, (![A_2322]: ('#skF_3'(A_2322, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_54061, c_53769])).
% 33.15/21.46  tff(c_54546, plain, (![D_2370, A_2371, B_2372]: (v5_pre_topc(D_2370, A_2371, B_2372) | ~v5_pre_topc(D_2370, g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371)), B_2372) | ~m1_subset_1(D_2370, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371))), u1_struct_0(B_2372)))) | ~v1_funct_2(D_2370, u1_struct_0(g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371))), u1_struct_0(B_2372)) | ~m1_subset_1(D_2370, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2371), u1_struct_0(B_2372)))) | ~v1_funct_2(D_2370, u1_struct_0(A_2371), u1_struct_0(B_2372)) | ~v1_funct_1(D_2370) | ~l1_pre_topc(B_2372) | ~v2_pre_topc(B_2372) | ~l1_pre_topc(A_2371) | ~v2_pre_topc(A_2371))), inference(cnfTransformation, [status(thm)], [f_181])).
% 33.15/21.46  tff(c_54559, plain, (![A_2371, B_2372]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371))), u1_struct_0(B_2372)), A_2371, B_2372) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371))), u1_struct_0(B_2372)), g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371)), B_2372) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371))), u1_struct_0(B_2372)), u1_struct_0(g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371))), u1_struct_0(B_2372)) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371))), u1_struct_0(B_2372)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2371), u1_struct_0(B_2372)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371))), u1_struct_0(B_2372)), u1_struct_0(A_2371), u1_struct_0(B_2372)) | ~v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2371), u1_pre_topc(A_2371))), u1_struct_0(B_2372))) | ~l1_pre_topc(B_2372) | ~v2_pre_topc(B_2372) | ~l1_pre_topc(A_2371) | ~v2_pre_topc(A_2371))), inference(resolution, [status(thm)], [c_62, c_54546])).
% 33.15/21.46  tff(c_58803, plain, (![A_2624, B_2625]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624))), u1_struct_0(B_2625)), A_2624, B_2625) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624))), u1_struct_0(B_2625)), g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624)), B_2625) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624))), u1_struct_0(B_2625)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2624), u1_struct_0(B_2625)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624))), u1_struct_0(B_2625)), u1_struct_0(A_2624), u1_struct_0(B_2625)) | ~l1_pre_topc(B_2625) | ~v2_pre_topc(B_2625) | ~l1_pre_topc(A_2624) | ~v2_pre_topc(A_2624))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_54559])).
% 33.15/21.46  tff(c_58815, plain, (![A_2624]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624))), u1_struct_0('#skF_5')), A_2624, '#skF_5') | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624))), '#skF_6'), g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624)), '#skF_5') | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624))), u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_2624), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624))), u1_struct_0('#skF_5')), u1_struct_0(A_2624), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_2624) | ~v2_pre_topc(A_2624))), inference(superposition, [status(thm), theory('equality')], [c_53886, c_58803])).
% 33.15/21.46  tff(c_58827, plain, (![A_2624]: (v5_pre_topc('#skF_6', A_2624, '#skF_5') | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_2624), u1_pre_topc(A_2624)), '#skF_5') | ~l1_pre_topc(A_2624) | ~v2_pre_topc(A_2624))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_54140, c_54071, c_53886, c_53886, c_53903, c_54071, c_53768, c_53886, c_53886, c_54071, c_54071, c_53886, c_58815])).
% 33.15/21.46  tff(c_77760, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_77756, c_58827])).
% 33.15/21.46  tff(c_77763, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_77760])).
% 33.15/21.46  tff(c_77765, plain, $false, inference(negUnitSimplification, [status(thm)], [c_421, c_77763])).
% 33.15/21.46  tff(c_77766, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))))), inference(splitRight, [status(thm)], [c_54425])).
% 33.15/21.46  tff(c_77780, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))='#skF_6'), inference(resolution, [status(thm)], [c_77766, c_53769])).
% 33.15/21.46  tff(c_53907, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_53886, c_70])).
% 33.15/21.46  tff(c_53920, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_53907])).
% 33.15/21.46  tff(c_53913, plain, (l1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_53886, c_330])).
% 33.15/21.46  tff(c_53924, plain, (l1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_53913])).
% 33.15/21.46  tff(c_54549, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_53892, c_54546])).
% 33.15/21.46  tff(c_54566, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_53920, c_53924, c_94, c_53895, c_53893, c_54549])).
% 33.15/21.46  tff(c_78035, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_54140, c_77780, c_53903, c_53768, c_77780, c_54566])).
% 33.15/21.46  tff(c_79385, plain, (![A_3454, A_3455, B_3456]: (v5_pre_topc(A_3454, A_3455, B_3456) | ~v5_pre_topc(A_3454, A_3455, g1_pre_topc(u1_struct_0(B_3456), u1_pre_topc(B_3456))) | ~v1_funct_2(A_3454, u1_struct_0(A_3455), u1_struct_0(g1_pre_topc(u1_struct_0(B_3456), u1_pre_topc(B_3456)))) | ~m1_subset_1(A_3454, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3455), u1_struct_0(B_3456)))) | ~v1_funct_2(A_3454, u1_struct_0(A_3455), u1_struct_0(B_3456)) | ~v1_funct_1(A_3454) | ~l1_pre_topc(B_3456) | ~v2_pre_topc(B_3456) | ~l1_pre_topc(A_3455) | ~v2_pre_topc(A_3455) | ~r1_tarski(A_3454, k2_zfmisc_1(u1_struct_0(A_3455), u1_struct_0(g1_pre_topc(u1_struct_0(B_3456), u1_pre_topc(B_3456))))))), inference(resolution, [status(thm)], [c_24, c_54356])).
% 33.15/21.46  tff(c_79413, plain, (![A_3454, A_3455]: (v5_pre_topc(A_3454, A_3455, '#skF_5') | ~v5_pre_topc(A_3454, A_3455, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v1_funct_2(A_3454, u1_struct_0(A_3455), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1(A_3454, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3455), u1_struct_0('#skF_5')))) | ~v1_funct_2(A_3454, u1_struct_0(A_3455), u1_struct_0('#skF_5')) | ~v1_funct_1(A_3454) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_3455) | ~v2_pre_topc(A_3455) | ~r1_tarski(A_3454, k2_zfmisc_1(u1_struct_0(A_3455), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))))))), inference(superposition, [status(thm), theory('equality')], [c_53886, c_79385])).
% 33.15/21.46  tff(c_79516, plain, (![A_3461, A_3462]: (v5_pre_topc(A_3461, A_3462, '#skF_5') | ~v5_pre_topc(A_3461, A_3462, g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~m1_subset_1(A_3461, k1_zfmisc_1('#skF_6')) | ~v1_funct_2(A_3461, u1_struct_0(A_3462), '#skF_6') | ~v1_funct_1(A_3461) | ~l1_pre_topc(A_3462) | ~v2_pre_topc(A_3462) | ~r1_tarski(A_3461, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_53768, c_77780, c_98, c_96, c_53886, c_53768, c_53886, c_77780, c_53886, c_53886, c_79413])).
% 33.15/21.46  tff(c_79519, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), '#skF_6') | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_78035, c_79516])).
% 33.15/21.46  tff(c_79525, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_308, c_102, c_100, c_94, c_54140, c_53903, c_79519])).
% 33.15/21.46  tff(c_79527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_421, c_79525])).
% 33.15/21.46  tff(c_79529, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_112])).
% 33.15/21.46  tff(c_356, plain, (![C_141, B_142, A_143]: (r2_hidden(C_141, B_142) | ~r2_hidden(C_141, A_143) | ~r1_tarski(A_143, B_142))), inference(cnfTransformation, [status(thm)], [f_38])).
% 33.15/21.46  tff(c_82229, plain, (![A_3661, B_3662, B_3663]: (r2_hidden('#skF_2'(A_3661, B_3662), B_3663) | ~r1_tarski(A_3661, B_3663) | r1_tarski(A_3661, B_3662))), inference(resolution, [status(thm)], [c_10, c_356])).
% 33.15/21.46  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 33.15/21.46  tff(c_89102, plain, (![A_3991, B_3992, B_3993, B_3994]: (r2_hidden('#skF_2'(A_3991, B_3992), B_3993) | ~r1_tarski(B_3994, B_3993) | ~r1_tarski(A_3991, B_3994) | r1_tarski(A_3991, B_3992))), inference(resolution, [status(thm)], [c_82229, c_6])).
% 33.15/21.46  tff(c_98779, plain, (![A_4344, B_4345, A_4346]: (r2_hidden('#skF_2'(A_4344, B_4345), k1_zfmisc_1(u1_struct_0(A_4346))) | ~r1_tarski(A_4344, u1_pre_topc(A_4346)) | r1_tarski(A_4344, B_4345) | ~l1_pre_topc(A_4346))), inference(resolution, [status(thm)], [c_332, c_89102])).
% 33.15/21.46  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 33.15/21.46  tff(c_98802, plain, (![A_4347, A_4348]: (~r1_tarski(A_4347, u1_pre_topc(A_4348)) | r1_tarski(A_4347, k1_zfmisc_1(u1_struct_0(A_4348))) | ~l1_pre_topc(A_4348))), inference(resolution, [status(thm)], [c_98779, c_8])).
% 33.15/21.46  tff(c_314, plain, (![A_131, B_132]: (l1_pre_topc(g1_pre_topc(A_131, B_132)) | ~m1_subset_1(B_132, k1_zfmisc_1(k1_zfmisc_1(A_131))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 33.15/21.46  tff(c_319, plain, (![A_131, A_13]: (l1_pre_topc(g1_pre_topc(A_131, A_13)) | ~r1_tarski(A_13, k1_zfmisc_1(A_131)))), inference(resolution, [status(thm)], [c_24, c_314])).
% 33.15/21.46  tff(c_98857, plain, (![A_4348, A_4347]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_4348), A_4347)) | ~r1_tarski(A_4347, u1_pre_topc(A_4348)) | ~l1_pre_topc(A_4348))), inference(resolution, [status(thm)], [c_98802, c_319])).
% 33.15/21.46  tff(c_79680, plain, (![C_3500, B_3501, A_3502]: (v1_xboole_0(C_3500) | ~m1_subset_1(C_3500, k1_zfmisc_1(k2_zfmisc_1(B_3501, A_3502))) | ~v1_xboole_0(A_3502))), inference(cnfTransformation, [status(thm)], [f_79])).
% 33.15/21.46  tff(c_79703, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_90, c_79680])).
% 33.15/21.46  tff(c_79708, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_79703])).
% 33.15/21.46  tff(c_79972, plain, (![B_3524, A_3525]: (k1_relat_1(B_3524)=A_3525 | ~v1_partfun1(B_3524, A_3525) | ~v4_relat_1(B_3524, A_3525) | ~v1_relat_1(B_3524))), inference(cnfTransformation, [status(thm)], [f_121])).
% 33.15/21.46  tff(c_79990, plain, (u1_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_4')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_383, c_79972])).
% 33.15/21.46  tff(c_80007, plain, (u1_struct_0('#skF_4')=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_79990])).
% 33.15/21.46  tff(c_80017, plain, (~v1_partfun1('#skF_6', u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_80007])).
% 33.15/21.46  tff(c_80458, plain, (![C_3557, A_3558, B_3559]: (v1_partfun1(C_3557, A_3558) | ~v1_funct_2(C_3557, A_3558, B_3559) | ~v1_funct_1(C_3557) | ~m1_subset_1(C_3557, k1_zfmisc_1(k2_zfmisc_1(A_3558, B_3559))) | v1_xboole_0(B_3559))), inference(cnfTransformation, [status(thm)], [f_93])).
% 33.15/21.46  tff(c_80477, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_90, c_80458])).
% 33.15/21.46  tff(c_80494, plain, (v1_partfun1('#skF_6', u1_struct_0('#skF_4')) | v1_xboole_0(u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_80477])).
% 33.15/21.46  tff(c_80496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79708, c_80017, c_80494])).
% 33.15/21.46  tff(c_80497, plain, (u1_struct_0('#skF_4')=k1_relat_1('#skF_6')), inference(splitRight, [status(thm)], [c_80007])).
% 33.15/21.46  tff(c_79528, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_112])).
% 33.15/21.46  tff(c_80579, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_80497, c_79528])).
% 33.15/21.46  tff(c_79700, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(resolution, [status(thm)], [c_115, c_79680])).
% 33.15/21.46  tff(c_80757, plain, (~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(splitLeft, [status(thm)], [c_79700])).
% 33.15/21.46  tff(c_80502, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_80497, c_114])).
% 33.15/21.46  tff(c_80500, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(demodulation, [status(thm), theory('equality')], [c_80497, c_115])).
% 33.15/21.46  tff(c_81433, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')))) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(resolution, [status(thm)], [c_80500, c_38])).
% 33.15/21.46  tff(c_81455, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_80502, c_81433])).
% 33.15/21.46  tff(c_81456, plain, (v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_80757, c_81455])).
% 33.15/21.46  tff(c_79638, plain, (v4_relat_1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_115, c_34])).
% 33.15/21.46  tff(c_79975, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_79638, c_79972])).
% 33.15/21.46  tff(c_79996, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))=k1_relat_1('#skF_6') | ~v1_partfun1('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_247, c_79975])).
% 33.15/21.46  tff(c_81725, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')))=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_81456, c_80497, c_80497, c_79996])).
% 33.15/21.46  tff(c_79642, plain, (r1_tarski('#skF_6', k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))), inference(resolution, [status(thm)], [c_115, c_22])).
% 33.15/21.46  tff(c_81241, plain, (r1_tarski('#skF_6', k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_80497, c_79642])).
% 33.15/21.46  tff(c_81728, plain, (r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))), inference(demodulation, [status(thm), theory('equality')], [c_81725, c_81241])).
% 33.15/21.46  tff(c_81729, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_81725, c_80502])).
% 33.15/21.46  tff(c_81727, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))))), inference(demodulation, [status(thm), theory('equality')], [c_81725, c_80500])).
% 33.15/21.46  tff(c_81165, plain, (![D_3596, A_3597, B_3598]: (v5_pre_topc(D_3596, g1_pre_topc(u1_struct_0(A_3597), u1_pre_topc(A_3597)), B_3598) | ~v5_pre_topc(D_3596, A_3597, B_3598) | ~m1_subset_1(D_3596, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3597), u1_pre_topc(A_3597))), u1_struct_0(B_3598)))) | ~v1_funct_2(D_3596, u1_struct_0(g1_pre_topc(u1_struct_0(A_3597), u1_pre_topc(A_3597))), u1_struct_0(B_3598)) | ~m1_subset_1(D_3596, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3597), u1_struct_0(B_3598)))) | ~v1_funct_2(D_3596, u1_struct_0(A_3597), u1_struct_0(B_3598)) | ~v1_funct_1(D_3596) | ~l1_pre_topc(B_3598) | ~v2_pre_topc(B_3598) | ~l1_pre_topc(A_3597) | ~v2_pre_topc(A_3597))), inference(cnfTransformation, [status(thm)], [f_181])).
% 33.15/21.46  tff(c_85025, plain, (![A_3821, A_3822, B_3823]: (v5_pre_topc(A_3821, g1_pre_topc(u1_struct_0(A_3822), u1_pre_topc(A_3822)), B_3823) | ~v5_pre_topc(A_3821, A_3822, B_3823) | ~v1_funct_2(A_3821, u1_struct_0(g1_pre_topc(u1_struct_0(A_3822), u1_pre_topc(A_3822))), u1_struct_0(B_3823)) | ~m1_subset_1(A_3821, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3822), u1_struct_0(B_3823)))) | ~v1_funct_2(A_3821, u1_struct_0(A_3822), u1_struct_0(B_3823)) | ~v1_funct_1(A_3821) | ~l1_pre_topc(B_3823) | ~v2_pre_topc(B_3823) | ~l1_pre_topc(A_3822) | ~v2_pre_topc(A_3822) | ~r1_tarski(A_3821, k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_3822), u1_pre_topc(A_3822))), u1_struct_0(B_3823))))), inference(resolution, [status(thm)], [c_24, c_81165])).
% 33.15/21.46  tff(c_85058, plain, (![A_3821, B_3823]: (v5_pre_topc(A_3821, g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), B_3823) | ~v5_pre_topc(A_3821, '#skF_4', B_3823) | ~v1_funct_2(A_3821, u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(B_3823)) | ~m1_subset_1(A_3821, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_3823)))) | ~v1_funct_2(A_3821, u1_struct_0('#skF_4'), u1_struct_0(B_3823)) | ~v1_funct_1(A_3821) | ~l1_pre_topc(B_3823) | ~v2_pre_topc(B_3823) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~r1_tarski(A_3821, k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4'))), u1_struct_0(B_3823))))), inference(superposition, [status(thm), theory('equality')], [c_80497, c_85025])).
% 33.15/21.46  tff(c_120419, plain, (![A_5019, B_5020]: (v5_pre_topc(A_5019, g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), B_5020) | ~v5_pre_topc(A_5019, '#skF_4', B_5020) | ~m1_subset_1(A_5019, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(B_5020)))) | ~v1_funct_2(A_5019, k1_relat_1('#skF_6'), u1_struct_0(B_5020)) | ~v1_funct_1(A_5019) | ~l1_pre_topc(B_5020) | ~v2_pre_topc(B_5020) | ~r1_tarski(A_5019, k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(B_5020))))), inference(demodulation, [status(thm), theory('equality')], [c_81725, c_102, c_100, c_80497, c_80497, c_81725, c_80497, c_80497, c_85058])).
% 33.15/21.46  tff(c_120422, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~r1_tarski('#skF_6', k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))), inference(resolution, [status(thm)], [c_81727, c_120419])).
% 33.15/21.46  tff(c_120442, plain, (v5_pre_topc('#skF_6', g1_pre_topc(k1_relat_1('#skF_6'), u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_81728, c_94, c_81729, c_120422])).
% 33.15/21.46  tff(c_120443, plain, (~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_80579, c_120442])).
% 33.15/21.46  tff(c_120675, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_120443])).
% 33.15/21.46  tff(c_120678, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_120675])).
% 33.15/21.46  tff(c_120682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_120678])).
% 33.15/21.46  tff(c_120683, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_120443])).
% 33.15/21.46  tff(c_120685, plain, (~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_120683])).
% 33.15/21.46  tff(c_80505, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_80497, c_92])).
% 33.15/21.46  tff(c_80504, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_80497, c_90])).
% 33.15/21.46  tff(c_81928, plain, (![D_3645, A_3646, B_3647]: (v5_pre_topc(D_3645, A_3646, g1_pre_topc(u1_struct_0(B_3647), u1_pre_topc(B_3647))) | ~v5_pre_topc(D_3645, A_3646, B_3647) | ~m1_subset_1(D_3645, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3646), u1_struct_0(g1_pre_topc(u1_struct_0(B_3647), u1_pre_topc(B_3647)))))) | ~v1_funct_2(D_3645, u1_struct_0(A_3646), u1_struct_0(g1_pre_topc(u1_struct_0(B_3647), u1_pre_topc(B_3647)))) | ~m1_subset_1(D_3645, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3646), u1_struct_0(B_3647)))) | ~v1_funct_2(D_3645, u1_struct_0(A_3646), u1_struct_0(B_3647)) | ~v1_funct_1(D_3645) | ~l1_pre_topc(B_3647) | ~v2_pre_topc(B_3647) | ~l1_pre_topc(A_3646) | ~v2_pre_topc(A_3646))), inference(cnfTransformation, [status(thm)], [f_210])).
% 33.15/21.46  tff(c_84353, plain, (![A_3779, A_3780, B_3781]: (v5_pre_topc(A_3779, A_3780, g1_pre_topc(u1_struct_0(B_3781), u1_pre_topc(B_3781))) | ~v5_pre_topc(A_3779, A_3780, B_3781) | ~v1_funct_2(A_3779, u1_struct_0(A_3780), u1_struct_0(g1_pre_topc(u1_struct_0(B_3781), u1_pre_topc(B_3781)))) | ~m1_subset_1(A_3779, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_3780), u1_struct_0(B_3781)))) | ~v1_funct_2(A_3779, u1_struct_0(A_3780), u1_struct_0(B_3781)) | ~v1_funct_1(A_3779) | ~l1_pre_topc(B_3781) | ~v2_pre_topc(B_3781) | ~l1_pre_topc(A_3780) | ~v2_pre_topc(A_3780) | ~r1_tarski(A_3779, k2_zfmisc_1(u1_struct_0(A_3780), u1_struct_0(g1_pre_topc(u1_struct_0(B_3781), u1_pre_topc(B_3781))))))), inference(resolution, [status(thm)], [c_24, c_81928])).
% 33.15/21.46  tff(c_84378, plain, (![A_3779, B_3781]: (v5_pre_topc(A_3779, '#skF_4', g1_pre_topc(u1_struct_0(B_3781), u1_pre_topc(B_3781))) | ~v5_pre_topc(A_3779, '#skF_4', B_3781) | ~v1_funct_2(A_3779, u1_struct_0('#skF_4'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3781), u1_pre_topc(B_3781)))) | ~m1_subset_1(A_3779, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_3781)))) | ~v1_funct_2(A_3779, u1_struct_0('#skF_4'), u1_struct_0(B_3781)) | ~v1_funct_1(A_3779) | ~l1_pre_topc(B_3781) | ~v2_pre_topc(B_3781) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~r1_tarski(A_3779, k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(B_3781), u1_pre_topc(B_3781))))))), inference(superposition, [status(thm), theory('equality')], [c_80497, c_84353])).
% 33.15/21.46  tff(c_127974, plain, (![A_5257, B_5258]: (v5_pre_topc(A_5257, '#skF_4', g1_pre_topc(u1_struct_0(B_5258), u1_pre_topc(B_5258))) | ~v5_pre_topc(A_5257, '#skF_4', B_5258) | ~v1_funct_2(A_5257, k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(B_5258), u1_pre_topc(B_5258)))) | ~m1_subset_1(A_5257, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(B_5258)))) | ~v1_funct_2(A_5257, k1_relat_1('#skF_6'), u1_struct_0(B_5258)) | ~v1_funct_1(A_5257) | ~l1_pre_topc(B_5258) | ~v2_pre_topc(B_5258) | ~r1_tarski(A_5257, k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0(B_5258), u1_pre_topc(B_5258))))))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_80497, c_80497, c_80497, c_84378])).
% 33.15/21.46  tff(c_128027, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), u1_struct_0('#skF_5')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_81728, c_127974])).
% 33.15/21.46  tff(c_128092, plain, (v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_94, c_80505, c_80504, c_81729, c_79529, c_128027])).
% 33.15/21.46  tff(c_128094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120685, c_128092])).
% 33.15/21.46  tff(c_128095, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_120683])).
% 33.15/21.46  tff(c_128099, plain, (~r1_tarski(u1_pre_topc('#skF_5'), u1_pre_topc('#skF_5')) | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_98857, c_128095])).
% 33.15/21.46  tff(c_128109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_308, c_128099])).
% 33.15/21.46  tff(c_128110, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_79700])).
% 33.15/21.46  tff(c_128126, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_128110, c_14])).
% 33.15/21.46  tff(c_79696, plain, (![C_3500]: (v1_xboole_0(C_3500) | ~m1_subset_1(C_3500, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_79680])).
% 33.15/21.46  tff(c_79725, plain, (![C_3508]: (v1_xboole_0(C_3508) | ~m1_subset_1(C_3508, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_79696])).
% 33.15/21.46  tff(c_79739, plain, (![B_3509]: (v1_xboole_0('#skF_3'(k1_xboole_0, B_3509)))), inference(resolution, [status(thm)], [c_190, c_79725])).
% 33.15/21.46  tff(c_79778, plain, (![B_3511]: ('#skF_3'(k1_xboole_0, B_3511)=k1_xboole_0)), inference(resolution, [status(thm)], [c_79739, c_14])).
% 33.15/21.46  tff(c_79807, plain, (![B_3511]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_3511))), inference(superposition, [status(thm), theory('equality')], [c_79778, c_52])).
% 33.15/21.46  tff(c_128136, plain, (![B_3511]: (v1_funct_2('#skF_6', '#skF_6', B_3511))), inference(demodulation, [status(thm), theory('equality')], [c_128126, c_128126, c_79807])).
% 33.15/21.46  tff(c_79751, plain, (![B_3509]: ('#skF_3'(k1_xboole_0, B_3509)=k1_xboole_0)), inference(resolution, [status(thm)], [c_79739, c_14])).
% 33.15/21.46  tff(c_80715, plain, (![C_3567, A_3568, B_3569]: (v1_partfun1(C_3567, A_3568) | ~v1_funct_2(C_3567, A_3568, B_3569) | ~v1_funct_1(C_3567) | ~m1_subset_1(C_3567, k1_zfmisc_1(k2_zfmisc_1(A_3568, B_3569))) | v1_xboole_0(B_3569))), inference(cnfTransformation, [status(thm)], [f_93])).
% 33.15/21.46  tff(c_80721, plain, (![A_38, B_39]: (v1_partfun1('#skF_3'(A_38, B_39), A_38) | ~v1_funct_2('#skF_3'(A_38, B_39), A_38, B_39) | ~v1_funct_1('#skF_3'(A_38, B_39)) | v1_xboole_0(B_39))), inference(resolution, [status(thm)], [c_62, c_80715])).
% 33.15/21.46  tff(c_80741, plain, (![A_3570, B_3571]: (v1_partfun1('#skF_3'(A_3570, B_3571), A_3570) | v1_xboole_0(B_3571))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_80721])).
% 33.15/21.46  tff(c_80750, plain, (![B_3509]: (v1_partfun1(k1_xboole_0, k1_xboole_0) | v1_xboole_0(B_3509))), inference(superposition, [status(thm), theory('equality')], [c_79751, c_80741])).
% 33.15/21.46  tff(c_80752, plain, (v1_partfun1(k1_xboole_0, k1_xboole_0)), inference(splitLeft, [status(thm)], [c_80750])).
% 33.15/21.46  tff(c_127, plain, (![B_89]: (k2_zfmisc_1(k1_xboole_0, B_89)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 33.15/21.46  tff(c_131, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127, c_28])).
% 33.15/21.46  tff(c_79590, plain, (![A_3486, A_3487, B_3488]: (v4_relat_1(A_3486, A_3487) | ~r1_tarski(A_3486, k2_zfmisc_1(A_3487, B_3488)))), inference(resolution, [status(thm)], [c_24, c_363])).
% 33.15/21.46  tff(c_79617, plain, (![A_3489, B_3490]: (v4_relat_1(k2_zfmisc_1(A_3489, B_3490), A_3489))), inference(resolution, [status(thm)], [c_308, c_79590])).
% 33.15/21.46  tff(c_79620, plain, (![A_11]: (v4_relat_1(k1_xboole_0, A_11))), inference(superposition, [status(thm), theory('equality')], [c_18, c_79617])).
% 33.15/21.46  tff(c_79981, plain, (![A_11]: (k1_relat_1(k1_xboole_0)=A_11 | ~v1_partfun1(k1_xboole_0, A_11) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_79620, c_79972])).
% 33.15/21.46  tff(c_80000, plain, (![A_11]: (k1_relat_1(k1_xboole_0)=A_11 | ~v1_partfun1(k1_xboole_0, A_11))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_79981])).
% 33.15/21.46  tff(c_80756, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_80752, c_80000])).
% 33.15/21.46  tff(c_128182, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_128126, c_128126, c_80756])).
% 33.15/21.46  tff(c_128195, plain, (u1_struct_0('#skF_4')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_128182, c_80497])).
% 33.15/21.46  tff(c_128152, plain, (![B_12]: (k2_zfmisc_1('#skF_6', B_12)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_128126, c_128126, c_20])).
% 33.15/21.46  tff(c_128140, plain, (![B_3509]: ('#skF_3'('#skF_6', B_3509)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_128126, c_128126, c_79751])).
% 33.15/21.46  tff(c_191, plain, (![A_109, B_110]: (r1_tarski('#skF_3'(A_109, B_110), k2_zfmisc_1(A_109, B_110)))), inference(resolution, [status(thm)], [c_181, c_22])).
% 33.15/21.46  tff(c_129473, plain, (![A_5341, B_5342, B_5343]: (r2_hidden('#skF_2'(A_5341, B_5342), B_5343) | ~r1_tarski(A_5341, B_5343) | r1_tarski(A_5341, B_5342))), inference(resolution, [status(thm)], [c_10, c_356])).
% 33.15/21.46  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 33.15/21.46  tff(c_129486, plain, (![B_5344, A_5345, B_5346]: (~v1_xboole_0(B_5344) | ~r1_tarski(A_5345, B_5344) | r1_tarski(A_5345, B_5346))), inference(resolution, [status(thm)], [c_129473, c_2])).
% 33.15/21.46  tff(c_129584, plain, (![A_5351, B_5352, B_5353]: (~v1_xboole_0(k2_zfmisc_1(A_5351, B_5352)) | r1_tarski('#skF_3'(A_5351, B_5352), B_5353))), inference(resolution, [status(thm)], [c_191, c_129486])).
% 33.15/21.46  tff(c_129625, plain, (![B_3509, B_5353]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', B_3509)) | r1_tarski('#skF_6', B_5353))), inference(superposition, [status(thm), theory('equality')], [c_128140, c_129584])).
% 33.15/21.46  tff(c_129640, plain, (![B_5353]: (r1_tarski('#skF_6', B_5353))), inference(demodulation, [status(thm), theory('equality')], [c_128110, c_128152, c_129625])).
% 33.15/21.46  tff(c_79710, plain, (![A_3506, B_3507]: (v1_xboole_0('#skF_3'(A_3506, B_3507)) | ~v1_xboole_0(B_3507))), inference(resolution, [status(thm)], [c_62, c_79680])).
% 33.15/21.46  tff(c_79722, plain, (![A_3506, B_3507]: ('#skF_3'(A_3506, B_3507)=k1_xboole_0 | ~v1_xboole_0(B_3507))), inference(resolution, [status(thm)], [c_79710, c_14])).
% 33.15/21.46  tff(c_128123, plain, (![A_3506]: ('#skF_3'(A_3506, '#skF_6')=k1_xboole_0)), inference(resolution, [status(thm)], [c_128110, c_79722])).
% 33.15/21.46  tff(c_128365, plain, (![A_3506]: ('#skF_3'(A_3506, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_128126, c_128123])).
% 33.15/21.46  tff(c_128111, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))), inference(splitRight, [status(thm)], [c_79700])).
% 33.15/21.46  tff(c_128150, plain, (![A_10]: (A_10='#skF_6' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_128126, c_14])).
% 33.15/21.46  tff(c_128727, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))='#skF_6'), inference(resolution, [status(thm)], [c_128111, c_128150])).
% 33.15/21.46  tff(c_128467, plain, (![D_5269, A_5270, B_5271]: (v5_pre_topc(D_5269, A_5270, g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271))) | ~v5_pre_topc(D_5269, A_5270, B_5271) | ~m1_subset_1(D_5269, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5270), u1_struct_0(g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271)))))) | ~v1_funct_2(D_5269, u1_struct_0(A_5270), u1_struct_0(g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271)))) | ~m1_subset_1(D_5269, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5270), u1_struct_0(B_5271)))) | ~v1_funct_2(D_5269, u1_struct_0(A_5270), u1_struct_0(B_5271)) | ~v1_funct_1(D_5269) | ~l1_pre_topc(B_5271) | ~v2_pre_topc(B_5271) | ~l1_pre_topc(A_5270) | ~v2_pre_topc(A_5270))), inference(cnfTransformation, [status(thm)], [f_210])).
% 33.15/21.46  tff(c_128477, plain, (![A_5270, B_5271]: (v5_pre_topc('#skF_3'(u1_struct_0(A_5270), u1_struct_0(g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271)))), A_5270, g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_5270), u1_struct_0(g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271)))), A_5270, B_5271) | ~v1_funct_2('#skF_3'(u1_struct_0(A_5270), u1_struct_0(g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271)))), u1_struct_0(A_5270), u1_struct_0(g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271)))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_5270), u1_struct_0(g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5270), u1_struct_0(B_5271)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_5270), u1_struct_0(g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271)))), u1_struct_0(A_5270), u1_struct_0(B_5271)) | ~v1_funct_1('#skF_3'(u1_struct_0(A_5270), u1_struct_0(g1_pre_topc(u1_struct_0(B_5271), u1_pre_topc(B_5271))))) | ~l1_pre_topc(B_5271) | ~v2_pre_topc(B_5271) | ~l1_pre_topc(A_5270) | ~v2_pre_topc(A_5270))), inference(resolution, [status(thm)], [c_62, c_128467])).
% 33.15/21.46  tff(c_132639, plain, (![A_5517, B_5518]: (v5_pre_topc('#skF_3'(u1_struct_0(A_5517), u1_struct_0(g1_pre_topc(u1_struct_0(B_5518), u1_pre_topc(B_5518)))), A_5517, g1_pre_topc(u1_struct_0(B_5518), u1_pre_topc(B_5518))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_5517), u1_struct_0(g1_pre_topc(u1_struct_0(B_5518), u1_pre_topc(B_5518)))), A_5517, B_5518) | ~m1_subset_1('#skF_3'(u1_struct_0(A_5517), u1_struct_0(g1_pre_topc(u1_struct_0(B_5518), u1_pre_topc(B_5518)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5517), u1_struct_0(B_5518)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_5517), u1_struct_0(g1_pre_topc(u1_struct_0(B_5518), u1_pre_topc(B_5518)))), u1_struct_0(A_5517), u1_struct_0(B_5518)) | ~l1_pre_topc(B_5518) | ~v2_pre_topc(B_5518) | ~l1_pre_topc(A_5517) | ~v2_pre_topc(A_5517))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_128477])).
% 33.15/21.46  tff(c_141834, plain, (![A_5855, B_5856]: (v5_pre_topc('#skF_3'(u1_struct_0(A_5855), u1_struct_0(g1_pre_topc(u1_struct_0(B_5856), u1_pre_topc(B_5856)))), A_5855, g1_pre_topc(u1_struct_0(B_5856), u1_pre_topc(B_5856))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_5855), u1_struct_0(g1_pre_topc(u1_struct_0(B_5856), u1_pre_topc(B_5856)))), A_5855, B_5856) | ~v1_funct_2('#skF_3'(u1_struct_0(A_5855), u1_struct_0(g1_pre_topc(u1_struct_0(B_5856), u1_pre_topc(B_5856)))), u1_struct_0(A_5855), u1_struct_0(B_5856)) | ~l1_pre_topc(B_5856) | ~v2_pre_topc(B_5856) | ~l1_pre_topc(A_5855) | ~v2_pre_topc(A_5855) | ~r1_tarski('#skF_3'(u1_struct_0(A_5855), u1_struct_0(g1_pre_topc(u1_struct_0(B_5856), u1_pre_topc(B_5856)))), k2_zfmisc_1(u1_struct_0(A_5855), u1_struct_0(B_5856))))), inference(resolution, [status(thm)], [c_24, c_132639])).
% 33.15/21.46  tff(c_141848, plain, (![A_5855]: (v5_pre_topc('#skF_3'(u1_struct_0(A_5855), '#skF_6'), A_5855, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_5855), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), A_5855, '#skF_5') | ~v1_funct_2('#skF_3'(u1_struct_0(A_5855), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), u1_struct_0(A_5855), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_5855) | ~v2_pre_topc(A_5855) | ~r1_tarski('#skF_3'(u1_struct_0(A_5855), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), k2_zfmisc_1(u1_struct_0(A_5855), u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_128727, c_141834])).
% 33.15/21.46  tff(c_142215, plain, (![A_5875]: (v5_pre_topc('#skF_6', A_5875, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', A_5875, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0(A_5875), u1_struct_0('#skF_5')) | ~l1_pre_topc(A_5875) | ~v2_pre_topc(A_5875))), inference(demodulation, [status(thm), theory('equality')], [c_129640, c_128365, c_128727, c_98, c_96, c_128365, c_128727, c_128365, c_128727, c_128365, c_141848])).
% 33.15/21.46  tff(c_128187, plain, (~v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_128182, c_80579])).
% 33.15/21.46  tff(c_79548, plain, (![A_3467, B_3468]: (v1_pre_topc(g1_pre_topc(A_3467, B_3468)) | ~m1_subset_1(B_3468, k1_zfmisc_1(k1_zfmisc_1(A_3467))))), inference(cnfTransformation, [status(thm)], [f_140])).
% 33.15/21.46  tff(c_79556, plain, (![A_43]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_43), u1_pre_topc(A_43))) | ~l1_pre_topc(A_43))), inference(resolution, [status(thm)], [c_68, c_79548])).
% 33.15/21.46  tff(c_128817, plain, (v1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_128727, c_79556])).
% 33.15/21.46  tff(c_129552, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_128817])).
% 33.15/21.46  tff(c_129555, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_330, c_129552])).
% 33.15/21.46  tff(c_129562, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_129555])).
% 33.15/21.46  tff(c_129564, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_128817])).
% 33.15/21.46  tff(c_128820, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_128727, c_70])).
% 33.15/21.46  tff(c_131365, plain, (v2_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_129564, c_128820])).
% 33.15/21.46  tff(c_131366, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitLeft, [status(thm)], [c_131365])).
% 33.15/21.46  tff(c_131369, plain, (~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_70, c_131366])).
% 33.15/21.46  tff(c_131373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_131369])).
% 33.15/21.46  tff(c_131375, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(splitRight, [status(thm)], [c_131365])).
% 33.15/21.46  tff(c_79754, plain, (![A_3510]: (v1_xboole_0('#skF_3'(A_3510, k1_xboole_0)))), inference(resolution, [status(thm)], [c_187, c_79725])).
% 33.15/21.46  tff(c_79842, plain, (![A_3512]: ('#skF_3'(A_3512, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_79754, c_14])).
% 33.15/21.46  tff(c_79859, plain, (![A_3512]: (v1_funct_2(k1_xboole_0, A_3512, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_79842, c_52])).
% 33.15/21.46  tff(c_128137, plain, (![A_3512]: (v1_funct_2('#skF_6', A_3512, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_128126, c_128126, c_79859])).
% 33.15/21.46  tff(c_79773, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_79751, c_190])).
% 33.15/21.46  tff(c_128138, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_128126, c_128126, c_79773])).
% 33.15/21.46  tff(c_128149, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_128126, c_128126, c_18])).
% 33.15/21.46  tff(c_128674, plain, (![D_5288, A_5289, B_5290]: (v5_pre_topc(D_5288, g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289)), B_5290) | ~v5_pre_topc(D_5288, A_5289, B_5290) | ~m1_subset_1(D_5288, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289))), u1_struct_0(B_5290)))) | ~v1_funct_2(D_5288, u1_struct_0(g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289))), u1_struct_0(B_5290)) | ~m1_subset_1(D_5288, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5289), u1_struct_0(B_5290)))) | ~v1_funct_2(D_5288, u1_struct_0(A_5289), u1_struct_0(B_5290)) | ~v1_funct_1(D_5288) | ~l1_pre_topc(B_5290) | ~v2_pre_topc(B_5290) | ~l1_pre_topc(A_5289) | ~v2_pre_topc(A_5289))), inference(cnfTransformation, [status(thm)], [f_181])).
% 33.15/21.46  tff(c_128684, plain, (![A_5289, B_5290]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289))), u1_struct_0(B_5290)), g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289)), B_5290) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289))), u1_struct_0(B_5290)), A_5289, B_5290) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289))), u1_struct_0(B_5290)), u1_struct_0(g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289))), u1_struct_0(B_5290)) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289))), u1_struct_0(B_5290)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5289), u1_struct_0(B_5290)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289))), u1_struct_0(B_5290)), u1_struct_0(A_5289), u1_struct_0(B_5290)) | ~v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5289), u1_pre_topc(A_5289))), u1_struct_0(B_5290))) | ~l1_pre_topc(B_5290) | ~v2_pre_topc(B_5290) | ~l1_pre_topc(A_5289) | ~v2_pre_topc(A_5289))), inference(resolution, [status(thm)], [c_62, c_128674])).
% 33.15/21.46  tff(c_133630, plain, (![A_5573, B_5574]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573))), u1_struct_0(B_5574)), g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573)), B_5574) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573))), u1_struct_0(B_5574)), A_5573, B_5574) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573))), u1_struct_0(B_5574)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5573), u1_struct_0(B_5574)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573))), u1_struct_0(B_5574)), u1_struct_0(A_5573), u1_struct_0(B_5574)) | ~l1_pre_topc(B_5574) | ~v2_pre_topc(B_5574) | ~l1_pre_topc(A_5573) | ~v2_pre_topc(A_5573))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_128684])).
% 33.15/21.46  tff(c_133636, plain, (![A_5573]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573)), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), A_5573, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573))), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5573), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5573), u1_pre_topc(A_5573))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), u1_struct_0(A_5573), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(A_5573) | ~v2_pre_topc(A_5573))), inference(superposition, [status(thm), theory('equality')], [c_128727, c_133630])).
% 33.15/21.46  tff(c_136008, plain, (![A_5662]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_5662), u1_pre_topc(A_5662)), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', A_5662, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc(A_5662) | ~v2_pre_topc(A_5662))), inference(demodulation, [status(thm), theory('equality')], [c_131375, c_129564, c_128137, c_128365, c_128727, c_128727, c_128138, c_128149, c_128365, c_128727, c_128365, c_128727, c_128365, c_128727, c_133636])).
% 33.15/21.46  tff(c_136017, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_128195, c_136008])).
% 33.15/21.46  tff(c_136022, plain, (v5_pre_topc('#skF_6', g1_pre_topc('#skF_6', u1_pre_topc('#skF_4')), g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_136017])).
% 33.15/21.46  tff(c_136023, plain, (~v5_pre_topc('#skF_6', '#skF_4', g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_128187, c_136022])).
% 33.15/21.46  tff(c_142228, plain, (~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_142215, c_136023])).
% 33.15/21.46  tff(c_142248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_128136, c_128195, c_79529, c_142228])).
% 33.15/21.46  tff(c_142249, plain, (![B_3509]: (v1_xboole_0(B_3509))), inference(splitRight, [status(thm)], [c_80750])).
% 33.15/21.46  tff(c_142289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142249, c_79708])).
% 33.15/21.46  tff(c_142290, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_79703])).
% 33.15/21.46  tff(c_142303, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_142290, c_14])).
% 33.15/21.46  tff(c_142319, plain, (![A_111]: (r1_tarski('#skF_3'(A_111, '#skF_6'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_142303, c_142303, c_196])).
% 33.15/21.46  tff(c_79705, plain, (![C_3500]: (v1_xboole_0(C_3500) | ~m1_subset_1(C_3500, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_79696])).
% 33.15/21.46  tff(c_142608, plain, (![C_5898]: (v1_xboole_0(C_5898) | ~m1_subset_1(C_5898, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_142303, c_79705])).
% 33.15/21.46  tff(c_142619, plain, (![A_5899]: (v1_xboole_0(A_5899) | ~r1_tarski(A_5899, '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_142608])).
% 33.15/21.46  tff(c_142639, plain, (![A_5900]: (v1_xboole_0('#skF_3'(A_5900, '#skF_6')))), inference(resolution, [status(thm)], [c_142319, c_142619])).
% 33.15/21.46  tff(c_142322, plain, (![A_10]: (A_10='#skF_6' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_142303, c_14])).
% 33.15/21.46  tff(c_142678, plain, (![A_5902]: ('#skF_3'(A_5902, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_142639, c_142322])).
% 33.15/21.46  tff(c_142704, plain, (![A_5902]: (v1_funct_2('#skF_6', A_5902, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_142678, c_52])).
% 33.15/21.46  tff(c_142291, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_79703])).
% 33.15/21.46  tff(c_142448, plain, (![A_5881]: (A_5881='#skF_6' | ~v1_xboole_0(A_5881))), inference(demodulation, [status(thm), theory('equality')], [c_142303, c_14])).
% 33.15/21.46  tff(c_142455, plain, (u1_struct_0('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_142291, c_142448])).
% 33.15/21.46  tff(c_142649, plain, (![A_5900]: ('#skF_3'(A_5900, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_142639, c_142322])).
% 33.15/21.46  tff(c_142321, plain, (![A_11]: (k2_zfmisc_1(A_11, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142303, c_142303, c_18])).
% 33.15/21.46  tff(c_142464, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_142455, c_90])).
% 33.15/21.46  tff(c_142470, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_142321, c_142464])).
% 33.15/21.46  tff(c_161087, plain, (![D_6710, A_6711, B_6712]: (v5_pre_topc(D_6710, g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711)), B_6712) | ~v5_pre_topc(D_6710, A_6711, B_6712) | ~m1_subset_1(D_6710, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711))), u1_struct_0(B_6712)))) | ~v1_funct_2(D_6710, u1_struct_0(g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711))), u1_struct_0(B_6712)) | ~m1_subset_1(D_6710, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6711), u1_struct_0(B_6712)))) | ~v1_funct_2(D_6710, u1_struct_0(A_6711), u1_struct_0(B_6712)) | ~v1_funct_1(D_6710) | ~l1_pre_topc(B_6712) | ~v2_pre_topc(B_6712) | ~l1_pre_topc(A_6711) | ~v2_pre_topc(A_6711))), inference(cnfTransformation, [status(thm)], [f_181])).
% 33.15/21.46  tff(c_161103, plain, (![A_6711, B_6712]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711))), u1_struct_0(B_6712)), g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711)), B_6712) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711))), u1_struct_0(B_6712)), A_6711, B_6712) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711))), u1_struct_0(B_6712)), u1_struct_0(g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711))), u1_struct_0(B_6712)) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711))), u1_struct_0(B_6712)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6711), u1_struct_0(B_6712)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711))), u1_struct_0(B_6712)), u1_struct_0(A_6711), u1_struct_0(B_6712)) | ~v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6711), u1_pre_topc(A_6711))), u1_struct_0(B_6712))) | ~l1_pre_topc(B_6712) | ~v2_pre_topc(B_6712) | ~l1_pre_topc(A_6711) | ~v2_pre_topc(A_6711))), inference(resolution, [status(thm)], [c_62, c_161087])).
% 33.15/21.46  tff(c_165899, plain, (![A_7003, B_7004]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003))), u1_struct_0(B_7004)), g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003)), B_7004) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003))), u1_struct_0(B_7004)), A_7003, B_7004) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003))), u1_struct_0(B_7004)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7003), u1_struct_0(B_7004)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003))), u1_struct_0(B_7004)), u1_struct_0(A_7003), u1_struct_0(B_7004)) | ~l1_pre_topc(B_7004) | ~v2_pre_topc(B_7004) | ~l1_pre_topc(A_7003) | ~v2_pre_topc(A_7003))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_161103])).
% 33.15/21.46  tff(c_165915, plain, (![A_7003]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003))), u1_struct_0('#skF_5')), g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003)), '#skF_5') | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003))), u1_struct_0('#skF_5')), A_7003, '#skF_5') | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003))), u1_struct_0('#skF_5')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_7003), '#skF_6'))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_7003), u1_pre_topc(A_7003))), u1_struct_0('#skF_5')), u1_struct_0(A_7003), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_7003) | ~v2_pre_topc(A_7003))), inference(superposition, [status(thm), theory('equality')], [c_142455, c_165899])).
% 33.15/21.46  tff(c_173142, plain, (![A_7253]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_7253), u1_pre_topc(A_7253)), '#skF_5') | ~v5_pre_topc('#skF_6', A_7253, '#skF_5') | ~l1_pre_topc(A_7253) | ~v2_pre_topc(A_7253))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_142704, c_142455, c_142649, c_142455, c_142470, c_142321, c_142649, c_142455, c_142649, c_142455, c_142649, c_142455, c_165915])).
% 33.15/21.46  tff(c_143200, plain, (![D_5945, A_5946, B_5947]: (v5_pre_topc(D_5945, g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946)), B_5947) | ~v5_pre_topc(D_5945, A_5946, B_5947) | ~m1_subset_1(D_5945, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946))), u1_struct_0(B_5947)))) | ~v1_funct_2(D_5945, u1_struct_0(g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946))), u1_struct_0(B_5947)) | ~m1_subset_1(D_5945, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5946), u1_struct_0(B_5947)))) | ~v1_funct_2(D_5945, u1_struct_0(A_5946), u1_struct_0(B_5947)) | ~v1_funct_1(D_5945) | ~l1_pre_topc(B_5947) | ~v2_pre_topc(B_5947) | ~l1_pre_topc(A_5946) | ~v2_pre_topc(A_5946))), inference(cnfTransformation, [status(thm)], [f_181])).
% 33.15/21.46  tff(c_143219, plain, (![A_5946, B_5947]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946))), u1_struct_0(B_5947)), g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946)), B_5947) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946))), u1_struct_0(B_5947)), A_5946, B_5947) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946))), u1_struct_0(B_5947)), u1_struct_0(g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946))), u1_struct_0(B_5947)) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946))), u1_struct_0(B_5947)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5946), u1_struct_0(B_5947)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946))), u1_struct_0(B_5947)), u1_struct_0(A_5946), u1_struct_0(B_5947)) | ~v1_funct_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_5946), u1_pre_topc(A_5946))), u1_struct_0(B_5947))) | ~l1_pre_topc(B_5947) | ~v2_pre_topc(B_5947) | ~l1_pre_topc(A_5946) | ~v2_pre_topc(A_5946))), inference(resolution, [status(thm)], [c_62, c_143200])).
% 33.15/21.46  tff(c_146766, plain, (![A_6161, B_6162]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161))), u1_struct_0(B_6162)), g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161)), B_6162) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161))), u1_struct_0(B_6162)), A_6161, B_6162) | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161))), u1_struct_0(B_6162)), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6161), u1_struct_0(B_6162)))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161))), u1_struct_0(B_6162)), u1_struct_0(A_6161), u1_struct_0(B_6162)) | ~l1_pre_topc(B_6162) | ~v2_pre_topc(B_6162) | ~l1_pre_topc(A_6161) | ~v2_pre_topc(A_6161))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_143219])).
% 33.15/21.46  tff(c_146780, plain, (![A_6161]: (v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161))), u1_struct_0('#skF_5')), g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161)), '#skF_5') | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161))), u1_struct_0('#skF_5')), A_6161, '#skF_5') | ~m1_subset_1('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161))), '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6161), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161))), u1_struct_0('#skF_5')), u1_struct_0(A_6161), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_6161) | ~v2_pre_topc(A_6161))), inference(superposition, [status(thm), theory('equality')], [c_142455, c_146766])).
% 33.15/21.46  tff(c_146799, plain, (![A_6161]: (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0(A_6161), u1_pre_topc(A_6161)), '#skF_5') | ~v5_pre_topc('#skF_6', A_6161, '#skF_5') | ~l1_pre_topc(A_6161) | ~v2_pre_topc(A_6161))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_142704, c_142649, c_142455, c_142455, c_142470, c_142649, c_142321, c_142455, c_142649, c_142455, c_142649, c_142455, c_146780])).
% 33.15/21.46  tff(c_142606, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_142455, c_79528])).
% 33.15/21.46  tff(c_142324, plain, (![B_12]: (k2_zfmisc_1('#skF_6', B_12)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_142303, c_142303, c_20])).
% 33.15/21.46  tff(c_142317, plain, (![B_113]: (r1_tarski('#skF_3'('#skF_6', B_113), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_142303, c_142303, c_202])).
% 33.15/21.46  tff(c_142655, plain, (![B_5901]: (v1_xboole_0('#skF_3'('#skF_6', B_5901)))), inference(resolution, [status(thm)], [c_142317, c_142619])).
% 33.15/21.46  tff(c_142665, plain, (![B_5901]: ('#skF_3'('#skF_6', B_5901)='#skF_6')), inference(resolution, [status(thm)], [c_142655, c_142322])).
% 33.15/21.46  tff(c_144035, plain, (![A_6002, B_6003, B_6004]: (r2_hidden('#skF_2'(A_6002, B_6003), B_6004) | ~r1_tarski(A_6002, B_6004) | r1_tarski(A_6002, B_6003))), inference(resolution, [status(thm)], [c_10, c_356])).
% 33.15/21.46  tff(c_144048, plain, (![B_6005, A_6006, B_6007]: (~v1_xboole_0(B_6005) | ~r1_tarski(A_6006, B_6005) | r1_tarski(A_6006, B_6007))), inference(resolution, [status(thm)], [c_144035, c_2])).
% 33.15/21.46  tff(c_144067, plain, (![A_6008, B_6009, B_6010]: (~v1_xboole_0(k2_zfmisc_1(A_6008, B_6009)) | r1_tarski('#skF_3'(A_6008, B_6009), B_6010))), inference(resolution, [status(thm)], [c_191, c_144048])).
% 33.15/21.46  tff(c_144108, plain, (![B_5901, B_6010]: (~v1_xboole_0(k2_zfmisc_1('#skF_6', B_5901)) | r1_tarski('#skF_6', B_6010))), inference(superposition, [status(thm), theory('equality')], [c_142665, c_144067])).
% 33.15/21.46  tff(c_144123, plain, (![B_6010]: (r1_tarski('#skF_6', B_6010))), inference(demodulation, [status(thm), theory('equality')], [c_142290, c_142324, c_144108])).
% 33.15/21.46  tff(c_142462, plain, (v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_142455, c_114])).
% 33.15/21.46  tff(c_142461, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))))))), inference(demodulation, [status(thm), theory('equality')], [c_142455, c_115])).
% 33.15/21.46  tff(c_142928, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(resolution, [status(thm)], [c_142461, c_44])).
% 33.15/21.46  tff(c_142952, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_142462, c_142290, c_142928])).
% 33.15/21.46  tff(c_143030, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))), inference(splitLeft, [status(thm)], [c_142952])).
% 33.15/21.46  tff(c_143043, plain, (u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))='#skF_6'), inference(resolution, [status(thm)], [c_143030, c_142322])).
% 33.15/21.46  tff(c_143084, plain, (l1_pre_topc(g1_pre_topc('#skF_6', u1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_143043, c_330])).
% 33.15/21.46  tff(c_158426, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_143084])).
% 33.15/21.46  tff(c_158451, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_330, c_158426])).
% 33.15/21.46  tff(c_158458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_158451])).
% 33.15/21.46  tff(c_158460, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_143084])).
% 33.15/21.46  tff(c_142739, plain, (![B_5903]: ('#skF_3'('#skF_6', B_5903)='#skF_6')), inference(resolution, [status(thm)], [c_142655, c_142322])).
% 33.15/21.46  tff(c_142756, plain, (![B_5903]: (v1_funct_2('#skF_6', '#skF_6', B_5903))), inference(superposition, [status(thm), theory('equality')], [c_142739, c_52])).
% 33.15/21.46  tff(c_143101, plain, (![D_5932, A_5933, B_5934]: (v5_pre_topc(D_5932, A_5933, g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934))) | ~v5_pre_topc(D_5932, A_5933, B_5934) | ~m1_subset_1(D_5932, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5933), u1_struct_0(g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934)))))) | ~v1_funct_2(D_5932, u1_struct_0(A_5933), u1_struct_0(g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934)))) | ~m1_subset_1(D_5932, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5933), u1_struct_0(B_5934)))) | ~v1_funct_2(D_5932, u1_struct_0(A_5933), u1_struct_0(B_5934)) | ~v1_funct_1(D_5932) | ~l1_pre_topc(B_5934) | ~v2_pre_topc(B_5934) | ~l1_pre_topc(A_5933) | ~v2_pre_topc(A_5933))), inference(cnfTransformation, [status(thm)], [f_210])).
% 33.15/21.46  tff(c_143120, plain, (![A_5933, B_5934]: (v5_pre_topc('#skF_3'(u1_struct_0(A_5933), u1_struct_0(g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934)))), A_5933, g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_5933), u1_struct_0(g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934)))), A_5933, B_5934) | ~v1_funct_2('#skF_3'(u1_struct_0(A_5933), u1_struct_0(g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934)))), u1_struct_0(A_5933), u1_struct_0(g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934)))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_5933), u1_struct_0(g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_5933), u1_struct_0(B_5934)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_5933), u1_struct_0(g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934)))), u1_struct_0(A_5933), u1_struct_0(B_5934)) | ~v1_funct_1('#skF_3'(u1_struct_0(A_5933), u1_struct_0(g1_pre_topc(u1_struct_0(B_5934), u1_pre_topc(B_5934))))) | ~l1_pre_topc(B_5934) | ~v2_pre_topc(B_5934) | ~l1_pre_topc(A_5933) | ~v2_pre_topc(A_5933))), inference(resolution, [status(thm)], [c_62, c_143101])).
% 33.15/21.46  tff(c_147793, plain, (![A_6219, B_6220]: (v5_pre_topc('#skF_3'(u1_struct_0(A_6219), u1_struct_0(g1_pre_topc(u1_struct_0(B_6220), u1_pre_topc(B_6220)))), A_6219, g1_pre_topc(u1_struct_0(B_6220), u1_pre_topc(B_6220))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_6219), u1_struct_0(g1_pre_topc(u1_struct_0(B_6220), u1_pre_topc(B_6220)))), A_6219, B_6220) | ~m1_subset_1('#skF_3'(u1_struct_0(A_6219), u1_struct_0(g1_pre_topc(u1_struct_0(B_6220), u1_pre_topc(B_6220)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6219), u1_struct_0(B_6220)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_6219), u1_struct_0(g1_pre_topc(u1_struct_0(B_6220), u1_pre_topc(B_6220)))), u1_struct_0(A_6219), u1_struct_0(B_6220)) | ~l1_pre_topc(B_6220) | ~v2_pre_topc(B_6220) | ~l1_pre_topc(A_6219) | ~v2_pre_topc(A_6219))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_143120])).
% 33.15/21.46  tff(c_157163, plain, (![A_6560, B_6561]: (v5_pre_topc('#skF_3'(u1_struct_0(A_6560), u1_struct_0(g1_pre_topc(u1_struct_0(B_6561), u1_pre_topc(B_6561)))), A_6560, g1_pre_topc(u1_struct_0(B_6561), u1_pre_topc(B_6561))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_6560), u1_struct_0(g1_pre_topc(u1_struct_0(B_6561), u1_pre_topc(B_6561)))), A_6560, B_6561) | ~v1_funct_2('#skF_3'(u1_struct_0(A_6560), u1_struct_0(g1_pre_topc(u1_struct_0(B_6561), u1_pre_topc(B_6561)))), u1_struct_0(A_6560), u1_struct_0(B_6561)) | ~l1_pre_topc(B_6561) | ~v2_pre_topc(B_6561) | ~l1_pre_topc(A_6560) | ~v2_pre_topc(A_6560) | ~r1_tarski('#skF_3'(u1_struct_0(A_6560), u1_struct_0(g1_pre_topc(u1_struct_0(B_6561), u1_pre_topc(B_6561)))), k2_zfmisc_1(u1_struct_0(A_6560), u1_struct_0(B_6561))))), inference(resolution, [status(thm)], [c_24, c_147793])).
% 33.15/21.46  tff(c_157189, plain, (![A_6560]: (v5_pre_topc('#skF_3'(u1_struct_0(A_6560), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), A_6560, g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_6560), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), A_6560, '#skF_5') | ~v1_funct_2('#skF_3'(u1_struct_0(A_6560), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), u1_struct_0(A_6560), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_6560) | ~v2_pre_topc(A_6560) | ~r1_tarski('#skF_3'(u1_struct_0(A_6560), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), k2_zfmisc_1(u1_struct_0(A_6560), u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_142455, c_157163])).
% 33.15/21.46  tff(c_160905, plain, (![A_6701]: (v5_pre_topc('#skF_3'(u1_struct_0(A_6701), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), A_6701, g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_6701), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), A_6701, '#skF_5') | ~v1_funct_2('#skF_3'(u1_struct_0(A_6701), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), u1_struct_0(A_6701), '#skF_6') | ~l1_pre_topc(A_6701) | ~v2_pre_topc(A_6701) | ~r1_tarski('#skF_3'(u1_struct_0(A_6701), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_142321, c_142455, c_142455, c_98, c_96, c_142455, c_142455, c_142455, c_142455, c_157189])).
% 33.15/21.46  tff(c_160911, plain, (v5_pre_topc('#skF_3'('#skF_6', u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~v1_funct_2('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), '#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~r1_tarski('#skF_3'(u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_143043, c_160905])).
% 33.15/21.46  tff(c_160919, plain, (v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_144123, c_142665, c_143043, c_158460, c_142756, c_142665, c_143043, c_143043, c_142665, c_143043, c_142665, c_160911])).
% 33.15/21.46  tff(c_160920, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_142606, c_160919])).
% 33.15/21.46  tff(c_160924, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_160920])).
% 33.15/21.46  tff(c_160927, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_70, c_160924])).
% 33.15/21.46  tff(c_160931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_160927])).
% 33.15/21.46  tff(c_160932, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5')), inference(splitRight, [status(thm)], [c_160920])).
% 33.15/21.46  tff(c_160936, plain, (~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_146799, c_160932])).
% 33.15/21.46  tff(c_160940, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_79529, c_160936])).
% 33.15/21.46  tff(c_160941, plain, (v1_xboole_0(u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))))), inference(splitRight, [status(thm)], [c_142952])).
% 33.15/21.46  tff(c_160955, plain, (u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))='#skF_6'), inference(resolution, [status(thm)], [c_160941, c_142322])).
% 33.15/21.46  tff(c_160958, plain, (![D_6702, A_6703, B_6704]: (v5_pre_topc(D_6702, A_6703, g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704))) | ~v5_pre_topc(D_6702, A_6703, B_6704) | ~m1_subset_1(D_6702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6703), u1_struct_0(g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704)))))) | ~v1_funct_2(D_6702, u1_struct_0(A_6703), u1_struct_0(g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704)))) | ~m1_subset_1(D_6702, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6703), u1_struct_0(B_6704)))) | ~v1_funct_2(D_6702, u1_struct_0(A_6703), u1_struct_0(B_6704)) | ~v1_funct_1(D_6702) | ~l1_pre_topc(B_6704) | ~v2_pre_topc(B_6704) | ~l1_pre_topc(A_6703) | ~v2_pre_topc(A_6703))), inference(cnfTransformation, [status(thm)], [f_210])).
% 33.15/21.46  tff(c_162883, plain, (![A_6852, A_6853, B_6854]: (v5_pre_topc(A_6852, A_6853, g1_pre_topc(u1_struct_0(B_6854), u1_pre_topc(B_6854))) | ~v5_pre_topc(A_6852, A_6853, B_6854) | ~v1_funct_2(A_6852, u1_struct_0(A_6853), u1_struct_0(g1_pre_topc(u1_struct_0(B_6854), u1_pre_topc(B_6854)))) | ~m1_subset_1(A_6852, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6853), u1_struct_0(B_6854)))) | ~v1_funct_2(A_6852, u1_struct_0(A_6853), u1_struct_0(B_6854)) | ~v1_funct_1(A_6852) | ~l1_pre_topc(B_6854) | ~v2_pre_topc(B_6854) | ~l1_pre_topc(A_6853) | ~v2_pre_topc(A_6853) | ~r1_tarski(A_6852, k2_zfmisc_1(u1_struct_0(A_6853), u1_struct_0(g1_pre_topc(u1_struct_0(B_6854), u1_pre_topc(B_6854))))))), inference(resolution, [status(thm)], [c_24, c_160958])).
% 33.15/21.46  tff(c_162911, plain, (![A_6852, A_6853]: (v5_pre_topc(A_6852, A_6853, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc(A_6852, A_6853, '#skF_5') | ~v1_funct_2(A_6852, u1_struct_0(A_6853), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))) | ~m1_subset_1(A_6852, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6853), u1_struct_0('#skF_5')))) | ~v1_funct_2(A_6852, u1_struct_0(A_6853), u1_struct_0('#skF_5')) | ~v1_funct_1(A_6852) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_6853) | ~v2_pre_topc(A_6853) | ~r1_tarski(A_6852, k2_zfmisc_1(u1_struct_0(A_6853), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))))))), inference(superposition, [status(thm), theory('equality')], [c_142455, c_162883])).
% 33.15/21.46  tff(c_164133, plain, (![A_6899, A_6900]: (v5_pre_topc(A_6899, A_6900, g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~v5_pre_topc(A_6899, A_6900, '#skF_5') | ~m1_subset_1(A_6899, k1_zfmisc_1('#skF_6')) | ~v1_funct_2(A_6899, u1_struct_0(A_6900), '#skF_6') | ~v1_funct_1(A_6899) | ~l1_pre_topc(A_6900) | ~v2_pre_topc(A_6900) | ~r1_tarski(A_6899, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_142321, c_160955, c_98, c_96, c_142455, c_142321, c_142455, c_160955, c_142455, c_142455, c_162911])).
% 33.15/21.46  tff(c_164140, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))), '#skF_6') | ~v1_funct_1('#skF_6') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_164133, c_142606])).
% 33.15/21.46  tff(c_164146, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_94, c_142704, c_142470, c_164140])).
% 33.15/21.46  tff(c_164476, plain, (~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_164146])).
% 33.15/21.46  tff(c_164479, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_70, c_164476])).
% 33.15/21.46  tff(c_164483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_164479])).
% 33.15/21.46  tff(c_164485, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitRight, [status(thm)], [c_164146])).
% 33.15/21.46  tff(c_160968, plain, (![A_6703, B_6704]: (v5_pre_topc('#skF_3'(u1_struct_0(A_6703), u1_struct_0(g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704)))), A_6703, g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_6703), u1_struct_0(g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704)))), A_6703, B_6704) | ~v1_funct_2('#skF_3'(u1_struct_0(A_6703), u1_struct_0(g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704)))), u1_struct_0(A_6703), u1_struct_0(g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704)))) | ~m1_subset_1('#skF_3'(u1_struct_0(A_6703), u1_struct_0(g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6703), u1_struct_0(B_6704)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_6703), u1_struct_0(g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704)))), u1_struct_0(A_6703), u1_struct_0(B_6704)) | ~v1_funct_1('#skF_3'(u1_struct_0(A_6703), u1_struct_0(g1_pre_topc(u1_struct_0(B_6704), u1_pre_topc(B_6704))))) | ~l1_pre_topc(B_6704) | ~v2_pre_topc(B_6704) | ~l1_pre_topc(A_6703) | ~v2_pre_topc(A_6703))), inference(resolution, [status(thm)], [c_62, c_160958])).
% 33.15/21.46  tff(c_165271, plain, (![A_6974, B_6975]: (v5_pre_topc('#skF_3'(u1_struct_0(A_6974), u1_struct_0(g1_pre_topc(u1_struct_0(B_6975), u1_pre_topc(B_6975)))), A_6974, g1_pre_topc(u1_struct_0(B_6975), u1_pre_topc(B_6975))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_6974), u1_struct_0(g1_pre_topc(u1_struct_0(B_6975), u1_pre_topc(B_6975)))), A_6974, B_6975) | ~m1_subset_1('#skF_3'(u1_struct_0(A_6974), u1_struct_0(g1_pre_topc(u1_struct_0(B_6975), u1_pre_topc(B_6975)))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6974), u1_struct_0(B_6975)))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_6974), u1_struct_0(g1_pre_topc(u1_struct_0(B_6975), u1_pre_topc(B_6975)))), u1_struct_0(A_6974), u1_struct_0(B_6975)) | ~l1_pre_topc(B_6975) | ~v2_pre_topc(B_6975) | ~l1_pre_topc(A_6974) | ~v2_pre_topc(A_6974))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_160968])).
% 33.15/21.46  tff(c_165283, plain, (![A_6974]: (v5_pre_topc('#skF_3'(u1_struct_0(A_6974), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), A_6974, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_3'(u1_struct_0(A_6974), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), A_6974, '#skF_5') | ~m1_subset_1('#skF_3'(u1_struct_0(A_6974), u1_struct_0(g1_pre_topc('#skF_6', u1_pre_topc('#skF_5')))), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_6974), u1_struct_0('#skF_5')))) | ~v1_funct_2('#skF_3'(u1_struct_0(A_6974), u1_struct_0(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5')))), u1_struct_0(A_6974), u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | ~l1_pre_topc(A_6974) | ~v2_pre_topc(A_6974))), inference(superposition, [status(thm), theory('equality')], [c_142455, c_165271])).
% 33.15/21.46  tff(c_165526, plain, (![A_6984]: (v5_pre_topc('#skF_6', A_6984, g1_pre_topc('#skF_6', u1_pre_topc('#skF_5'))) | ~v5_pre_topc('#skF_6', A_6984, '#skF_5') | ~l1_pre_topc(A_6984) | ~v2_pre_topc(A_6984))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_142704, c_142455, c_142649, c_160955, c_142455, c_142470, c_142321, c_142455, c_142649, c_160955, c_142649, c_160955, c_142455, c_142455, c_142649, c_160955, c_142455, c_165283])).
% 33.15/21.46  tff(c_165536, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(resolution, [status(thm)], [c_165526, c_142606])).
% 33.15/21.46  tff(c_165543, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_164485, c_165536])).
% 33.15/21.46  tff(c_166631, plain, (~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')))), inference(splitLeft, [status(thm)], [c_165543])).
% 33.15/21.46  tff(c_166634, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_330, c_166631])).
% 33.15/21.46  tff(c_166641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_166634])).
% 33.15/21.46  tff(c_166642, plain, (~v5_pre_topc('#skF_6', g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')), '#skF_5')), inference(splitRight, [status(thm)], [c_165543])).
% 33.15/21.46  tff(c_173145, plain, (~v5_pre_topc('#skF_6', '#skF_4', '#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_173142, c_166642])).
% 33.15/21.46  tff(c_173155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_79529, c_173145])).
% 33.15/21.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.15/21.46  
% 33.15/21.46  Inference rules
% 33.15/21.46  ----------------------
% 33.15/21.46  #Ref     : 0
% 33.15/21.46  #Sup     : 40296
% 33.15/21.46  #Fact    : 0
% 33.15/21.46  #Define  : 0
% 33.15/21.46  #Split   : 109
% 33.15/21.46  #Chain   : 0
% 33.15/21.46  #Close   : 0
% 33.15/21.46  
% 33.15/21.46  Ordering : KBO
% 33.15/21.46  
% 33.15/21.46  Simplification rules
% 33.15/21.46  ----------------------
% 33.15/21.46  #Subsume      : 10859
% 33.15/21.46  #Demod        : 76307
% 33.15/21.46  #Tautology    : 23446
% 33.15/21.46  #SimpNegUnit  : 145
% 33.15/21.46  #BackRed      : 379
% 33.15/21.46  
% 33.15/21.46  #Partial instantiations: 0
% 33.15/21.46  #Strategies tried      : 1
% 33.15/21.46  
% 33.15/21.46  Timing (in seconds)
% 33.15/21.46  ----------------------
% 33.15/21.47  Preprocessing        : 0.40
% 33.15/21.47  Parsing              : 0.21
% 33.15/21.47  CNF conversion       : 0.03
% 33.15/21.47  Main loop            : 20.15
% 33.15/21.47  Inferencing          : 4.69
% 33.15/21.47  Reduction            : 8.70
% 33.15/21.47  Demodulation         : 7.06
% 33.15/21.47  BG Simplification    : 0.34
% 33.15/21.47  Subsumption          : 5.63
% 33.15/21.47  Abstraction          : 0.59
% 33.15/21.47  MUC search           : 0.00
% 33.15/21.47  Cooper               : 0.00
% 33.15/21.47  Total                : 20.73
% 33.15/21.47  Index Insertion      : 0.00
% 33.15/21.47  Index Deletion       : 0.00
% 33.15/21.47  Index Matching       : 0.00
% 33.15/21.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
