%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:51 EST 2020

% Result     : Theorem 8.41s
% Output     : CNFRefutation 8.41s
% Verified   : 
% Statistics : Number of formulae       :  141 (1961 expanded)
%              Number of leaves         :   50 ( 741 expanded)
%              Depth                    :   22
%              Number of atoms          :  337 (9294 expanded)
%              Number of equality atoms :   30 ( 675 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(r1_funct_2,type,(
    r1_funct_2: ( $i * $i * $i * $i * $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_229,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(B),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
                   => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                     => r1_funct_2(u1_struct_0(B),u1_struct_0(A),u1_struct_0(C),u1_struct_0(A),D,k2_tmap_1(B,A,D,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_182,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_178,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( ( v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ( B = g1_pre_topc(u1_struct_0(C),u1_pre_topc(C))
               => ( m1_pre_topc(B,A)
                <=> m1_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_196,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v1_xboole_0(B)
        & ~ v1_xboole_0(D)
        & v1_funct_1(E)
        & v1_funct_2(E,A,B)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & v1_funct_2(F,C,D)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( r1_funct_2(A,B,C,D,E,F)
      <=> E = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_160,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_26,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_150,plain,(
    ! [A_105] :
      ( m1_subset_1(u1_pre_topc(A_105),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105))))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( l1_pre_topc(g1_pre_topc(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(k1_zfmisc_1(A_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_163,plain,(
    ! [A_106] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_106),u1_pre_topc(A_106)))
      | ~ l1_pre_topc(A_106) ) ),
    inference(resolution,[status(thm)],[c_150,c_22])).

tff(c_166,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_163])).

tff(c_168,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_166])).

tff(c_87,plain,(
    ! [B_85,A_86] :
      ( l1_pre_topc(B_85)
      | ~ m1_pre_topc(B_85,A_86)
      | ~ l1_pre_topc(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_93,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_87])).

tff(c_97,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_93])).

tff(c_50,plain,(
    ! [A_60] :
      ( m1_pre_topc(A_60,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_182,plain,(
    ! [B_110,A_111] :
      ( m1_pre_topc(B_110,A_111)
      | ~ m1_pre_topc(B_110,g1_pre_topc(u1_struct_0(A_111),u1_pre_topc(A_111)))
      | ~ l1_pre_topc(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_192,plain,(
    ! [A_111] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(A_111),u1_pre_topc(A_111)),A_111)
      | ~ l1_pre_topc(A_111)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_111),u1_pre_topc(A_111))) ) ),
    inference(resolution,[status(thm)],[c_50,c_182])).

tff(c_169,plain,(
    ! [A_107] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_107),u1_pre_topc(A_107)))
      | ~ l1_pre_topc(A_107)
      | ~ v2_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_172,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_169])).

tff(c_174,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_172])).

tff(c_850,plain,(
    ! [C_144,A_145] :
      ( m1_pre_topc(C_144,A_145)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_144),u1_pre_topc(C_144)),A_145)
      | ~ l1_pre_topc(C_144)
      | ~ v2_pre_topc(C_144)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_144),u1_pre_topc(C_144)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_144),u1_pre_topc(C_144)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_874,plain,(
    ! [A_145] :
      ( m1_pre_topc('#skF_2',A_145)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_145)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_850])).

tff(c_921,plain,(
    ! [A_147] :
      ( m1_pre_topc('#skF_2',A_147)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_147)
      | ~ l1_pre_topc(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_58,c_168,c_58,c_72,c_70,c_874])).

tff(c_938,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_192,c_921])).

tff(c_958,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_97,c_938])).

tff(c_348,plain,(
    ! [B_124,C_125,A_126] :
      ( r1_tarski(u1_struct_0(B_124),u1_struct_0(C_125))
      | ~ m1_pre_topc(B_124,C_125)
      | ~ m1_pre_topc(C_125,A_126)
      | ~ m1_pre_topc(B_124,A_126)
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_361,plain,(
    ! [B_124,A_60] :
      ( r1_tarski(u1_struct_0(B_124),u1_struct_0(A_60))
      | ~ m1_pre_topc(B_124,A_60)
      | ~ v2_pre_topc(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_50,c_348])).

tff(c_139,plain,(
    ! [B_103,A_104] :
      ( v2_pre_topc(B_103)
      | ~ m1_pre_topc(B_103,A_104)
      | ~ l1_pre_topc(A_104)
      | ~ v2_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_145,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_139])).

tff(c_149,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_145])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_254,plain,(
    ! [B_119,C_120,A_121] :
      ( m1_pre_topc(B_119,C_120)
      | ~ r1_tarski(u1_struct_0(B_119),u1_struct_0(C_120))
      | ~ m1_pre_topc(C_120,A_121)
      | ~ m1_pre_topc(B_119,A_121)
      | ~ l1_pre_topc(A_121)
      | ~ v2_pre_topc(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_365,plain,(
    ! [B_127,A_128] :
      ( m1_pre_topc(B_127,B_127)
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128)
      | ~ v2_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_373,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_365])).

tff(c_381,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_373])).

tff(c_52,plain,(
    ! [B_65,C_67,A_61] :
      ( r1_tarski(u1_struct_0(B_65),u1_struct_0(C_67))
      | ~ m1_pre_topc(B_65,C_67)
      | ~ m1_pre_topc(C_67,A_61)
      | ~ m1_pre_topc(B_65,A_61)
      | ~ l1_pre_topc(A_61)
      | ~ v2_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_385,plain,(
    ! [B_65] :
      ( r1_tarski(u1_struct_0(B_65),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_65,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_381,c_52])).

tff(c_404,plain,(
    ! [B_129] :
      ( r1_tarski(u1_struct_0(B_129),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_129,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_97,c_385])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_473,plain,(
    ! [B_132] :
      ( u1_struct_0(B_132) = u1_struct_0('#skF_3')
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(B_132))
      | ~ m1_pre_topc(B_132,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_404,c_2])).

tff(c_486,plain,(
    ! [A_60] :
      ( u1_struct_0(A_60) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_60,'#skF_3')
      | ~ m1_pre_topc('#skF_3',A_60)
      | ~ v2_pre_topc(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(resolution,[status(thm)],[c_361,c_473])).

tff(c_969,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_958,c_486])).

tff(c_985,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_66,c_969])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1034,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_62])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1033,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_60])).

tff(c_40,plain,(
    ! [B_33,C_34,F_37,A_32,D_35] :
      ( r1_funct_2(A_32,B_33,C_34,D_35,F_37,F_37)
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(C_34,D_35)))
      | ~ v1_funct_2(F_37,C_34,D_35)
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(F_37,A_32,B_33)
      | ~ v1_funct_1(F_37)
      | v1_xboole_0(D_35)
      | v1_xboole_0(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1138,plain,(
    ! [A_32,B_33] :
      ( r1_funct_2(A_32,B_33,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2('#skF_4',A_32,B_33)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_33) ) ),
    inference(resolution,[status(thm)],[c_1033,c_40])).

tff(c_1152,plain,(
    ! [A_32,B_33] :
      ( r1_funct_2(A_32,B_33,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2('#skF_4',A_32,B_33)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1034,c_1138])).

tff(c_3007,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1152])).

tff(c_32,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3010,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3007,c_32])).

tff(c_3013,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3010])).

tff(c_3016,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_3013])).

tff(c_3020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_3016])).

tff(c_3022,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1152])).

tff(c_6426,plain,(
    ! [A_249,B_250] :
      ( r1_funct_2(A_249,B_250,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_249,B_250)))
      | ~ v1_funct_2('#skF_4',A_249,B_250)
      | v1_xboole_0(B_250) ) ),
    inference(splitRight,[status(thm)],[c_1152])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_213,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k2_partfun1(A_113,B_114,C_115,D_116) = k7_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114)))
      | ~ v1_funct_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_215,plain,(
    ! [D_116] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_116) = k7_relat_1('#skF_4',D_116)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_213])).

tff(c_218,plain,(
    ! [D_116] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_116) = k7_relat_1('#skF_4',D_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_215])).

tff(c_1028,plain,(
    ! [D_116] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_116) = k7_relat_1('#skF_4',D_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_218])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1277,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( k2_partfun1(u1_struct_0(A_160),u1_struct_0(B_161),C_162,u1_struct_0(D_163)) = k2_tmap_1(A_160,B_161,C_162,D_163)
      | ~ m1_pre_topc(D_163,A_160)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_160),u1_struct_0(B_161))))
      | ~ v1_funct_2(C_162,u1_struct_0(A_160),u1_struct_0(B_161))
      | ~ v1_funct_1(C_162)
      | ~ l1_pre_topc(B_161)
      | ~ v2_pre_topc(B_161)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1281,plain,(
    ! [B_161,C_162,D_163] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_161),C_162,u1_struct_0(D_163)) = k2_tmap_1('#skF_2',B_161,C_162,D_163)
      | ~ m1_pre_topc(D_163,'#skF_2')
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_161))))
      | ~ v1_funct_2(C_162,u1_struct_0('#skF_2'),u1_struct_0(B_161))
      | ~ v1_funct_1(C_162)
      | ~ l1_pre_topc(B_161)
      | ~ v2_pre_topc(B_161)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_985,c_1277])).

tff(c_1293,plain,(
    ! [B_161,C_162,D_163] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_161),C_162,u1_struct_0(D_163)) = k2_tmap_1('#skF_2',B_161,C_162,D_163)
      | ~ m1_pre_topc(D_163,'#skF_2')
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_161))))
      | ~ v1_funct_2(C_162,u1_struct_0('#skF_3'),u1_struct_0(B_161))
      | ~ v1_funct_1(C_162)
      | ~ l1_pre_topc(B_161)
      | ~ v2_pre_topc(B_161)
      | v2_struct_0(B_161)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_985,c_985,c_1281])).

tff(c_1826,plain,(
    ! [B_173,C_174,D_175] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_173),C_174,u1_struct_0(D_175)) = k2_tmap_1('#skF_2',B_173,C_174,D_175)
      | ~ m1_pre_topc(D_175,'#skF_2')
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_173))))
      | ~ v1_funct_2(C_174,u1_struct_0('#skF_3'),u1_struct_0(B_173))
      | ~ v1_funct_1(C_174)
      | ~ l1_pre_topc(B_173)
      | ~ v2_pre_topc(B_173)
      | v2_struct_0(B_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1293])).

tff(c_1830,plain,(
    ! [D_175] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_175)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_175)
      | ~ m1_pre_topc(D_175,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_1033,c_1826])).

tff(c_1839,plain,(
    ! [D_175] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_175)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_175)
      | ~ m1_pre_topc(D_175,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_1034,c_1028,c_1830])).

tff(c_1846,plain,(
    ! [D_176] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_176)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_176)
      | ~ m1_pre_topc(D_176,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1839])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_108,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_8])).

tff(c_111,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_108])).

tff(c_113,plain,(
    ! [C_93,A_94,B_95] :
      ( v4_relat_1(C_93,A_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_117,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_113])).

tff(c_123,plain,(
    ! [B_99,A_100] :
      ( k7_relat_1(B_99,A_100) = B_99
      | ~ v4_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_126,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_123])).

tff(c_129,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_126])).

tff(c_1031,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_129])).

tff(c_1855,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1846,c_1031])).

tff(c_1876,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1855])).

tff(c_56,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1029,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_56])).

tff(c_1886,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1876,c_1029])).

tff(c_6429,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6426,c_1886])).

tff(c_6434,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1033,c_6429])).

tff(c_6436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3022,c_6434])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.41/2.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/2.74  
% 8.41/2.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/2.74  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.41/2.74  
% 8.41/2.74  %Foreground sorts:
% 8.41/2.74  
% 8.41/2.74  
% 8.41/2.74  %Background operators:
% 8.41/2.74  
% 8.41/2.74  
% 8.41/2.74  %Foreground operators:
% 8.41/2.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.41/2.74  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.41/2.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.41/2.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.41/2.74  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.41/2.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.41/2.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.41/2.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.41/2.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.41/2.74  tff('#skF_2', type, '#skF_2': $i).
% 8.41/2.74  tff('#skF_3', type, '#skF_3': $i).
% 8.41/2.74  tff('#skF_1', type, '#skF_1': $i).
% 8.41/2.74  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.41/2.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.41/2.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.41/2.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.41/2.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.41/2.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.41/2.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.41/2.74  tff('#skF_4', type, '#skF_4': $i).
% 8.41/2.74  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 8.41/2.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.41/2.74  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.41/2.74  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.41/2.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.41/2.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.41/2.74  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.41/2.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.41/2.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.41/2.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.41/2.74  
% 8.41/2.76  tff(f_229, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 8.41/2.76  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.41/2.76  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 8.41/2.76  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 8.41/2.76  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.41/2.76  tff(f_182, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.41/2.76  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 8.41/2.76  tff(f_104, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 8.41/2.76  tff(f_178, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 8.41/2.76  tff(f_196, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 8.41/2.76  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 8.41/2.76  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.41/2.76  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 8.41/2.76  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 8.41/2.76  tff(f_58, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.41/2.76  tff(f_160, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 8.41/2.76  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.41/2.76  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.41/2.76  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.41/2.76  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 8.41/2.76  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_26, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.41/2.76  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_150, plain, (![A_105]: (m1_subset_1(u1_pre_topc(A_105), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_105)))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.41/2.76  tff(c_22, plain, (![A_20, B_21]: (l1_pre_topc(g1_pre_topc(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(k1_zfmisc_1(A_20))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.41/2.76  tff(c_163, plain, (![A_106]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_106), u1_pre_topc(A_106))) | ~l1_pre_topc(A_106))), inference(resolution, [status(thm)], [c_150, c_22])).
% 8.41/2.76  tff(c_166, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_163])).
% 8.41/2.76  tff(c_168, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_166])).
% 8.41/2.76  tff(c_87, plain, (![B_85, A_86]: (l1_pre_topc(B_85) | ~m1_pre_topc(B_85, A_86) | ~l1_pre_topc(A_86))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.41/2.76  tff(c_93, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_87])).
% 8.41/2.76  tff(c_97, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_93])).
% 8.41/2.76  tff(c_50, plain, (![A_60]: (m1_pre_topc(A_60, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_182])).
% 8.41/2.76  tff(c_182, plain, (![B_110, A_111]: (m1_pre_topc(B_110, A_111) | ~m1_pre_topc(B_110, g1_pre_topc(u1_struct_0(A_111), u1_pre_topc(A_111))) | ~l1_pre_topc(A_111))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.41/2.76  tff(c_192, plain, (![A_111]: (m1_pre_topc(g1_pre_topc(u1_struct_0(A_111), u1_pre_topc(A_111)), A_111) | ~l1_pre_topc(A_111) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_111), u1_pre_topc(A_111))))), inference(resolution, [status(thm)], [c_50, c_182])).
% 8.41/2.76  tff(c_169, plain, (![A_107]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_107), u1_pre_topc(A_107))) | ~l1_pre_topc(A_107) | ~v2_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.41/2.76  tff(c_172, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_58, c_169])).
% 8.41/2.76  tff(c_174, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_172])).
% 8.41/2.76  tff(c_850, plain, (![C_144, A_145]: (m1_pre_topc(C_144, A_145) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_144), u1_pre_topc(C_144)), A_145) | ~l1_pre_topc(C_144) | ~v2_pre_topc(C_144) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_144), u1_pre_topc(C_144))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_144), u1_pre_topc(C_144))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_178])).
% 8.41/2.76  tff(c_874, plain, (![A_145]: (m1_pre_topc('#skF_2', A_145) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_145) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_145))), inference(superposition, [status(thm), theory('equality')], [c_58, c_850])).
% 8.41/2.76  tff(c_921, plain, (![A_147]: (m1_pre_topc('#skF_2', A_147) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_147) | ~l1_pre_topc(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_58, c_168, c_58, c_72, c_70, c_874])).
% 8.41/2.76  tff(c_938, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_192, c_921])).
% 8.41/2.76  tff(c_958, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_97, c_938])).
% 8.41/2.76  tff(c_348, plain, (![B_124, C_125, A_126]: (r1_tarski(u1_struct_0(B_124), u1_struct_0(C_125)) | ~m1_pre_topc(B_124, C_125) | ~m1_pre_topc(C_125, A_126) | ~m1_pre_topc(B_124, A_126) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.41/2.76  tff(c_361, plain, (![B_124, A_60]: (r1_tarski(u1_struct_0(B_124), u1_struct_0(A_60)) | ~m1_pre_topc(B_124, A_60) | ~v2_pre_topc(A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_50, c_348])).
% 8.41/2.76  tff(c_139, plain, (![B_103, A_104]: (v2_pre_topc(B_103) | ~m1_pre_topc(B_103, A_104) | ~l1_pre_topc(A_104) | ~v2_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_67])).
% 8.41/2.76  tff(c_145, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_139])).
% 8.41/2.76  tff(c_149, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_145])).
% 8.41/2.76  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/2.76  tff(c_254, plain, (![B_119, C_120, A_121]: (m1_pre_topc(B_119, C_120) | ~r1_tarski(u1_struct_0(B_119), u1_struct_0(C_120)) | ~m1_pre_topc(C_120, A_121) | ~m1_pre_topc(B_119, A_121) | ~l1_pre_topc(A_121) | ~v2_pre_topc(A_121))), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.41/2.76  tff(c_365, plain, (![B_127, A_128]: (m1_pre_topc(B_127, B_127) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128) | ~v2_pre_topc(A_128))), inference(resolution, [status(thm)], [c_6, c_254])).
% 8.41/2.76  tff(c_373, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_365])).
% 8.41/2.76  tff(c_381, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_373])).
% 8.41/2.76  tff(c_52, plain, (![B_65, C_67, A_61]: (r1_tarski(u1_struct_0(B_65), u1_struct_0(C_67)) | ~m1_pre_topc(B_65, C_67) | ~m1_pre_topc(C_67, A_61) | ~m1_pre_topc(B_65, A_61) | ~l1_pre_topc(A_61) | ~v2_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.41/2.76  tff(c_385, plain, (![B_65]: (r1_tarski(u1_struct_0(B_65), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_65, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_381, c_52])).
% 8.41/2.76  tff(c_404, plain, (![B_129]: (r1_tarski(u1_struct_0(B_129), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_129, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_97, c_385])).
% 8.41/2.76  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.41/2.76  tff(c_473, plain, (![B_132]: (u1_struct_0(B_132)=u1_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(B_132)) | ~m1_pre_topc(B_132, '#skF_3'))), inference(resolution, [status(thm)], [c_404, c_2])).
% 8.41/2.76  tff(c_486, plain, (![A_60]: (u1_struct_0(A_60)=u1_struct_0('#skF_3') | ~m1_pre_topc(A_60, '#skF_3') | ~m1_pre_topc('#skF_3', A_60) | ~v2_pre_topc(A_60) | ~l1_pre_topc(A_60))), inference(resolution, [status(thm)], [c_361, c_473])).
% 8.41/2.76  tff(c_969, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_958, c_486])).
% 8.41/2.76  tff(c_985, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_66, c_969])).
% 8.41/2.76  tff(c_62, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_1034, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_62])).
% 8.41/2.76  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_1033, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_60])).
% 8.41/2.76  tff(c_40, plain, (![B_33, C_34, F_37, A_32, D_35]: (r1_funct_2(A_32, B_33, C_34, D_35, F_37, F_37) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(C_34, D_35))) | ~v1_funct_2(F_37, C_34, D_35) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(F_37, A_32, B_33) | ~v1_funct_1(F_37) | v1_xboole_0(D_35) | v1_xboole_0(B_33))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.41/2.76  tff(c_1138, plain, (![A_32, B_33]: (r1_funct_2(A_32, B_33, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2('#skF_4', A_32, B_33) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_33))), inference(resolution, [status(thm)], [c_1033, c_40])).
% 8.41/2.76  tff(c_1152, plain, (![A_32, B_33]: (r1_funct_2(A_32, B_33, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2('#skF_4', A_32, B_33) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_33))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1034, c_1138])).
% 8.41/2.76  tff(c_3007, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1152])).
% 8.41/2.76  tff(c_32, plain, (![A_27]: (~v1_xboole_0(u1_struct_0(A_27)) | ~l1_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_96])).
% 8.41/2.76  tff(c_3010, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_3007, c_32])).
% 8.41/2.76  tff(c_3013, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_80, c_3010])).
% 8.41/2.76  tff(c_3016, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_3013])).
% 8.41/2.76  tff(c_3020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_3016])).
% 8.41/2.76  tff(c_3022, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1152])).
% 8.41/2.76  tff(c_6426, plain, (![A_249, B_250]: (r1_funct_2(A_249, B_250, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_249, B_250))) | ~v1_funct_2('#skF_4', A_249, B_250) | v1_xboole_0(B_250))), inference(splitRight, [status(thm)], [c_1152])).
% 8.41/2.76  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_213, plain, (![A_113, B_114, C_115, D_116]: (k2_partfun1(A_113, B_114, C_115, D_116)=k7_relat_1(C_115, D_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_113, B_114))) | ~v1_funct_1(C_115))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.41/2.76  tff(c_215, plain, (![D_116]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_116)=k7_relat_1('#skF_4', D_116) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_213])).
% 8.41/2.76  tff(c_218, plain, (![D_116]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_116)=k7_relat_1('#skF_4', D_116))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_215])).
% 8.41/2.76  tff(c_1028, plain, (![D_116]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_116)=k7_relat_1('#skF_4', D_116))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_218])).
% 8.41/2.76  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_1277, plain, (![A_160, B_161, C_162, D_163]: (k2_partfun1(u1_struct_0(A_160), u1_struct_0(B_161), C_162, u1_struct_0(D_163))=k2_tmap_1(A_160, B_161, C_162, D_163) | ~m1_pre_topc(D_163, A_160) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_160), u1_struct_0(B_161)))) | ~v1_funct_2(C_162, u1_struct_0(A_160), u1_struct_0(B_161)) | ~v1_funct_1(C_162) | ~l1_pre_topc(B_161) | ~v2_pre_topc(B_161) | v2_struct_0(B_161) | ~l1_pre_topc(A_160) | ~v2_pre_topc(A_160) | v2_struct_0(A_160))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.41/2.76  tff(c_1281, plain, (![B_161, C_162, D_163]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_161), C_162, u1_struct_0(D_163))=k2_tmap_1('#skF_2', B_161, C_162, D_163) | ~m1_pre_topc(D_163, '#skF_2') | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_161)))) | ~v1_funct_2(C_162, u1_struct_0('#skF_2'), u1_struct_0(B_161)) | ~v1_funct_1(C_162) | ~l1_pre_topc(B_161) | ~v2_pre_topc(B_161) | v2_struct_0(B_161) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_985, c_1277])).
% 8.41/2.76  tff(c_1293, plain, (![B_161, C_162, D_163]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_161), C_162, u1_struct_0(D_163))=k2_tmap_1('#skF_2', B_161, C_162, D_163) | ~m1_pre_topc(D_163, '#skF_2') | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_161)))) | ~v1_funct_2(C_162, u1_struct_0('#skF_3'), u1_struct_0(B_161)) | ~v1_funct_1(C_162) | ~l1_pre_topc(B_161) | ~v2_pre_topc(B_161) | v2_struct_0(B_161) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_985, c_985, c_1281])).
% 8.41/2.76  tff(c_1826, plain, (![B_173, C_174, D_175]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_173), C_174, u1_struct_0(D_175))=k2_tmap_1('#skF_2', B_173, C_174, D_175) | ~m1_pre_topc(D_175, '#skF_2') | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_173)))) | ~v1_funct_2(C_174, u1_struct_0('#skF_3'), u1_struct_0(B_173)) | ~v1_funct_1(C_174) | ~l1_pre_topc(B_173) | ~v2_pre_topc(B_173) | v2_struct_0(B_173))), inference(negUnitSimplification, [status(thm)], [c_74, c_1293])).
% 8.41/2.76  tff(c_1830, plain, (![D_175]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_175))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_175) | ~m1_pre_topc(D_175, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1033, c_1826])).
% 8.41/2.76  tff(c_1839, plain, (![D_175]: (k7_relat_1('#skF_4', u1_struct_0(D_175))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_175) | ~m1_pre_topc(D_175, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_1034, c_1028, c_1830])).
% 8.41/2.76  tff(c_1846, plain, (![D_176]: (k7_relat_1('#skF_4', u1_struct_0(D_176))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_176) | ~m1_pre_topc(D_176, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_80, c_1839])).
% 8.41/2.76  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.41/2.76  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.41/2.76  tff(c_108, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_60, c_8])).
% 8.41/2.76  tff(c_111, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_108])).
% 8.41/2.76  tff(c_113, plain, (![C_93, A_94, B_95]: (v4_relat_1(C_93, A_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.41/2.76  tff(c_117, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_113])).
% 8.41/2.76  tff(c_123, plain, (![B_99, A_100]: (k7_relat_1(B_99, A_100)=B_99 | ~v4_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_46])).
% 8.41/2.76  tff(c_126, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_117, c_123])).
% 8.41/2.76  tff(c_129, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_111, c_126])).
% 8.41/2.76  tff(c_1031, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_985, c_129])).
% 8.41/2.76  tff(c_1855, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1846, c_1031])).
% 8.41/2.76  tff(c_1876, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1855])).
% 8.41/2.76  tff(c_56, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 8.41/2.76  tff(c_1029, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_985, c_56])).
% 8.41/2.76  tff(c_1886, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1876, c_1029])).
% 8.41/2.76  tff(c_6429, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_6426, c_1886])).
% 8.41/2.76  tff(c_6434, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1034, c_1033, c_6429])).
% 8.41/2.76  tff(c_6436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3022, c_6434])).
% 8.41/2.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.41/2.76  
% 8.41/2.76  Inference rules
% 8.41/2.76  ----------------------
% 8.41/2.76  #Ref     : 0
% 8.41/2.76  #Sup     : 1207
% 8.41/2.76  #Fact    : 0
% 8.41/2.76  #Define  : 0
% 8.41/2.76  #Split   : 7
% 8.41/2.76  #Chain   : 0
% 8.41/2.76  #Close   : 0
% 8.41/2.76  
% 8.41/2.76  Ordering : KBO
% 8.41/2.76  
% 8.41/2.76  Simplification rules
% 8.41/2.76  ----------------------
% 8.41/2.76  #Subsume      : 180
% 8.41/2.76  #Demod        : 4911
% 8.41/2.76  #Tautology    : 682
% 8.41/2.76  #SimpNegUnit  : 10
% 8.41/2.76  #BackRed      : 15
% 8.41/2.76  
% 8.41/2.76  #Partial instantiations: 0
% 8.41/2.76  #Strategies tried      : 1
% 8.41/2.76  
% 8.41/2.76  Timing (in seconds)
% 8.41/2.76  ----------------------
% 8.41/2.77  Preprocessing        : 0.41
% 8.41/2.77  Parsing              : 0.22
% 8.41/2.77  CNF conversion       : 0.03
% 8.41/2.77  Main loop            : 1.50
% 8.41/2.77  Inferencing          : 0.39
% 8.41/2.77  Reduction            : 0.72
% 8.41/2.77  Demodulation         : 0.59
% 8.41/2.77  BG Simplification    : 0.04
% 8.41/2.77  Subsumption          : 0.28
% 8.41/2.77  Abstraction          : 0.07
% 8.41/2.77  MUC search           : 0.00
% 8.41/2.77  Cooper               : 0.00
% 8.41/2.77  Total                : 1.96
% 8.41/2.77  Index Insertion      : 0.00
% 8.41/2.77  Index Deletion       : 0.00
% 8.41/2.77  Index Matching       : 0.00
% 8.41/2.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
