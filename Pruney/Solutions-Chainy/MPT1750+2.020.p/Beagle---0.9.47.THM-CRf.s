%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:54 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :  125 (1414 expanded)
%              Number of leaves         :   45 ( 516 expanded)
%              Depth                    :   23
%              Number of atoms          :  298 (6872 expanded)
%              Number of equality atoms :   30 ( 467 expanded)
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

tff(f_224,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_177,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_191,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_128,axiom,(
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

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_155,axiom,(
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

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_50,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_86,plain,(
    ! [B_81,A_82] :
      ( l1_pre_topc(B_81)
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_92,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_86])).

tff(c_96,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_92])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_188,plain,(
    ! [A_107,B_108] :
      ( m1_pre_topc(A_107,g1_pre_topc(u1_struct_0(B_108),u1_pre_topc(B_108)))
      | ~ m1_pre_topc(A_107,B_108)
      | ~ l1_pre_topc(B_108)
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_201,plain,(
    ! [A_107] :
      ( m1_pre_topc(A_107,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_107,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_188])).

tff(c_216,plain,(
    ! [A_110] :
      ( m1_pre_topc(A_110,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_110,'#skF_2')
      | ~ l1_pre_topc(A_110) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_201])).

tff(c_34,plain,(
    ! [B_26,A_24] :
      ( m1_pre_topc(B_26,A_24)
      | ~ m1_pre_topc(B_26,g1_pre_topc(u1_struct_0(A_24),u1_pre_topc(A_24)))
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_222,plain,(
    ! [A_110] :
      ( m1_pre_topc(A_110,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_110,'#skF_2')
      | ~ l1_pre_topc(A_110) ) ),
    inference(resolution,[status(thm)],[c_216,c_34])).

tff(c_233,plain,(
    ! [A_111] :
      ( m1_pre_topc(A_111,'#skF_3')
      | ~ m1_pre_topc(A_111,'#skF_2')
      | ~ l1_pre_topc(A_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_222])).

tff(c_243,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_233])).

tff(c_253,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_243])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_163,plain,(
    ! [B_104,A_105] :
      ( m1_pre_topc(B_104,A_105)
      | ~ m1_pre_topc(B_104,g1_pre_topc(u1_struct_0(A_105),u1_pre_topc(A_105)))
      | ~ l1_pre_topc(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_166,plain,(
    ! [B_104] :
      ( m1_pre_topc(B_104,'#skF_2')
      | ~ m1_pre_topc(B_104,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_163])).

tff(c_172,plain,(
    ! [B_104] :
      ( m1_pre_topc(B_104,'#skF_2')
      | ~ m1_pre_topc(B_104,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_166])).

tff(c_192,plain,(
    ! [A_107] :
      ( m1_pre_topc(A_107,'#skF_2')
      | ~ m1_pre_topc(A_107,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_188,c_172])).

tff(c_204,plain,(
    ! [A_107] :
      ( m1_pre_topc(A_107,'#skF_2')
      | ~ m1_pre_topc(A_107,'#skF_3')
      | ~ l1_pre_topc(A_107) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_192])).

tff(c_319,plain,(
    ! [B_118,C_119,A_120] :
      ( r1_tarski(u1_struct_0(B_118),u1_struct_0(C_119))
      | ~ m1_pre_topc(B_118,C_119)
      | ~ m1_pre_topc(C_119,A_120)
      | ~ m1_pre_topc(B_118,A_120)
      | ~ l1_pre_topc(A_120)
      | ~ v2_pre_topc(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_331,plain,(
    ! [B_118,A_107] :
      ( r1_tarski(u1_struct_0(B_118),u1_struct_0(A_107))
      | ~ m1_pre_topc(B_118,A_107)
      | ~ m1_pre_topc(B_118,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_pre_topc(A_107,'#skF_3')
      | ~ l1_pre_topc(A_107) ) ),
    inference(resolution,[status(thm)],[c_204,c_319])).

tff(c_493,plain,(
    ! [B_132,A_133] :
      ( r1_tarski(u1_struct_0(B_132),u1_struct_0(A_133))
      | ~ m1_pre_topc(B_132,A_133)
      | ~ m1_pre_topc(B_132,'#skF_2')
      | ~ m1_pre_topc(A_133,'#skF_3')
      | ~ l1_pre_topc(A_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_331])).

tff(c_339,plain,(
    ! [B_118] :
      ( r1_tarski(u1_struct_0(B_118),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_118,'#skF_3')
      | ~ m1_pre_topc(B_118,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_319])).

tff(c_365,plain,(
    ! [B_121] :
      ( r1_tarski(u1_struct_0(B_121),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_121,'#skF_3')
      | ~ m1_pre_topc(B_121,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_339])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_368,plain,(
    ! [B_121] :
      ( u1_struct_0(B_121) = u1_struct_0('#skF_3')
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(B_121))
      | ~ m1_pre_topc(B_121,'#skF_3')
      | ~ m1_pre_topc(B_121,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_365,c_2])).

tff(c_500,plain,(
    ! [A_133] :
      ( u1_struct_0(A_133) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_133,'#skF_2')
      | ~ m1_pre_topc('#skF_3',A_133)
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | ~ m1_pre_topc(A_133,'#skF_3')
      | ~ l1_pre_topc(A_133) ) ),
    inference(resolution,[status(thm)],[c_493,c_368])).

tff(c_511,plain,(
    ! [A_134] :
      ( u1_struct_0(A_134) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_134,'#skF_2')
      | ~ m1_pre_topc('#skF_3',A_134)
      | ~ m1_pre_topc(A_134,'#skF_3')
      | ~ l1_pre_topc(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_500])).

tff(c_521,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_511])).

tff(c_533,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_253,c_66,c_521])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_544,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_62])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_543,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_60])).

tff(c_817,plain,(
    ! [C_141,A_144,D_145,B_142,F_143] :
      ( r1_funct_2(A_144,B_142,C_141,D_145,F_143,F_143)
      | ~ m1_subset_1(F_143,k1_zfmisc_1(k2_zfmisc_1(C_141,D_145)))
      | ~ v1_funct_2(F_143,C_141,D_145)
      | ~ m1_subset_1(F_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_142)))
      | ~ v1_funct_2(F_143,A_144,B_142)
      | ~ v1_funct_1(F_143)
      | v1_xboole_0(D_145)
      | v1_xboole_0(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_819,plain,(
    ! [A_144,B_142] :
      ( r1_funct_2(A_144,B_142,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_144,B_142)))
      | ~ v1_funct_2('#skF_4',A_144,B_142)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_142) ) ),
    inference(resolution,[status(thm)],[c_543,c_817])).

tff(c_822,plain,(
    ! [A_144,B_142] :
      ( r1_funct_2(A_144,B_142,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_144,B_142)))
      | ~ v1_funct_2('#skF_4',A_144,B_142)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_544,c_819])).

tff(c_1887,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_822])).

tff(c_28,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1890,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1887,c_28])).

tff(c_1893,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1890])).

tff(c_1896,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1893])).

tff(c_1900,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1896])).

tff(c_1902,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_822])).

tff(c_4724,plain,(
    ! [A_233,B_234] :
      ( r1_funct_2(A_233,B_234,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_2('#skF_4',A_233,B_234)
      | v1_xboole_0(B_234) ) ),
    inference(splitRight,[status(thm)],[c_822])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_257,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k2_partfun1(A_112,B_113,C_114,D_115) = k7_relat_1(C_114,D_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ v1_funct_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_259,plain,(
    ! [D_115] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_115) = k7_relat_1('#skF_4',D_115)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_257])).

tff(c_262,plain,(
    ! [D_115] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_115) = k7_relat_1('#skF_4',D_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_259])).

tff(c_538,plain,(
    ! [D_115] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_115) = k7_relat_1('#skF_4',D_115) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_262])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_1114,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( k2_partfun1(u1_struct_0(A_157),u1_struct_0(B_158),C_159,u1_struct_0(D_160)) = k2_tmap_1(A_157,B_158,C_159,D_160)
      | ~ m1_pre_topc(D_160,A_157)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_157),u1_struct_0(B_158))))
      | ~ v1_funct_2(C_159,u1_struct_0(A_157),u1_struct_0(B_158))
      | ~ v1_funct_1(C_159)
      | ~ l1_pre_topc(B_158)
      | ~ v2_pre_topc(B_158)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1122,plain,(
    ! [B_158,C_159,D_160] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_158),C_159,u1_struct_0(D_160)) = k2_tmap_1('#skF_2',B_158,C_159,D_160)
      | ~ m1_pre_topc(D_160,'#skF_2')
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_158))))
      | ~ v1_funct_2(C_159,u1_struct_0('#skF_2'),u1_struct_0(B_158))
      | ~ v1_funct_1(C_159)
      | ~ l1_pre_topc(B_158)
      | ~ v2_pre_topc(B_158)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_533,c_1114])).

tff(c_1134,plain,(
    ! [B_158,C_159,D_160] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_158),C_159,u1_struct_0(D_160)) = k2_tmap_1('#skF_2',B_158,C_159,D_160)
      | ~ m1_pre_topc(D_160,'#skF_2')
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_158))))
      | ~ v1_funct_2(C_159,u1_struct_0('#skF_3'),u1_struct_0(B_158))
      | ~ v1_funct_1(C_159)
      | ~ l1_pre_topc(B_158)
      | ~ v2_pre_topc(B_158)
      | v2_struct_0(B_158)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_533,c_533,c_1122])).

tff(c_1203,plain,(
    ! [B_163,C_164,D_165] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_163),C_164,u1_struct_0(D_165)) = k2_tmap_1('#skF_2',B_163,C_164,D_165)
      | ~ m1_pre_topc(D_165,'#skF_2')
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_163))))
      | ~ v1_funct_2(C_164,u1_struct_0('#skF_3'),u1_struct_0(B_163))
      | ~ v1_funct_1(C_164)
      | ~ l1_pre_topc(B_163)
      | ~ v2_pre_topc(B_163)
      | v2_struct_0(B_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1134])).

tff(c_1207,plain,(
    ! [D_165] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_165)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_165)
      | ~ m1_pre_topc(D_165,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_543,c_1203])).

tff(c_1214,plain,(
    ! [D_165] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_165)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_165)
      | ~ m1_pre_topc(D_165,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_544,c_538,c_1207])).

tff(c_1219,plain,(
    ! [D_166] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_166)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_166)
      | ~ m1_pre_topc(D_166,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1214])).

tff(c_104,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_108,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_104])).

tff(c_131,plain,(
    ! [C_97,A_98,B_99] :
      ( v4_relat_1(C_97,A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_135,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_131])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k7_relat_1(B_4,A_3) = B_4
      | ~ v4_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_138,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_135,c_8])).

tff(c_141,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_138])).

tff(c_539,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_141])).

tff(c_1225,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1219,c_539])).

tff(c_1240,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1225])).

tff(c_56,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_541,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_56])).

tff(c_1247,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1240,c_541])).

tff(c_4727,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_4724,c_1247])).

tff(c_4732,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_543,c_4727])).

tff(c_4734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1902,c_4732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.19  
% 6.21/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.19  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.21/2.19  
% 6.21/2.19  %Foreground sorts:
% 6.21/2.19  
% 6.21/2.19  
% 6.21/2.19  %Background operators:
% 6.21/2.19  
% 6.21/2.19  
% 6.21/2.19  %Foreground operators:
% 6.21/2.19  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.21/2.19  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.21/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.21/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.19  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.21/2.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.21/2.19  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.21/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.21/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.21/2.19  tff('#skF_2', type, '#skF_2': $i).
% 6.21/2.19  tff('#skF_3', type, '#skF_3': $i).
% 6.21/2.19  tff('#skF_1', type, '#skF_1': $i).
% 6.21/2.19  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.21/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.21/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.21/2.19  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.21/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.21/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.21/2.19  tff('#skF_4', type, '#skF_4': $i).
% 6.21/2.19  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 6.21/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.19  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.21/2.19  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.21/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.21/2.19  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.21/2.19  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.21/2.19  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.21/2.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.21/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.21/2.19  
% 6.21/2.21  tff(f_224, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 6.21/2.21  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.21/2.21  tff(f_177, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.21/2.21  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.21/2.21  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 6.21/2.21  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 6.21/2.21  tff(f_191, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 6.21/2.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.21/2.21  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 6.21/2.21  tff(f_82, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.21/2.21  tff(f_53, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.21/2.21  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.21/2.21  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.21/2.21  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.21/2.21  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.21/2.21  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.21/2.21  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_50, plain, (![A_58]: (m1_pre_topc(A_58, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_177])).
% 6.21/2.21  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_86, plain, (![B_81, A_82]: (l1_pre_topc(B_81) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.21/2.21  tff(c_92, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_86])).
% 6.21/2.21  tff(c_96, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_92])).
% 6.21/2.21  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_188, plain, (![A_107, B_108]: (m1_pre_topc(A_107, g1_pre_topc(u1_struct_0(B_108), u1_pre_topc(B_108))) | ~m1_pre_topc(A_107, B_108) | ~l1_pre_topc(B_108) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.21/2.21  tff(c_201, plain, (![A_107]: (m1_pre_topc(A_107, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_107, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_107))), inference(superposition, [status(thm), theory('equality')], [c_58, c_188])).
% 6.21/2.21  tff(c_216, plain, (![A_110]: (m1_pre_topc(A_110, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_110, '#skF_2') | ~l1_pre_topc(A_110))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_201])).
% 6.21/2.21  tff(c_34, plain, (![B_26, A_24]: (m1_pre_topc(B_26, A_24) | ~m1_pre_topc(B_26, g1_pre_topc(u1_struct_0(A_24), u1_pre_topc(A_24))) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.21/2.21  tff(c_222, plain, (![A_110]: (m1_pre_topc(A_110, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_110, '#skF_2') | ~l1_pre_topc(A_110))), inference(resolution, [status(thm)], [c_216, c_34])).
% 6.21/2.21  tff(c_233, plain, (![A_111]: (m1_pre_topc(A_111, '#skF_3') | ~m1_pre_topc(A_111, '#skF_2') | ~l1_pre_topc(A_111))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_222])).
% 6.21/2.21  tff(c_243, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_233])).
% 6.21/2.21  tff(c_253, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_243])).
% 6.21/2.21  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_163, plain, (![B_104, A_105]: (m1_pre_topc(B_104, A_105) | ~m1_pre_topc(B_104, g1_pre_topc(u1_struct_0(A_105), u1_pre_topc(A_105))) | ~l1_pre_topc(A_105))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.21/2.21  tff(c_166, plain, (![B_104]: (m1_pre_topc(B_104, '#skF_2') | ~m1_pre_topc(B_104, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_163])).
% 6.21/2.21  tff(c_172, plain, (![B_104]: (m1_pre_topc(B_104, '#skF_2') | ~m1_pre_topc(B_104, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_166])).
% 6.21/2.21  tff(c_192, plain, (![A_107]: (m1_pre_topc(A_107, '#skF_2') | ~m1_pre_topc(A_107, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_188, c_172])).
% 6.21/2.21  tff(c_204, plain, (![A_107]: (m1_pre_topc(A_107, '#skF_2') | ~m1_pre_topc(A_107, '#skF_3') | ~l1_pre_topc(A_107))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_192])).
% 6.21/2.21  tff(c_319, plain, (![B_118, C_119, A_120]: (r1_tarski(u1_struct_0(B_118), u1_struct_0(C_119)) | ~m1_pre_topc(B_118, C_119) | ~m1_pre_topc(C_119, A_120) | ~m1_pre_topc(B_118, A_120) | ~l1_pre_topc(A_120) | ~v2_pre_topc(A_120))), inference(cnfTransformation, [status(thm)], [f_191])).
% 6.21/2.21  tff(c_331, plain, (![B_118, A_107]: (r1_tarski(u1_struct_0(B_118), u1_struct_0(A_107)) | ~m1_pre_topc(B_118, A_107) | ~m1_pre_topc(B_118, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc(A_107, '#skF_3') | ~l1_pre_topc(A_107))), inference(resolution, [status(thm)], [c_204, c_319])).
% 6.21/2.21  tff(c_493, plain, (![B_132, A_133]: (r1_tarski(u1_struct_0(B_132), u1_struct_0(A_133)) | ~m1_pre_topc(B_132, A_133) | ~m1_pre_topc(B_132, '#skF_2') | ~m1_pre_topc(A_133, '#skF_3') | ~l1_pre_topc(A_133))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_331])).
% 6.21/2.21  tff(c_339, plain, (![B_118]: (r1_tarski(u1_struct_0(B_118), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_118, '#skF_3') | ~m1_pre_topc(B_118, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_66, c_319])).
% 6.21/2.21  tff(c_365, plain, (![B_121]: (r1_tarski(u1_struct_0(B_121), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_121, '#skF_3') | ~m1_pre_topc(B_121, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_339])).
% 6.21/2.21  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.21  tff(c_368, plain, (![B_121]: (u1_struct_0(B_121)=u1_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(B_121)) | ~m1_pre_topc(B_121, '#skF_3') | ~m1_pre_topc(B_121, '#skF_2'))), inference(resolution, [status(thm)], [c_365, c_2])).
% 6.21/2.21  tff(c_500, plain, (![A_133]: (u1_struct_0(A_133)=u1_struct_0('#skF_3') | ~m1_pre_topc(A_133, '#skF_2') | ~m1_pre_topc('#skF_3', A_133) | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc(A_133, '#skF_3') | ~l1_pre_topc(A_133))), inference(resolution, [status(thm)], [c_493, c_368])).
% 6.21/2.21  tff(c_511, plain, (![A_134]: (u1_struct_0(A_134)=u1_struct_0('#skF_3') | ~m1_pre_topc(A_134, '#skF_2') | ~m1_pre_topc('#skF_3', A_134) | ~m1_pre_topc(A_134, '#skF_3') | ~l1_pre_topc(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_500])).
% 6.21/2.21  tff(c_521, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_511])).
% 6.21/2.21  tff(c_533, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_253, c_66, c_521])).
% 6.21/2.21  tff(c_62, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_544, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_62])).
% 6.21/2.21  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_543, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_60])).
% 6.21/2.21  tff(c_817, plain, (![C_141, A_144, D_145, B_142, F_143]: (r1_funct_2(A_144, B_142, C_141, D_145, F_143, F_143) | ~m1_subset_1(F_143, k1_zfmisc_1(k2_zfmisc_1(C_141, D_145))) | ~v1_funct_2(F_143, C_141, D_145) | ~m1_subset_1(F_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_142))) | ~v1_funct_2(F_143, A_144, B_142) | ~v1_funct_1(F_143) | v1_xboole_0(D_145) | v1_xboole_0(B_142))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.21/2.21  tff(c_819, plain, (![A_144, B_142]: (r1_funct_2(A_144, B_142, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_144, B_142))) | ~v1_funct_2('#skF_4', A_144, B_142) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_142))), inference(resolution, [status(thm)], [c_543, c_817])).
% 6.21/2.21  tff(c_822, plain, (![A_144, B_142]: (r1_funct_2(A_144, B_142, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_144, B_142))) | ~v1_funct_2('#skF_4', A_144, B_142) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_142))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_544, c_819])).
% 6.21/2.21  tff(c_1887, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_822])).
% 6.21/2.21  tff(c_28, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.21/2.21  tff(c_1890, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1887, c_28])).
% 6.21/2.21  tff(c_1893, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_80, c_1890])).
% 6.21/2.21  tff(c_1896, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1893])).
% 6.21/2.21  tff(c_1900, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1896])).
% 6.21/2.21  tff(c_1902, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_822])).
% 6.21/2.21  tff(c_4724, plain, (![A_233, B_234]: (r1_funct_2(A_233, B_234, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_2('#skF_4', A_233, B_234) | v1_xboole_0(B_234))), inference(splitRight, [status(thm)], [c_822])).
% 6.21/2.21  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_257, plain, (![A_112, B_113, C_114, D_115]: (k2_partfun1(A_112, B_113, C_114, D_115)=k7_relat_1(C_114, D_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~v1_funct_1(C_114))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.21/2.21  tff(c_259, plain, (![D_115]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_115)=k7_relat_1('#skF_4', D_115) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_257])).
% 6.21/2.21  tff(c_262, plain, (![D_115]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_115)=k7_relat_1('#skF_4', D_115))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_259])).
% 6.21/2.21  tff(c_538, plain, (![D_115]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_115)=k7_relat_1('#skF_4', D_115))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_262])).
% 6.21/2.21  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_1114, plain, (![A_157, B_158, C_159, D_160]: (k2_partfun1(u1_struct_0(A_157), u1_struct_0(B_158), C_159, u1_struct_0(D_160))=k2_tmap_1(A_157, B_158, C_159, D_160) | ~m1_pre_topc(D_160, A_157) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_157), u1_struct_0(B_158)))) | ~v1_funct_2(C_159, u1_struct_0(A_157), u1_struct_0(B_158)) | ~v1_funct_1(C_159) | ~l1_pre_topc(B_158) | ~v2_pre_topc(B_158) | v2_struct_0(B_158) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.21/2.21  tff(c_1122, plain, (![B_158, C_159, D_160]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_158), C_159, u1_struct_0(D_160))=k2_tmap_1('#skF_2', B_158, C_159, D_160) | ~m1_pre_topc(D_160, '#skF_2') | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_158)))) | ~v1_funct_2(C_159, u1_struct_0('#skF_2'), u1_struct_0(B_158)) | ~v1_funct_1(C_159) | ~l1_pre_topc(B_158) | ~v2_pre_topc(B_158) | v2_struct_0(B_158) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_533, c_1114])).
% 6.21/2.21  tff(c_1134, plain, (![B_158, C_159, D_160]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_158), C_159, u1_struct_0(D_160))=k2_tmap_1('#skF_2', B_158, C_159, D_160) | ~m1_pre_topc(D_160, '#skF_2') | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_158)))) | ~v1_funct_2(C_159, u1_struct_0('#skF_3'), u1_struct_0(B_158)) | ~v1_funct_1(C_159) | ~l1_pre_topc(B_158) | ~v2_pre_topc(B_158) | v2_struct_0(B_158) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_533, c_533, c_1122])).
% 6.21/2.21  tff(c_1203, plain, (![B_163, C_164, D_165]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_163), C_164, u1_struct_0(D_165))=k2_tmap_1('#skF_2', B_163, C_164, D_165) | ~m1_pre_topc(D_165, '#skF_2') | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_163)))) | ~v1_funct_2(C_164, u1_struct_0('#skF_3'), u1_struct_0(B_163)) | ~v1_funct_1(C_164) | ~l1_pre_topc(B_163) | ~v2_pre_topc(B_163) | v2_struct_0(B_163))), inference(negUnitSimplification, [status(thm)], [c_74, c_1134])).
% 6.21/2.21  tff(c_1207, plain, (![D_165]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_165))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_165) | ~m1_pre_topc(D_165, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_543, c_1203])).
% 6.21/2.21  tff(c_1214, plain, (![D_165]: (k7_relat_1('#skF_4', u1_struct_0(D_165))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_165) | ~m1_pre_topc(D_165, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_544, c_538, c_1207])).
% 6.21/2.21  tff(c_1219, plain, (![D_166]: (k7_relat_1('#skF_4', u1_struct_0(D_166))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_166) | ~m1_pre_topc(D_166, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_80, c_1214])).
% 6.21/2.21  tff(c_104, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.21/2.21  tff(c_108, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_104])).
% 6.21/2.21  tff(c_131, plain, (![C_97, A_98, B_99]: (v4_relat_1(C_97, A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.21/2.21  tff(c_135, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_131])).
% 6.21/2.21  tff(c_8, plain, (![B_4, A_3]: (k7_relat_1(B_4, A_3)=B_4 | ~v4_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.21/2.21  tff(c_138, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_135, c_8])).
% 6.21/2.21  tff(c_141, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_138])).
% 6.21/2.21  tff(c_539, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_141])).
% 6.21/2.21  tff(c_1225, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1219, c_539])).
% 6.21/2.21  tff(c_1240, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1225])).
% 6.21/2.21  tff(c_56, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 6.21/2.21  tff(c_541, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_533, c_56])).
% 6.21/2.21  tff(c_1247, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1240, c_541])).
% 6.21/2.21  tff(c_4727, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_4724, c_1247])).
% 6.21/2.21  tff(c_4732, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_544, c_543, c_4727])).
% 6.21/2.21  tff(c_4734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1902, c_4732])).
% 6.21/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.21  
% 6.21/2.21  Inference rules
% 6.21/2.21  ----------------------
% 6.21/2.21  #Ref     : 0
% 6.21/2.21  #Sup     : 893
% 6.21/2.21  #Fact    : 0
% 6.21/2.21  #Define  : 0
% 6.21/2.21  #Split   : 7
% 6.21/2.21  #Chain   : 0
% 6.21/2.21  #Close   : 0
% 6.21/2.21  
% 6.21/2.21  Ordering : KBO
% 6.21/2.21  
% 6.21/2.21  Simplification rules
% 6.21/2.21  ----------------------
% 6.21/2.21  #Subsume      : 234
% 6.21/2.21  #Demod        : 2303
% 6.21/2.21  #Tautology    : 378
% 6.21/2.21  #SimpNegUnit  : 9
% 6.21/2.21  #BackRed      : 13
% 6.21/2.21  
% 6.21/2.21  #Partial instantiations: 0
% 6.21/2.21  #Strategies tried      : 1
% 6.21/2.21  
% 6.21/2.21  Timing (in seconds)
% 6.21/2.21  ----------------------
% 6.21/2.22  Preprocessing        : 0.39
% 6.21/2.22  Parsing              : 0.20
% 6.21/2.22  CNF conversion       : 0.03
% 6.21/2.22  Main loop            : 1.05
% 6.21/2.22  Inferencing          : 0.31
% 6.21/2.22  Reduction            : 0.43
% 6.21/2.22  Demodulation         : 0.33
% 6.21/2.22  BG Simplification    : 0.04
% 6.21/2.22  Subsumption          : 0.21
% 6.21/2.22  Abstraction          : 0.05
% 6.21/2.22  MUC search           : 0.00
% 6.21/2.22  Cooper               : 0.00
% 6.21/2.22  Total                : 1.47
% 6.21/2.22  Index Insertion      : 0.00
% 6.21/2.22  Index Deletion       : 0.00
% 6.21/2.22  Index Matching       : 0.00
% 6.21/2.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
