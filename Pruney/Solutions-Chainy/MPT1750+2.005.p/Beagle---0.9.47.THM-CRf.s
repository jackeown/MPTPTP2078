%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:51 EST 2020

% Result     : Theorem 7.68s
% Output     : CNFRefutation 8.14s
% Verified   : 
% Statistics : Number of formulae       :  160 (2130 expanded)
%              Number of leaves         :   45 ( 789 expanded)
%              Depth                    :   24
%              Number of atoms          :  401 (10820 expanded)
%              Number of equality atoms :   35 ( 892 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_228,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_tmap_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_181,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_195,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_177,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

tff(f_132,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

tff(f_95,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_159,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(A,C)
       => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_24,plain,(
    ! [A_20] :
      ( l1_struct_0(A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_48,plain,(
    ! [A_58] :
      ( m1_pre_topc(A_58,A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_188,plain,(
    ! [B_106,C_107,A_108] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0(C_107))
      | ~ m1_pre_topc(B_106,C_107)
      | ~ m1_pre_topc(C_107,A_108)
      | ~ m1_pre_topc(B_106,A_108)
      | ~ l1_pre_topc(A_108)
      | ~ v2_pre_topc(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_198,plain,(
    ! [B_106,A_58] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0(A_58))
      | ~ m1_pre_topc(B_106,A_58)
      | ~ v2_pre_topc(A_58)
      | ~ l1_pre_topc(A_58) ) ),
    inference(resolution,[status(thm)],[c_48,c_188])).

tff(c_194,plain,(
    ! [B_106] :
      ( r1_tarski(u1_struct_0(B_106),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_106,'#skF_3')
      | ~ m1_pre_topc(B_106,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_188])).

tff(c_202,plain,(
    ! [B_109] :
      ( r1_tarski(u1_struct_0(B_109),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_109,'#skF_3')
      | ~ m1_pre_topc(B_109,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_194])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_239,plain,(
    ! [B_113] :
      ( u1_struct_0(B_113) = u1_struct_0('#skF_3')
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(B_113))
      | ~ m1_pre_topc(B_113,'#skF_3')
      | ~ m1_pre_topc(B_113,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_202,c_2])).

tff(c_283,plain,(
    ! [A_120] :
      ( u1_struct_0(A_120) = u1_struct_0('#skF_3')
      | ~ m1_pre_topc(A_120,'#skF_3')
      | ~ m1_pre_topc(A_120,'#skF_2')
      | ~ m1_pre_topc('#skF_3',A_120)
      | ~ v2_pre_topc(A_120)
      | ~ l1_pre_topc(A_120) ) ),
    inference(resolution,[status(thm)],[c_198,c_239])).

tff(c_291,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_283])).

tff(c_302,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_64,c_291])).

tff(c_307,plain,(
    ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_302])).

tff(c_84,plain,(
    ! [B_81,A_82] :
      ( l1_pre_topc(B_81)
      | ~ m1_pre_topc(B_81,A_82)
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_84])).

tff(c_94,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_90])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_119,plain,(
    ! [A_91] :
      ( m1_subset_1(u1_pre_topc(A_91),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_91))))
      | ~ l1_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( l1_pre_topc(g1_pre_topc(A_18,B_19))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_140,plain,(
    ! [A_94] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_94),u1_pre_topc(A_94)))
      | ~ l1_pre_topc(A_94) ) ),
    inference(resolution,[status(thm)],[c_119,c_20])).

tff(c_143,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_140])).

tff(c_145,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_143])).

tff(c_150,plain,(
    ! [B_98,A_99] :
      ( m1_pre_topc(B_98,A_99)
      | ~ m1_pre_topc(B_98,g1_pre_topc(u1_struct_0(A_99),u1_pre_topc(A_99)))
      | ~ l1_pre_topc(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_153,plain,(
    ! [B_98] :
      ( m1_pre_topc(B_98,'#skF_2')
      | ~ m1_pre_topc(B_98,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_150])).

tff(c_168,plain,(
    ! [B_105] :
      ( m1_pre_topc(B_105,'#skF_2')
      | ~ m1_pre_topc(B_105,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_153])).

tff(c_172,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_48,c_168])).

tff(c_175,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_172])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_308,plain,(
    ! [B_121,C_122,A_123] :
      ( m1_pre_topc(B_121,C_122)
      | ~ r1_tarski(u1_struct_0(B_121),u1_struct_0(C_122))
      | ~ m1_pre_topc(C_122,A_123)
      | ~ m1_pre_topc(B_121,A_123)
      | ~ l1_pre_topc(A_123)
      | ~ v2_pre_topc(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_319,plain,(
    ! [B_124,A_125] :
      ( m1_pre_topc(B_124,B_124)
      | ~ m1_pre_topc(B_124,A_125)
      | ~ l1_pre_topc(A_125)
      | ~ v2_pre_topc(A_125) ) ),
    inference(resolution,[status(thm)],[c_6,c_308])).

tff(c_323,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_175,c_319])).

tff(c_331,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_323])).

tff(c_36,plain,(
    ! [B_29,A_27] :
      ( m1_pre_topc(B_29,A_27)
      | ~ m1_pre_topc(B_29,g1_pre_topc(u1_struct_0(A_27),u1_pre_topc(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_386,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_331,c_36])).

tff(c_403,plain,(
    m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_386])).

tff(c_134,plain,(
    ! [A_93] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_93),u1_pre_topc(A_93)))
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_137,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_134])).

tff(c_139,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_137])).

tff(c_742,plain,(
    ! [C_144,A_145] :
      ( m1_pre_topc(C_144,A_145)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_144),u1_pre_topc(C_144)),A_145)
      | ~ l1_pre_topc(C_144)
      | ~ v2_pre_topc(C_144)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_144),u1_pre_topc(C_144)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_144),u1_pre_topc(C_144)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_760,plain,(
    ! [A_145] :
      ( m1_pre_topc('#skF_2',A_145)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_145)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_145) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_742])).

tff(c_812,plain,(
    ! [A_146] :
      ( m1_pre_topc('#skF_2',A_146)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_146)
      | ~ l1_pre_topc(A_146) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_56,c_145,c_56,c_70,c_68,c_760])).

tff(c_815,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_403,c_812])).

tff(c_832,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_815])).

tff(c_834,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_832])).

tff(c_835,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_859,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_60])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_858,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_58])).

tff(c_1768,plain,(
    ! [D_181,B_178,C_177,A_180,F_179] :
      ( r1_funct_2(A_180,B_178,C_177,D_181,F_179,F_179)
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(C_177,D_181)))
      | ~ v1_funct_2(F_179,C_177,D_181)
      | ~ m1_subset_1(F_179,k1_zfmisc_1(k2_zfmisc_1(A_180,B_178)))
      | ~ v1_funct_2(F_179,A_180,B_178)
      | ~ v1_funct_1(F_179)
      | v1_xboole_0(D_181)
      | v1_xboole_0(B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1770,plain,(
    ! [A_180,B_178] :
      ( r1_funct_2(A_180,B_178,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_180,B_178)))
      | ~ v1_funct_2('#skF_4',A_180,B_178)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_178) ) ),
    inference(resolution,[status(thm)],[c_858,c_1768])).

tff(c_1775,plain,(
    ! [A_180,B_178] :
      ( r1_funct_2(A_180,B_178,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_180,B_178)))
      | ~ v1_funct_2('#skF_4',A_180,B_178)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_859,c_1770])).

tff(c_1901,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1775])).

tff(c_30,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(u1_struct_0(A_25))
      | ~ l1_struct_0(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1904,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1901,c_30])).

tff(c_1907,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1904])).

tff(c_1910,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1907])).

tff(c_1914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1910])).

tff(c_1916,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1775])).

tff(c_1915,plain,(
    ! [A_180,B_178] :
      ( r1_funct_2(A_180,B_178,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_180,B_178)))
      | ~ v1_funct_2('#skF_4',A_180,B_178)
      | v1_xboole_0(B_178) ) ),
    inference(splitRight,[status(thm)],[c_1775])).

tff(c_935,plain,(
    ! [B_147,C_148,A_149] :
      ( m1_pre_topc(B_147,C_148)
      | ~ r1_tarski(u1_struct_0(B_147),u1_struct_0(C_148))
      | ~ m1_pre_topc(C_148,A_149)
      | ~ m1_pre_topc(B_147,A_149)
      | ~ l1_pre_topc(A_149)
      | ~ v2_pre_topc(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1011,plain,(
    ! [B_156,A_157] :
      ( m1_pre_topc(B_156,B_156)
      | ~ m1_pre_topc(B_156,A_157)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157) ) ),
    inference(resolution,[status(thm)],[c_6,c_935])).

tff(c_1021,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_1011])).

tff(c_1032,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1021])).

tff(c_836,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_302])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_107,plain,(
    ! [B_87,A_88] :
      ( v2_pre_topc(B_87)
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88)
      | ~ v2_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_113,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_107])).

tff(c_117,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_113])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_2178,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( k2_partfun1(u1_struct_0(A_199),u1_struct_0(B_200),C_201,u1_struct_0(D_202)) = k2_tmap_1(A_199,B_200,C_201,D_202)
      | ~ m1_pre_topc(D_202,A_199)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_199),u1_struct_0(B_200))))
      | ~ v1_funct_2(C_201,u1_struct_0(A_199),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc(A_199)
      | ~ v2_pre_topc(A_199)
      | v2_struct_0(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_2184,plain,(
    ! [D_202] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_858,c_2178])).

tff(c_2198,plain,(
    ! [D_202] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_94,c_76,c_74,c_62,c_859,c_2184])).

tff(c_2207,plain,(
    ! [D_203] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_203)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_203)
      | ~ m1_pre_topc(D_203,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_78,c_2198])).

tff(c_2227,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_2207])).

tff(c_2235,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_836,c_2227])).

tff(c_2199,plain,(
    ! [D_202] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_202)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_202)
      | ~ m1_pre_topc(D_202,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_78,c_2198])).

tff(c_2254,plain,
    ( k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2') = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2235,c_2199])).

tff(c_2269,plain,(
    k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2') = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1032,c_2254])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( m1_subset_1(k2_partfun1(A_7,B_8,C_9,D_10),k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2262,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2235,c_12])).

tff(c_2273,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_858,c_2262])).

tff(c_2311,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2269,c_2273])).

tff(c_1107,plain,(
    ! [A_159,B_160,D_161,C_162] :
      ( r2_relset_1(A_159,B_160,k2_partfun1(A_159,B_160,D_161,C_162),D_161)
      | ~ r1_tarski(A_159,C_162)
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_2(D_161,A_159,B_160)
      | ~ v1_funct_1(D_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1109,plain,(
    ! [C_162] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_162),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_162)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_858,c_1107])).

tff(c_1114,plain,(
    ! [C_162] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_162),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_859,c_1109])).

tff(c_2257,plain,
    ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2'),'#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2235,c_1114])).

tff(c_2271,plain,(
    r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2257])).

tff(c_2305,plain,(
    r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2269,c_2271])).

tff(c_10,plain,(
    ! [D_6,C_5,A_3,B_4] :
      ( D_6 = C_5
      | ~ r2_relset_1(A_3,B_4,C_5,D_6)
      | ~ m1_subset_1(D_6,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2307,plain,
    ( k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_2305,c_10])).

tff(c_2310,plain,
    ( k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_858,c_2307])).

tff(c_7445,plain,(
    k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2311,c_2310])).

tff(c_2278,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2269,c_2235])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_2186,plain,(
    ! [B_200,C_201,D_202] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_200),C_201,u1_struct_0(D_202)) = k2_tmap_1('#skF_2',B_200,C_201,D_202)
      | ~ m1_pre_topc(D_202,'#skF_2')
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_200))))
      | ~ v1_funct_2(C_201,u1_struct_0('#skF_2'),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_835,c_2178])).

tff(c_2201,plain,(
    ! [B_200,C_201,D_202] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_200),C_201,u1_struct_0(D_202)) = k2_tmap_1('#skF_2',B_200,C_201,D_202)
      | ~ m1_pre_topc(D_202,'#skF_2')
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_200))))
      | ~ v1_funct_2(C_201,u1_struct_0('#skF_3'),u1_struct_0(B_200))
      | ~ v1_funct_1(C_201)
      | ~ l1_pre_topc(B_200)
      | ~ v2_pre_topc(B_200)
      | v2_struct_0(B_200)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_835,c_835,c_2186])).

tff(c_4975,plain,(
    ! [B_303,C_304,D_305] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_303),C_304,u1_struct_0(D_305)) = k2_tmap_1('#skF_2',B_303,C_304,D_305)
      | ~ m1_pre_topc(D_305,'#skF_2')
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_303))))
      | ~ v1_funct_2(C_304,u1_struct_0('#skF_3'),u1_struct_0(B_303))
      | ~ v1_funct_1(C_304)
      | ~ l1_pre_topc(B_303)
      | ~ v2_pre_topc(B_303)
      | v2_struct_0(B_303) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_2201])).

tff(c_4985,plain,(
    ! [D_305] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_305)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_305)
      | ~ m1_pre_topc(D_305,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_858,c_4975])).

tff(c_5005,plain,(
    ! [D_305] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_305)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_305)
      | ~ m1_pre_topc(D_305,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_859,c_4985])).

tff(c_5123,plain,(
    ! [D_310] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_310)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_310)
      | ~ m1_pre_topc(D_310,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5005])).

tff(c_5157,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2278,c_5123])).

tff(c_5180,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5157])).

tff(c_54,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_856,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_54])).

tff(c_5241,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5180,c_856])).

tff(c_7449,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7445,c_5241])).

tff(c_7859,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_1915,c_7449])).

tff(c_7862,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_859,c_858,c_7859])).

tff(c_7864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1916,c_7862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.68/2.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.68  
% 7.68/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.68/2.68  %$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.68/2.68  
% 7.68/2.68  %Foreground sorts:
% 7.68/2.68  
% 7.68/2.68  
% 7.68/2.68  %Background operators:
% 7.68/2.68  
% 7.68/2.68  
% 7.68/2.68  %Foreground operators:
% 7.68/2.68  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.68/2.68  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.68/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.68/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.68/2.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.68/2.68  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.68/2.68  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.68/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.68/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.68/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.68/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.68/2.68  tff('#skF_1', type, '#skF_1': $i).
% 7.68/2.68  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.68/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.68/2.68  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.68/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.68/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.68/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.68/2.68  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 7.68/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.68/2.68  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.68/2.68  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.68/2.68  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.68/2.68  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.68/2.68  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.68/2.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.68/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.68/2.68  
% 8.14/2.70  tff(f_228, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 8.14/2.70  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.14/2.70  tff(f_181, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.14/2.70  tff(f_195, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 8.14/2.70  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.14/2.70  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.14/2.70  tff(f_87, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 8.14/2.70  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 8.14/2.70  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 8.14/2.70  tff(f_103, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 8.14/2.70  tff(f_177, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 8.14/2.70  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 8.14/2.70  tff(f_95, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 8.14/2.70  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 8.14/2.70  tff(f_159, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 8.14/2.70  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 8.14/2.70  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 8.14/2.70  tff(f_39, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.14/2.70  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_24, plain, (![A_20]: (l1_struct_0(A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.14/2.70  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_48, plain, (![A_58]: (m1_pre_topc(A_58, A_58) | ~l1_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_181])).
% 8.14/2.70  tff(c_188, plain, (![B_106, C_107, A_108]: (r1_tarski(u1_struct_0(B_106), u1_struct_0(C_107)) | ~m1_pre_topc(B_106, C_107) | ~m1_pre_topc(C_107, A_108) | ~m1_pre_topc(B_106, A_108) | ~l1_pre_topc(A_108) | ~v2_pre_topc(A_108))), inference(cnfTransformation, [status(thm)], [f_195])).
% 8.14/2.70  tff(c_198, plain, (![B_106, A_58]: (r1_tarski(u1_struct_0(B_106), u1_struct_0(A_58)) | ~m1_pre_topc(B_106, A_58) | ~v2_pre_topc(A_58) | ~l1_pre_topc(A_58))), inference(resolution, [status(thm)], [c_48, c_188])).
% 8.14/2.70  tff(c_194, plain, (![B_106]: (r1_tarski(u1_struct_0(B_106), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_106, '#skF_3') | ~m1_pre_topc(B_106, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_188])).
% 8.14/2.70  tff(c_202, plain, (![B_109]: (r1_tarski(u1_struct_0(B_109), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_109, '#skF_3') | ~m1_pre_topc(B_109, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_194])).
% 8.14/2.70  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.14/2.70  tff(c_239, plain, (![B_113]: (u1_struct_0(B_113)=u1_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(B_113)) | ~m1_pre_topc(B_113, '#skF_3') | ~m1_pre_topc(B_113, '#skF_2'))), inference(resolution, [status(thm)], [c_202, c_2])).
% 8.14/2.70  tff(c_283, plain, (![A_120]: (u1_struct_0(A_120)=u1_struct_0('#skF_3') | ~m1_pre_topc(A_120, '#skF_3') | ~m1_pre_topc(A_120, '#skF_2') | ~m1_pre_topc('#skF_3', A_120) | ~v2_pre_topc(A_120) | ~l1_pre_topc(A_120))), inference(resolution, [status(thm)], [c_198, c_239])).
% 8.14/2.70  tff(c_291, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_48, c_283])).
% 8.14/2.70  tff(c_302, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_64, c_291])).
% 8.14/2.70  tff(c_307, plain, (~m1_pre_topc('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_302])).
% 8.14/2.70  tff(c_84, plain, (![B_81, A_82]: (l1_pre_topc(B_81) | ~m1_pre_topc(B_81, A_82) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.14/2.70  tff(c_90, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_84])).
% 8.14/2.70  tff(c_94, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_90])).
% 8.14/2.70  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_119, plain, (![A_91]: (m1_subset_1(u1_pre_topc(A_91), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_91)))) | ~l1_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.14/2.70  tff(c_20, plain, (![A_18, B_19]: (l1_pre_topc(g1_pre_topc(A_18, B_19)) | ~m1_subset_1(B_19, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.14/2.70  tff(c_140, plain, (![A_94]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_94), u1_pre_topc(A_94))) | ~l1_pre_topc(A_94))), inference(resolution, [status(thm)], [c_119, c_20])).
% 8.14/2.70  tff(c_143, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_140])).
% 8.14/2.70  tff(c_145, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_143])).
% 8.14/2.70  tff(c_150, plain, (![B_98, A_99]: (m1_pre_topc(B_98, A_99) | ~m1_pre_topc(B_98, g1_pre_topc(u1_struct_0(A_99), u1_pre_topc(A_99))) | ~l1_pre_topc(A_99))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.14/2.70  tff(c_153, plain, (![B_98]: (m1_pre_topc(B_98, '#skF_2') | ~m1_pre_topc(B_98, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_150])).
% 8.14/2.70  tff(c_168, plain, (![B_105]: (m1_pre_topc(B_105, '#skF_2') | ~m1_pre_topc(B_105, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_153])).
% 8.14/2.70  tff(c_172, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_48, c_168])).
% 8.14/2.70  tff(c_175, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_172])).
% 8.14/2.70  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.14/2.70  tff(c_308, plain, (![B_121, C_122, A_123]: (m1_pre_topc(B_121, C_122) | ~r1_tarski(u1_struct_0(B_121), u1_struct_0(C_122)) | ~m1_pre_topc(C_122, A_123) | ~m1_pre_topc(B_121, A_123) | ~l1_pre_topc(A_123) | ~v2_pre_topc(A_123))), inference(cnfTransformation, [status(thm)], [f_195])).
% 8.14/2.70  tff(c_319, plain, (![B_124, A_125]: (m1_pre_topc(B_124, B_124) | ~m1_pre_topc(B_124, A_125) | ~l1_pre_topc(A_125) | ~v2_pre_topc(A_125))), inference(resolution, [status(thm)], [c_6, c_308])).
% 8.14/2.70  tff(c_323, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_175, c_319])).
% 8.14/2.70  tff(c_331, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_323])).
% 8.14/2.70  tff(c_36, plain, (![B_29, A_27]: (m1_pre_topc(B_29, A_27) | ~m1_pre_topc(B_29, g1_pre_topc(u1_struct_0(A_27), u1_pre_topc(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 8.14/2.70  tff(c_386, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_331, c_36])).
% 8.14/2.70  tff(c_403, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_386])).
% 8.14/2.70  tff(c_134, plain, (![A_93]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_93), u1_pre_topc(A_93))) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.14/2.70  tff(c_137, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_134])).
% 8.14/2.70  tff(c_139, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_137])).
% 8.14/2.70  tff(c_742, plain, (![C_144, A_145]: (m1_pre_topc(C_144, A_145) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_144), u1_pre_topc(C_144)), A_145) | ~l1_pre_topc(C_144) | ~v2_pre_topc(C_144) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_144), u1_pre_topc(C_144))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_144), u1_pre_topc(C_144))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.14/2.70  tff(c_760, plain, (![A_145]: (m1_pre_topc('#skF_2', A_145) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_145) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_145))), inference(superposition, [status(thm), theory('equality')], [c_56, c_742])).
% 8.14/2.70  tff(c_812, plain, (![A_146]: (m1_pre_topc('#skF_2', A_146) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_146) | ~l1_pre_topc(A_146))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_56, c_145, c_56, c_70, c_68, c_760])).
% 8.14/2.70  tff(c_815, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_403, c_812])).
% 8.14/2.70  tff(c_832, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_815])).
% 8.14/2.70  tff(c_834, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_832])).
% 8.14/2.70  tff(c_835, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_302])).
% 8.14/2.70  tff(c_60, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_859, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_60])).
% 8.14/2.70  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_858, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_58])).
% 8.14/2.70  tff(c_1768, plain, (![D_181, B_178, C_177, A_180, F_179]: (r1_funct_2(A_180, B_178, C_177, D_181, F_179, F_179) | ~m1_subset_1(F_179, k1_zfmisc_1(k2_zfmisc_1(C_177, D_181))) | ~v1_funct_2(F_179, C_177, D_181) | ~m1_subset_1(F_179, k1_zfmisc_1(k2_zfmisc_1(A_180, B_178))) | ~v1_funct_2(F_179, A_180, B_178) | ~v1_funct_1(F_179) | v1_xboole_0(D_181) | v1_xboole_0(B_178))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.14/2.70  tff(c_1770, plain, (![A_180, B_178]: (r1_funct_2(A_180, B_178, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_180, B_178))) | ~v1_funct_2('#skF_4', A_180, B_178) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_178))), inference(resolution, [status(thm)], [c_858, c_1768])).
% 8.14/2.70  tff(c_1775, plain, (![A_180, B_178]: (r1_funct_2(A_180, B_178, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_180, B_178))) | ~v1_funct_2('#skF_4', A_180, B_178) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_178))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_859, c_1770])).
% 8.14/2.70  tff(c_1901, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1775])).
% 8.14/2.70  tff(c_30, plain, (![A_25]: (~v1_xboole_0(u1_struct_0(A_25)) | ~l1_struct_0(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.14/2.70  tff(c_1904, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1901, c_30])).
% 8.14/2.70  tff(c_1907, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_78, c_1904])).
% 8.14/2.70  tff(c_1910, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1907])).
% 8.14/2.70  tff(c_1914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1910])).
% 8.14/2.70  tff(c_1916, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1775])).
% 8.14/2.70  tff(c_1915, plain, (![A_180, B_178]: (r1_funct_2(A_180, B_178, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_180, B_178))) | ~v1_funct_2('#skF_4', A_180, B_178) | v1_xboole_0(B_178))), inference(splitRight, [status(thm)], [c_1775])).
% 8.14/2.70  tff(c_935, plain, (![B_147, C_148, A_149]: (m1_pre_topc(B_147, C_148) | ~r1_tarski(u1_struct_0(B_147), u1_struct_0(C_148)) | ~m1_pre_topc(C_148, A_149) | ~m1_pre_topc(B_147, A_149) | ~l1_pre_topc(A_149) | ~v2_pre_topc(A_149))), inference(cnfTransformation, [status(thm)], [f_195])).
% 8.14/2.70  tff(c_1011, plain, (![B_156, A_157]: (m1_pre_topc(B_156, B_156) | ~m1_pre_topc(B_156, A_157) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157))), inference(resolution, [status(thm)], [c_6, c_935])).
% 8.14/2.70  tff(c_1021, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_1011])).
% 8.14/2.70  tff(c_1032, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1021])).
% 8.14/2.70  tff(c_836, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_302])).
% 8.14/2.70  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_107, plain, (![B_87, A_88]: (v2_pre_topc(B_87) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88) | ~v2_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.14/2.70  tff(c_113, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_107])).
% 8.14/2.70  tff(c_117, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_113])).
% 8.14/2.70  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_2178, plain, (![A_199, B_200, C_201, D_202]: (k2_partfun1(u1_struct_0(A_199), u1_struct_0(B_200), C_201, u1_struct_0(D_202))=k2_tmap_1(A_199, B_200, C_201, D_202) | ~m1_pre_topc(D_202, A_199) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_199), u1_struct_0(B_200)))) | ~v1_funct_2(C_201, u1_struct_0(A_199), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc(A_199) | ~v2_pre_topc(A_199) | v2_struct_0(A_199))), inference(cnfTransformation, [status(thm)], [f_159])).
% 8.14/2.70  tff(c_2184, plain, (![D_202]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_858, c_2178])).
% 8.14/2.70  tff(c_2198, plain, (![D_202]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_94, c_76, c_74, c_62, c_859, c_2184])).
% 8.14/2.70  tff(c_2207, plain, (![D_203]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_203))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_203) | ~m1_pre_topc(D_203, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_78, c_2198])).
% 8.14/2.70  tff(c_2227, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_835, c_2207])).
% 8.14/2.70  tff(c_2235, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_836, c_2227])).
% 8.14/2.70  tff(c_2199, plain, (![D_202]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_202))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_202) | ~m1_pre_topc(D_202, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_66, c_78, c_2198])).
% 8.14/2.70  tff(c_2254, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2235, c_2199])).
% 8.14/2.70  tff(c_2269, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1032, c_2254])).
% 8.14/2.70  tff(c_12, plain, (![A_7, B_8, C_9, D_10]: (m1_subset_1(k2_partfun1(A_7, B_8, C_9, D_10), k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.14/2.70  tff(c_2262, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2235, c_12])).
% 8.14/2.70  tff(c_2273, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_858, c_2262])).
% 8.14/2.70  tff(c_2311, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_2269, c_2273])).
% 8.14/2.70  tff(c_1107, plain, (![A_159, B_160, D_161, C_162]: (r2_relset_1(A_159, B_160, k2_partfun1(A_159, B_160, D_161, C_162), D_161) | ~r1_tarski(A_159, C_162) | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_2(D_161, A_159, B_160) | ~v1_funct_1(D_161))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.14/2.70  tff(c_1109, plain, (![C_162]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_162), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_162) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_858, c_1107])).
% 8.14/2.70  tff(c_1114, plain, (![C_162]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_162), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_162))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_859, c_1109])).
% 8.14/2.70  tff(c_2257, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2'), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2235, c_1114])).
% 8.14/2.70  tff(c_2271, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2257])).
% 8.14/2.70  tff(c_2305, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2269, c_2271])).
% 8.14/2.70  tff(c_10, plain, (![D_6, C_5, A_3, B_4]: (D_6=C_5 | ~r2_relset_1(A_3, B_4, C_5, D_6) | ~m1_subset_1(D_6, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.14/2.70  tff(c_2307, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_2305, c_10])).
% 8.14/2.70  tff(c_2310, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_858, c_2307])).
% 8.14/2.70  tff(c_7445, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2311, c_2310])).
% 8.14/2.70  tff(c_2278, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2269, c_2235])).
% 8.14/2.70  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_2186, plain, (![B_200, C_201, D_202]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_200), C_201, u1_struct_0(D_202))=k2_tmap_1('#skF_2', B_200, C_201, D_202) | ~m1_pre_topc(D_202, '#skF_2') | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_200)))) | ~v1_funct_2(C_201, u1_struct_0('#skF_2'), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_835, c_2178])).
% 8.14/2.70  tff(c_2201, plain, (![B_200, C_201, D_202]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_200), C_201, u1_struct_0(D_202))=k2_tmap_1('#skF_2', B_200, C_201, D_202) | ~m1_pre_topc(D_202, '#skF_2') | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_200)))) | ~v1_funct_2(C_201, u1_struct_0('#skF_3'), u1_struct_0(B_200)) | ~v1_funct_1(C_201) | ~l1_pre_topc(B_200) | ~v2_pre_topc(B_200) | v2_struct_0(B_200) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_835, c_835, c_2186])).
% 8.14/2.70  tff(c_4975, plain, (![B_303, C_304, D_305]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_303), C_304, u1_struct_0(D_305))=k2_tmap_1('#skF_2', B_303, C_304, D_305) | ~m1_pre_topc(D_305, '#skF_2') | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_303)))) | ~v1_funct_2(C_304, u1_struct_0('#skF_3'), u1_struct_0(B_303)) | ~v1_funct_1(C_304) | ~l1_pre_topc(B_303) | ~v2_pre_topc(B_303) | v2_struct_0(B_303))), inference(negUnitSimplification, [status(thm)], [c_72, c_2201])).
% 8.14/2.70  tff(c_4985, plain, (![D_305]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_305))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_305) | ~m1_pre_topc(D_305, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_858, c_4975])).
% 8.14/2.70  tff(c_5005, plain, (![D_305]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_305))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_305) | ~m1_pre_topc(D_305, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_859, c_4985])).
% 8.14/2.70  tff(c_5123, plain, (![D_310]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_310))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_310) | ~m1_pre_topc(D_310, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_78, c_5005])).
% 8.14/2.70  tff(c_5157, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2278, c_5123])).
% 8.14/2.70  tff(c_5180, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5157])).
% 8.14/2.70  tff(c_54, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 8.14/2.70  tff(c_856, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_835, c_54])).
% 8.14/2.70  tff(c_5241, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5180, c_856])).
% 8.14/2.70  tff(c_7449, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7445, c_5241])).
% 8.14/2.70  tff(c_7859, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_1915, c_7449])).
% 8.14/2.70  tff(c_7862, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_859, c_858, c_7859])).
% 8.14/2.70  tff(c_7864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1916, c_7862])).
% 8.14/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.14/2.70  
% 8.14/2.70  Inference rules
% 8.14/2.70  ----------------------
% 8.14/2.70  #Ref     : 0
% 8.14/2.70  #Sup     : 1535
% 8.14/2.70  #Fact    : 0
% 8.14/2.70  #Define  : 0
% 8.14/2.70  #Split   : 7
% 8.14/2.70  #Chain   : 0
% 8.14/2.70  #Close   : 0
% 8.14/2.70  
% 8.14/2.70  Ordering : KBO
% 8.14/2.70  
% 8.14/2.70  Simplification rules
% 8.14/2.70  ----------------------
% 8.14/2.70  #Subsume      : 210
% 8.14/2.70  #Demod        : 3737
% 8.14/2.70  #Tautology    : 746
% 8.14/2.71  #SimpNegUnit  : 69
% 8.14/2.71  #BackRed      : 49
% 8.14/2.71  
% 8.14/2.71  #Partial instantiations: 0
% 8.14/2.71  #Strategies tried      : 1
% 8.14/2.71  
% 8.14/2.71  Timing (in seconds)
% 8.14/2.71  ----------------------
% 8.14/2.71  Preprocessing        : 0.38
% 8.14/2.71  Parsing              : 0.20
% 8.14/2.71  CNF conversion       : 0.03
% 8.14/2.71  Main loop            : 1.53
% 8.14/2.71  Inferencing          : 0.46
% 8.14/2.71  Reduction            : 0.65
% 8.14/2.71  Demodulation         : 0.50
% 8.14/2.71  BG Simplification    : 0.05
% 8.14/2.71  Subsumption          : 0.29
% 8.14/2.71  Abstraction          : 0.07
% 8.14/2.71  MUC search           : 0.00
% 8.14/2.71  Cooper               : 0.00
% 8.14/2.71  Total                : 1.96
% 8.14/2.71  Index Insertion      : 0.00
% 8.14/2.71  Index Deletion       : 0.00
% 8.14/2.71  Index Matching       : 0.00
% 8.14/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
