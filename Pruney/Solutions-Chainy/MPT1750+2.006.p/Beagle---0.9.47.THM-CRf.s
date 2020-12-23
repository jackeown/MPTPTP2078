%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:51 EST 2020

% Result     : Theorem 5.67s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :  133 (7794 expanded)
%              Number of leaves         :   41 (2724 expanded)
%              Depth                    :   28
%              Number of atoms          :  323 (36222 expanded)
%              Number of equality atoms :   32 (2129 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_201,negated_conjecture,(
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

tff(f_70,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_92,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_154,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_66,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_168,axiom,(
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

tff(f_123,axiom,(
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

tff(f_85,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_150,axiom,(
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

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_20,plain,(
    ! [A_18] :
      ( l1_struct_0(A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_74,plain,(
    ! [B_73,A_74] :
      ( l1_pre_topc(B_73)
      | ~ m1_pre_topc(B_73,A_74)
      | ~ l1_pre_topc(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_74])).

tff(c_84,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_80])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_128,plain,(
    ! [A_85,B_86] :
      ( m1_pre_topc(A_85,g1_pre_topc(u1_struct_0(B_86),u1_pre_topc(B_86)))
      | ~ m1_pre_topc(A_85,B_86)
      | ~ l1_pre_topc(B_86)
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_144,plain,(
    ! [A_85] :
      ( m1_pre_topc(A_85,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_85,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_85) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_128])).

tff(c_174,plain,(
    ! [A_89] :
      ( m1_pre_topc(A_89,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_89,'#skF_2')
      | ~ l1_pre_topc(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_144])).

tff(c_26,plain,(
    ! [B_25,A_23] :
      ( m1_pre_topc(B_25,A_23)
      | ~ m1_pre_topc(B_25,g1_pre_topc(u1_struct_0(A_23),u1_pre_topc(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_180,plain,(
    ! [A_89] :
      ( m1_pre_topc(A_89,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_89,'#skF_2')
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_174,c_26])).

tff(c_193,plain,(
    ! [A_90] :
      ( m1_pre_topc(A_90,'#skF_3')
      | ~ m1_pre_topc(A_90,'#skF_2')
      | ~ l1_pre_topc(A_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_180])).

tff(c_203,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_193])).

tff(c_210,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_203])).

tff(c_38,plain,(
    ! [A_50] :
      ( m1_pre_topc(A_50,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_200,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_193])).

tff(c_207,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_200])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_92,plain,(
    ! [B_77,A_78] :
      ( v2_pre_topc(B_77)
      | ~ m1_pre_topc(B_77,A_78)
      | ~ l1_pre_topc(A_78)
      | ~ v2_pre_topc(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_98,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_92])).

tff(c_102,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_98])).

tff(c_299,plain,(
    ! [B_98,C_99,A_100] :
      ( r1_tarski(u1_struct_0(B_98),u1_struct_0(C_99))
      | ~ m1_pre_topc(B_98,C_99)
      | ~ m1_pre_topc(C_99,A_100)
      | ~ m1_pre_topc(B_98,A_100)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_305,plain,(
    ! [B_98] :
      ( r1_tarski(u1_struct_0(B_98),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_98,'#skF_2')
      | ~ m1_pre_topc(B_98,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_207,c_299])).

tff(c_322,plain,(
    ! [B_98] :
      ( r1_tarski(u1_struct_0(B_98),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_98,'#skF_2')
      | ~ m1_pre_topc(B_98,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_84,c_305])).

tff(c_303,plain,(
    ! [B_98] :
      ( r1_tarski(u1_struct_0(B_98),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_98,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_210,c_299])).

tff(c_332,plain,(
    ! [B_101] :
      ( r1_tarski(u1_struct_0(B_101),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_101,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_84,c_303])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_351,plain,(
    ! [B_109] :
      ( u1_struct_0(B_109) = u1_struct_0('#skF_3')
      | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0(B_109))
      | ~ m1_pre_topc(B_109,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_332,c_2])).

tff(c_359,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_322,c_351])).

tff(c_371,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_54,c_207,c_359])).

tff(c_50,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_386,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_385,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_48])).

tff(c_906,plain,(
    ! [B_140,C_143,A_141,F_142,D_139] :
      ( r1_funct_2(A_141,B_140,C_143,D_139,F_142,F_142)
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_143,D_139)))
      | ~ v1_funct_2(F_142,C_143,D_139)
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2(F_142,A_141,B_140)
      | ~ v1_funct_1(F_142)
      | v1_xboole_0(D_139)
      | v1_xboole_0(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_908,plain,(
    ! [A_141,B_140] :
      ( r1_funct_2(A_141,B_140,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2('#skF_4',A_141,B_140)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_140) ) ),
    inference(resolution,[status(thm)],[c_385,c_906])).

tff(c_913,plain,(
    ! [A_141,B_140] :
      ( r1_funct_2(A_141,B_140,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2('#skF_4',A_141,B_140)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_386,c_908])).

tff(c_1260,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_913])).

tff(c_24,plain,(
    ! [A_22] :
      ( ~ v1_xboole_0(u1_struct_0(A_22))
      | ~ l1_struct_0(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1263,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1260,c_24])).

tff(c_1266,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1263])).

tff(c_1269,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_1266])).

tff(c_1273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1269])).

tff(c_1275,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_3015,plain,(
    ! [A_271,B_272] :
      ( r1_funct_2(A_271,B_272,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_271,B_272)))
      | ~ v1_funct_2('#skF_4',A_271,B_272)
      | v1_xboole_0(B_272) ) ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1323,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( k2_partfun1(u1_struct_0(A_166),u1_struct_0(B_167),C_168,u1_struct_0(D_169)) = k2_tmap_1(A_166,B_167,C_168,D_169)
      | ~ m1_pre_topc(D_169,A_166)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166),u1_struct_0(B_167))))
      | ~ v1_funct_2(C_168,u1_struct_0(A_166),u1_struct_0(B_167))
      | ~ v1_funct_1(C_168)
      | ~ l1_pre_topc(B_167)
      | ~ v2_pre_topc(B_167)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1325,plain,(
    ! [D_169] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_169)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_169)
      | ~ m1_pre_topc(D_169,'#skF_3')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_385,c_1323])).

tff(c_1335,plain,(
    ! [D_169] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_169)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_169)
      | ~ m1_pre_topc(D_169,'#skF_3')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_84,c_66,c_64,c_52,c_386,c_1325])).

tff(c_1478,plain,(
    ! [D_174] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_174)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_174)
      | ~ m1_pre_topc(D_174,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_68,c_1335])).

tff(c_1495,plain,
    ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1478])).

tff(c_1501,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_1495])).

tff(c_1336,plain,(
    ! [D_169] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_169)) = k2_tmap_1('#skF_3','#skF_1','#skF_4',D_169)
      | ~ m1_pre_topc(D_169,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_68,c_1335])).

tff(c_1542,plain,
    ( k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2') = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1501,c_1336])).

tff(c_1557,plain,(
    k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2') = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_1542])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( m1_subset_1(k2_partfun1(A_7,B_8,C_9,D_10),k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8)))
      | ~ v1_funct_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1550,plain,
    ( m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1501,c_12])).

tff(c_1561,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_385,c_1550])).

tff(c_1625,plain,(
    m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1561])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_723,plain,(
    ! [A_127,B_128,D_129,C_130] :
      ( r2_relset_1(A_127,B_128,k2_partfun1(A_127,B_128,D_129,C_130),D_129)
      | ~ r1_tarski(A_127,C_130)
      | ~ m1_subset_1(D_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128)))
      | ~ v1_funct_2(D_129,A_127,B_128)
      | ~ v1_funct_1(D_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_725,plain,(
    ! [C_130] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_130),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_130)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_385,c_723])).

tff(c_730,plain,(
    ! [C_130] :
      ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',C_130),'#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_3'),C_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_386,c_725])).

tff(c_1545,plain,
    ( r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2'),'#skF_4')
    | ~ r1_tarski(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1501,c_730])).

tff(c_1559,plain,(
    r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1545])).

tff(c_1619,plain,(
    r2_relset_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1559])).

tff(c_10,plain,(
    ! [D_6,C_5,A_3,B_4] :
      ( D_6 = C_5
      | ~ r2_relset_1(A_3,B_4,C_5,D_6)
      | ~ m1_subset_1(D_6,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4)))
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1621,plain,
    ( k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(resolution,[status(thm)],[c_1619,c_10])).

tff(c_1624,plain,
    ( k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_subset_1(k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_1621])).

tff(c_2271,plain,(
    k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1625,c_1624])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1327,plain,(
    ! [B_167,C_168,D_169] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_167),C_168,u1_struct_0(D_169)) = k2_tmap_1('#skF_2',B_167,C_168,D_169)
      | ~ m1_pre_topc(D_169,'#skF_2')
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_167))))
      | ~ v1_funct_2(C_168,u1_struct_0('#skF_2'),u1_struct_0(B_167))
      | ~ v1_funct_1(C_168)
      | ~ l1_pre_topc(B_167)
      | ~ v2_pre_topc(B_167)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1323])).

tff(c_1338,plain,(
    ! [B_167,C_168,D_169] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_167),C_168,u1_struct_0(D_169)) = k2_tmap_1('#skF_2',B_167,C_168,D_169)
      | ~ m1_pre_topc(D_169,'#skF_2')
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_167))))
      | ~ v1_funct_2(C_168,u1_struct_0('#skF_3'),u1_struct_0(B_167))
      | ~ v1_funct_1(C_168)
      | ~ l1_pre_topc(B_167)
      | ~ v2_pre_topc(B_167)
      | v2_struct_0(B_167)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_371,c_371,c_1327])).

tff(c_1602,plain,(
    ! [B_181,C_182,D_183] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_181),C_182,u1_struct_0(D_183)) = k2_tmap_1('#skF_2',B_181,C_182,D_183)
      | ~ m1_pre_topc(D_183,'#skF_2')
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_181))))
      | ~ v1_funct_2(C_182,u1_struct_0('#skF_3'),u1_struct_0(B_181))
      | ~ v1_funct_1(C_182)
      | ~ l1_pre_topc(B_181)
      | ~ v2_pre_topc(B_181)
      | v2_struct_0(B_181) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1338])).

tff(c_1604,plain,(
    ! [D_183] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_183)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_183)
      | ~ m1_pre_topc(D_183,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_385,c_1602])).

tff(c_1612,plain,(
    ! [D_183] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_183)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_183)
      | ~ m1_pre_topc(D_183,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_386,c_1604])).

tff(c_1737,plain,(
    ! [D_188] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_188)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_188)
      | ~ m1_pre_topc(D_188,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1612])).

tff(c_1591,plain,(
    k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0('#skF_3')) = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1501])).

tff(c_1743,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1737,c_1591])).

tff(c_1775,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1743])).

tff(c_44,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_382,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_44])).

tff(c_1797,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_3','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1775,c_382])).

tff(c_2276,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2271,c_1797])).

tff(c_3018,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_3015,c_2276])).

tff(c_3023,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_385,c_3018])).

tff(c_3025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1275,c_3023])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:04:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.67/2.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.09  
% 5.67/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.09  %$ r1_funct_2 > r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.67/2.09  
% 5.67/2.09  %Foreground sorts:
% 5.67/2.09  
% 5.67/2.09  
% 5.67/2.09  %Background operators:
% 5.67/2.09  
% 5.67/2.09  
% 5.67/2.09  %Foreground operators:
% 5.67/2.09  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.67/2.09  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.67/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.67/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.67/2.09  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.67/2.09  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.67/2.09  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.67/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.67/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.67/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.67/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.67/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.67/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.67/2.09  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.67/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.67/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.67/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.67/2.09  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 5.67/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.67/2.09  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.67/2.09  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.67/2.09  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.67/2.09  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.67/2.09  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.67/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.67/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.67/2.09  
% 5.67/2.11  tff(f_201, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 5.67/2.11  tff(f_70, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.67/2.11  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.67/2.11  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.67/2.11  tff(f_92, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 5.67/2.11  tff(f_154, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.67/2.11  tff(f_66, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.67/2.11  tff(f_168, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 5.67/2.11  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.67/2.11  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 5.67/2.11  tff(f_85, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.67/2.11  tff(f_150, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.67/2.11  tff(f_47, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 5.67/2.11  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 5.67/2.11  tff(f_39, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.67/2.11  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_20, plain, (![A_18]: (l1_struct_0(A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.67/2.11  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_74, plain, (![B_73, A_74]: (l1_pre_topc(B_73) | ~m1_pre_topc(B_73, A_74) | ~l1_pre_topc(A_74))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.67/2.11  tff(c_80, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_74])).
% 5.67/2.11  tff(c_84, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_80])).
% 5.67/2.11  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_128, plain, (![A_85, B_86]: (m1_pre_topc(A_85, g1_pre_topc(u1_struct_0(B_86), u1_pre_topc(B_86))) | ~m1_pre_topc(A_85, B_86) | ~l1_pre_topc(B_86) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.67/2.11  tff(c_144, plain, (![A_85]: (m1_pre_topc(A_85, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_85, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_85))), inference(superposition, [status(thm), theory('equality')], [c_46, c_128])).
% 5.67/2.11  tff(c_174, plain, (![A_89]: (m1_pre_topc(A_89, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_89, '#skF_2') | ~l1_pre_topc(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_144])).
% 5.67/2.11  tff(c_26, plain, (![B_25, A_23]: (m1_pre_topc(B_25, A_23) | ~m1_pre_topc(B_25, g1_pre_topc(u1_struct_0(A_23), u1_pre_topc(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_92])).
% 5.67/2.11  tff(c_180, plain, (![A_89]: (m1_pre_topc(A_89, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_89, '#skF_2') | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_174, c_26])).
% 5.67/2.11  tff(c_193, plain, (![A_90]: (m1_pre_topc(A_90, '#skF_3') | ~m1_pre_topc(A_90, '#skF_2') | ~l1_pre_topc(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_180])).
% 5.67/2.11  tff(c_203, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_193])).
% 5.67/2.11  tff(c_210, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_203])).
% 5.67/2.11  tff(c_38, plain, (![A_50]: (m1_pre_topc(A_50, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_154])).
% 5.67/2.11  tff(c_200, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_38, c_193])).
% 5.67/2.11  tff(c_207, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_200])).
% 5.67/2.11  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_92, plain, (![B_77, A_78]: (v2_pre_topc(B_77) | ~m1_pre_topc(B_77, A_78) | ~l1_pre_topc(A_78) | ~v2_pre_topc(A_78))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.67/2.11  tff(c_98, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_92])).
% 5.67/2.11  tff(c_102, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_98])).
% 5.67/2.11  tff(c_299, plain, (![B_98, C_99, A_100]: (r1_tarski(u1_struct_0(B_98), u1_struct_0(C_99)) | ~m1_pre_topc(B_98, C_99) | ~m1_pre_topc(C_99, A_100) | ~m1_pre_topc(B_98, A_100) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100))), inference(cnfTransformation, [status(thm)], [f_168])).
% 5.67/2.11  tff(c_305, plain, (![B_98]: (r1_tarski(u1_struct_0(B_98), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_98, '#skF_2') | ~m1_pre_topc(B_98, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_207, c_299])).
% 5.67/2.11  tff(c_322, plain, (![B_98]: (r1_tarski(u1_struct_0(B_98), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_98, '#skF_2') | ~m1_pre_topc(B_98, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_84, c_305])).
% 5.67/2.11  tff(c_303, plain, (![B_98]: (r1_tarski(u1_struct_0(B_98), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_98, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_210, c_299])).
% 5.67/2.11  tff(c_332, plain, (![B_101]: (r1_tarski(u1_struct_0(B_101), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_101, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_84, c_303])).
% 5.67/2.11  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.67/2.11  tff(c_351, plain, (![B_109]: (u1_struct_0(B_109)=u1_struct_0('#skF_3') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0(B_109)) | ~m1_pre_topc(B_109, '#skF_3'))), inference(resolution, [status(thm)], [c_332, c_2])).
% 5.67/2.11  tff(c_359, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_322, c_351])).
% 5.67/2.11  tff(c_371, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_54, c_207, c_359])).
% 5.67/2.11  tff(c_50, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_386, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_50])).
% 5.67/2.11  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_385, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_48])).
% 5.67/2.11  tff(c_906, plain, (![B_140, C_143, A_141, F_142, D_139]: (r1_funct_2(A_141, B_140, C_143, D_139, F_142, F_142) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_143, D_139))) | ~v1_funct_2(F_142, C_143, D_139) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2(F_142, A_141, B_140) | ~v1_funct_1(F_142) | v1_xboole_0(D_139) | v1_xboole_0(B_140))), inference(cnfTransformation, [status(thm)], [f_123])).
% 5.67/2.11  tff(c_908, plain, (![A_141, B_140]: (r1_funct_2(A_141, B_140, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2('#skF_4', A_141, B_140) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_140))), inference(resolution, [status(thm)], [c_385, c_906])).
% 5.67/2.11  tff(c_913, plain, (![A_141, B_140]: (r1_funct_2(A_141, B_140, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2('#skF_4', A_141, B_140) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_140))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_386, c_908])).
% 5.67/2.11  tff(c_1260, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_913])).
% 5.67/2.11  tff(c_24, plain, (![A_22]: (~v1_xboole_0(u1_struct_0(A_22)) | ~l1_struct_0(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.67/2.11  tff(c_1263, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1260, c_24])).
% 5.67/2.11  tff(c_1266, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_1263])).
% 5.67/2.11  tff(c_1269, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_20, c_1266])).
% 5.67/2.11  tff(c_1273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_1269])).
% 5.67/2.11  tff(c_1275, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_913])).
% 5.67/2.11  tff(c_3015, plain, (![A_271, B_272]: (r1_funct_2(A_271, B_272, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))) | ~v1_funct_2('#skF_4', A_271, B_272) | v1_xboole_0(B_272))), inference(splitRight, [status(thm)], [c_913])).
% 5.67/2.11  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_1323, plain, (![A_166, B_167, C_168, D_169]: (k2_partfun1(u1_struct_0(A_166), u1_struct_0(B_167), C_168, u1_struct_0(D_169))=k2_tmap_1(A_166, B_167, C_168, D_169) | ~m1_pre_topc(D_169, A_166) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0(A_166), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_pre_topc(B_167) | ~v2_pre_topc(B_167) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.67/2.11  tff(c_1325, plain, (![D_169]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_169))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_169) | ~m1_pre_topc(D_169, '#skF_3') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_385, c_1323])).
% 5.67/2.11  tff(c_1335, plain, (![D_169]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_169))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_169) | ~m1_pre_topc(D_169, '#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_84, c_66, c_64, c_52, c_386, c_1325])).
% 5.67/2.11  tff(c_1478, plain, (![D_174]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_174))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_174) | ~m1_pre_topc(D_174, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_68, c_1335])).
% 5.67/2.11  tff(c_1495, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_371, c_1478])).
% 5.67/2.11  tff(c_1501, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_207, c_1495])).
% 5.67/2.11  tff(c_1336, plain, (![D_169]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_169))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', D_169) | ~m1_pre_topc(D_169, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_56, c_68, c_1335])).
% 5.67/2.11  tff(c_1542, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1501, c_1336])).
% 5.67/2.11  tff(c_1557, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2')=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_1542])).
% 5.67/2.11  tff(c_12, plain, (![A_7, B_8, C_9, D_10]: (m1_subset_1(k2_partfun1(A_7, B_8, C_9, D_10), k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))) | ~v1_funct_1(C_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.67/2.11  tff(c_1550, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1501, c_12])).
% 5.67/2.11  tff(c_1561, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_385, c_1550])).
% 5.67/2.11  tff(c_1625, plain, (m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_1557, c_1561])).
% 5.67/2.11  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.67/2.11  tff(c_723, plain, (![A_127, B_128, D_129, C_130]: (r2_relset_1(A_127, B_128, k2_partfun1(A_127, B_128, D_129, C_130), D_129) | ~r1_tarski(A_127, C_130) | ~m1_subset_1(D_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))) | ~v1_funct_2(D_129, A_127, B_128) | ~v1_funct_1(D_129))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.67/2.11  tff(c_725, plain, (![C_130]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_130), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_130) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_385, c_723])).
% 5.67/2.11  tff(c_730, plain, (![C_130]: (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', C_130), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), C_130))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_386, c_725])).
% 5.67/2.11  tff(c_1545, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2'), '#skF_4') | ~r1_tarski(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1501, c_730])).
% 5.67/2.11  tff(c_1559, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1545])).
% 5.67/2.11  tff(c_1619, plain, (r2_relset_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1557, c_1559])).
% 5.67/2.11  tff(c_10, plain, (![D_6, C_5, A_3, B_4]: (D_6=C_5 | ~r2_relset_1(A_3, B_4, C_5, D_6) | ~m1_subset_1(D_6, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.67/2.11  tff(c_1621, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_1619, c_10])).
% 5.67/2.11  tff(c_1624, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_subset_1(k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_385, c_1621])).
% 5.67/2.11  tff(c_2271, plain, (k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1625, c_1624])).
% 5.67/2.11  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_1327, plain, (![B_167, C_168, D_169]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_167), C_168, u1_struct_0(D_169))=k2_tmap_1('#skF_2', B_167, C_168, D_169) | ~m1_pre_topc(D_169, '#skF_2') | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0('#skF_2'), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_pre_topc(B_167) | ~v2_pre_topc(B_167) | v2_struct_0(B_167) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_1323])).
% 5.67/2.11  tff(c_1338, plain, (![B_167, C_168, D_169]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_167), C_168, u1_struct_0(D_169))=k2_tmap_1('#skF_2', B_167, C_168, D_169) | ~m1_pre_topc(D_169, '#skF_2') | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0('#skF_3'), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_pre_topc(B_167) | ~v2_pre_topc(B_167) | v2_struct_0(B_167) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_371, c_371, c_1327])).
% 5.67/2.11  tff(c_1602, plain, (![B_181, C_182, D_183]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_181), C_182, u1_struct_0(D_183))=k2_tmap_1('#skF_2', B_181, C_182, D_183) | ~m1_pre_topc(D_183, '#skF_2') | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_181)))) | ~v1_funct_2(C_182, u1_struct_0('#skF_3'), u1_struct_0(B_181)) | ~v1_funct_1(C_182) | ~l1_pre_topc(B_181) | ~v2_pre_topc(B_181) | v2_struct_0(B_181))), inference(negUnitSimplification, [status(thm)], [c_62, c_1338])).
% 5.67/2.11  tff(c_1604, plain, (![D_183]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_183))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_183) | ~m1_pre_topc(D_183, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_385, c_1602])).
% 5.67/2.11  tff(c_1612, plain, (![D_183]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_183))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_183) | ~m1_pre_topc(D_183, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_386, c_1604])).
% 5.67/2.11  tff(c_1737, plain, (![D_188]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_188))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_188) | ~m1_pre_topc(D_188, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_68, c_1612])).
% 5.67/2.11  tff(c_1591, plain, (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0('#skF_3'))=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1557, c_1501])).
% 5.67/2.11  tff(c_1743, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1737, c_1591])).
% 5.67/2.11  tff(c_1775, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')=k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1743])).
% 5.67/2.11  tff(c_44, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 5.67/2.11  tff(c_382, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_44])).
% 5.67/2.11  tff(c_1797, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_3', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1775, c_382])).
% 5.67/2.11  tff(c_2276, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2271, c_1797])).
% 5.67/2.11  tff(c_3018, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_3015, c_2276])).
% 5.67/2.11  tff(c_3023, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_386, c_385, c_3018])).
% 5.67/2.11  tff(c_3025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1275, c_3023])).
% 5.67/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.67/2.11  
% 5.67/2.11  Inference rules
% 5.67/2.11  ----------------------
% 5.67/2.11  #Ref     : 0
% 5.67/2.11  #Sup     : 587
% 5.67/2.11  #Fact    : 0
% 5.67/2.11  #Define  : 0
% 5.67/2.11  #Split   : 5
% 5.67/2.11  #Chain   : 0
% 5.67/2.11  #Close   : 0
% 5.67/2.11  
% 5.67/2.11  Ordering : KBO
% 5.67/2.11  
% 5.67/2.11  Simplification rules
% 5.67/2.11  ----------------------
% 5.67/2.11  #Subsume      : 137
% 5.67/2.11  #Demod        : 1120
% 5.67/2.11  #Tautology    : 273
% 5.67/2.11  #SimpNegUnit  : 32
% 5.67/2.11  #BackRed      : 35
% 5.67/2.11  
% 5.67/2.11  #Partial instantiations: 0
% 5.67/2.11  #Strategies tried      : 1
% 5.67/2.11  
% 5.67/2.11  Timing (in seconds)
% 5.67/2.11  ----------------------
% 5.67/2.12  Preprocessing        : 0.37
% 5.67/2.12  Parsing              : 0.19
% 5.67/2.12  CNF conversion       : 0.03
% 5.67/2.12  Main loop            : 0.95
% 5.67/2.12  Inferencing          : 0.32
% 5.67/2.12  Reduction            : 0.33
% 5.67/2.12  Demodulation         : 0.24
% 5.67/2.12  BG Simplification    : 0.04
% 5.67/2.12  Subsumption          : 0.20
% 5.67/2.12  Abstraction          : 0.05
% 5.67/2.12  MUC search           : 0.00
% 5.67/2.12  Cooper               : 0.00
% 5.67/2.12  Total                : 1.36
% 5.67/2.12  Index Insertion      : 0.00
% 5.67/2.12  Index Deletion       : 0.00
% 5.67/2.12  Index Matching       : 0.00
% 5.67/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
