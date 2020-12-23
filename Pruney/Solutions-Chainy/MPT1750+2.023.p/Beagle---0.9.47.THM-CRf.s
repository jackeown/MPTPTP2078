%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:54 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 8.36s
% Verified   : 
% Statistics : Number of formulae       :  157 (1717 expanded)
%              Number of leaves         :   48 ( 609 expanded)
%              Depth                    :   23
%              Number of atoms          :  383 (7540 expanded)
%              Number of equality atoms :   30 ( 488 expanded)
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

tff(f_216,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_158,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_176,axiom,(
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

tff(f_183,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_122,axiom,(
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

tff(f_76,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_149,axiom,(
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

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_88,plain,(
    ! [B_80,A_81] :
      ( l1_pre_topc(B_80)
      | ~ m1_pre_topc(B_80,A_81)
      | ~ l1_pre_topc(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_88])).

tff(c_94,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_91])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_293,plain,(
    ! [A_129,B_130] :
      ( m1_pre_topc(A_129,g1_pre_topc(u1_struct_0(B_130),u1_pre_topc(B_130)))
      | ~ m1_pre_topc(A_129,B_130)
      | ~ l1_pre_topc(B_130)
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_310,plain,(
    ! [A_129] :
      ( m1_pre_topc(A_129,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_129,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_293])).

tff(c_368,plain,(
    ! [A_139] :
      ( m1_pre_topc(A_139,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_139,'#skF_2')
      | ~ l1_pre_topc(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_310])).

tff(c_32,plain,(
    ! [B_25,A_23] :
      ( m1_pre_topc(B_25,A_23)
      | ~ m1_pre_topc(B_25,g1_pre_topc(u1_struct_0(A_23),u1_pre_topc(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_376,plain,(
    ! [A_139] :
      ( m1_pre_topc(A_139,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_139,'#skF_2')
      | ~ l1_pre_topc(A_139) ) ),
    inference(resolution,[status(thm)],[c_368,c_32])).

tff(c_395,plain,(
    ! [A_140] :
      ( m1_pre_topc(A_140,'#skF_3')
      | ~ m1_pre_topc(A_140,'#skF_2')
      | ~ l1_pre_topc(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_376])).

tff(c_409,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_395])).

tff(c_419,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_409])).

tff(c_44,plain,(
    ! [B_52,A_50] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_52),u1_pre_topc(B_52)),A_50)
      | ~ m1_pre_topc(B_52,A_50)
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_241,plain,(
    ! [B_124,A_125] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_124),u1_pre_topc(B_124)),A_125)
      | ~ m1_pre_topc(B_124,A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_24,plain,(
    ! [B_20,A_18] :
      ( l1_pre_topc(B_20)
      | ~ m1_pre_topc(B_20,A_18)
      | ~ l1_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_280,plain,(
    ! [B_127,A_128] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_127),u1_pre_topc(B_127)))
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_241,c_24])).

tff(c_286,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_280])).

tff(c_291,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_286])).

tff(c_257,plain,(
    ! [A_125] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_125)
      | ~ m1_pre_topc('#skF_2',A_125)
      | ~ l1_pre_topc(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_241])).

tff(c_402,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_257,c_395])).

tff(c_413,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_291,c_402])).

tff(c_436,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_234,plain,(
    ! [B_121,A_122] :
      ( m1_pre_topc(B_121,A_122)
      | ~ m1_pre_topc(B_121,g1_pre_topc(u1_struct_0(A_122),u1_pre_topc(A_122)))
      | ~ l1_pre_topc(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_237,plain,(
    ! [B_121] :
      ( m1_pre_topc(B_121,'#skF_2')
      | ~ m1_pre_topc(B_121,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_234])).

tff(c_239,plain,(
    ! [B_121] :
      ( m1_pre_topc(B_121,'#skF_2')
      | ~ m1_pre_topc(B_121,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_237])).

tff(c_299,plain,(
    ! [A_129] :
      ( m1_pre_topc(A_129,'#skF_2')
      | ~ m1_pre_topc(A_129,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_129) ) ),
    inference(resolution,[status(thm)],[c_293,c_239])).

tff(c_314,plain,(
    ! [A_129] :
      ( m1_pre_topc(A_129,'#skF_2')
      | ~ m1_pre_topc(A_129,'#skF_3')
      | ~ l1_pre_topc(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_299])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_213,plain,(
    ! [A_114] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_114),u1_pre_topc(A_114)))
      | ~ l1_pre_topc(A_114)
      | ~ v2_pre_topc(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_216,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_213])).

tff(c_218,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_216])).

tff(c_443,plain,(
    ! [C_141,A_142] :
      ( m1_pre_topc(C_141,A_142)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_141),u1_pre_topc(C_141)),A_142)
      | ~ l1_pre_topc(C_141)
      | ~ v2_pre_topc(C_141)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_141),u1_pre_topc(C_141)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_141),u1_pre_topc(C_141)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_464,plain,(
    ! [A_142] :
      ( m1_pre_topc('#skF_2',A_142)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_142)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_443])).

tff(c_485,plain,(
    ! [A_144] :
      ( m1_pre_topc('#skF_2',A_144)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_144)
      | ~ l1_pre_topc(A_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_56,c_291,c_56,c_70,c_68,c_464])).

tff(c_493,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_314,c_485])).

tff(c_510,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_68,c_493])).

tff(c_511,plain,(
    ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_510])).

tff(c_522,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_511])).

tff(c_529,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_419,c_522])).

tff(c_531,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_388,plain,(
    ! [A_139] :
      ( m1_pre_topc(A_139,'#skF_3')
      | ~ m1_pre_topc(A_139,'#skF_2')
      | ~ l1_pre_topc(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_376])).

tff(c_534,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_531,c_388])).

tff(c_544,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_534])).

tff(c_219,plain,(
    ! [B_115,A_116] :
      ( m1_subset_1(u1_struct_0(B_115),k1_zfmisc_1(u1_struct_0(A_116)))
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_223,plain,(
    ! [B_115,A_116] :
      ( r1_tarski(u1_struct_0(B_115),u1_struct_0(A_116))
      | ~ m1_pre_topc(B_115,A_116)
      | ~ l1_pre_topc(A_116) ) ),
    inference(resolution,[status(thm)],[c_219,c_8])).

tff(c_224,plain,(
    ! [B_117,A_118] :
      ( r1_tarski(u1_struct_0(B_117),u1_struct_0(A_118))
      | ~ m1_pre_topc(B_117,A_118)
      | ~ l1_pre_topc(A_118) ) ),
    inference(resolution,[status(thm)],[c_219,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_710,plain,(
    ! [B_151,A_152] :
      ( u1_struct_0(B_151) = u1_struct_0(A_152)
      | ~ r1_tarski(u1_struct_0(A_152),u1_struct_0(B_151))
      | ~ m1_pre_topc(B_151,A_152)
      | ~ l1_pre_topc(A_152) ) ),
    inference(resolution,[status(thm)],[c_224,c_2])).

tff(c_808,plain,(
    ! [B_158,A_159] :
      ( u1_struct_0(B_158) = u1_struct_0(A_159)
      | ~ m1_pre_topc(A_159,B_158)
      | ~ l1_pre_topc(B_158)
      | ~ m1_pre_topc(B_158,A_159)
      | ~ l1_pre_topc(A_159) ) ),
    inference(resolution,[status(thm)],[c_223,c_710])).

tff(c_834,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_808])).

tff(c_871,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_544,c_68,c_834])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_764,plain,(
    ! [A_155,D_153,F_156,C_157,B_154] :
      ( r1_funct_2(A_155,B_154,C_157,D_153,F_156,F_156)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(C_157,D_153)))
      | ~ v1_funct_2(F_156,C_157,D_153)
      | ~ m1_subset_1(F_156,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154)))
      | ~ v1_funct_2(F_156,A_155,B_154)
      | ~ v1_funct_1(F_156)
      | v1_xboole_0(D_153)
      | v1_xboole_0(B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_766,plain,(
    ! [A_155,B_154] :
      ( r1_funct_2(A_155,B_154,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_155,B_154)))
      | ~ v1_funct_2('#skF_4',A_155,B_154)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_154) ) ),
    inference(resolution,[status(thm)],[c_58,c_764])).

tff(c_772,plain,(
    ! [A_155,B_154] :
      ( r1_funct_2(A_155,B_154,u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_155,B_154)))
      | ~ v1_funct_2('#skF_4',A_155,B_154)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_766])).

tff(c_1670,plain,(
    ! [A_155,B_154] :
      ( r1_funct_2(A_155,B_154,u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_155,B_154)))
      | ~ v1_funct_2('#skF_4',A_155,B_154)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_772])).

tff(c_1671,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1670])).

tff(c_26,plain,(
    ! [A_21] :
      ( ~ v1_xboole_0(u1_struct_0(A_21))
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1674,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1671,c_26])).

tff(c_1677,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1674])).

tff(c_1680,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1677])).

tff(c_1684,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1680])).

tff(c_1686,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1670])).

tff(c_99,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_8])).

tff(c_878,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_99])).

tff(c_880,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_60])).

tff(c_879,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_58])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1745,plain,(
    ! [C_203,A_200,D_199,B_202,A_201] :
      ( r1_funct_2(A_200,B_202,C_203,D_199,A_201,A_201)
      | ~ v1_funct_2(A_201,C_203,D_199)
      | ~ m1_subset_1(A_201,k1_zfmisc_1(k2_zfmisc_1(A_200,B_202)))
      | ~ v1_funct_2(A_201,A_200,B_202)
      | ~ v1_funct_1(A_201)
      | v1_xboole_0(D_199)
      | v1_xboole_0(B_202)
      | ~ r1_tarski(A_201,k2_zfmisc_1(C_203,D_199)) ) ),
    inference(resolution,[status(thm)],[c_10,c_764])).

tff(c_1747,plain,(
    ! [C_203,D_199] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_203,D_199,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_203,D_199)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_199)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_203,D_199)) ) ),
    inference(resolution,[status(thm)],[c_879,c_1745])).

tff(c_1753,plain,(
    ! [C_203,D_199] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_203,D_199,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_203,D_199)
      | v1_xboole_0(D_199)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_203,D_199)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_880,c_1747])).

tff(c_3390,plain,(
    ! [C_253,D_254] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_253,D_254,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_253,D_254)
      | v1_xboole_0(D_254)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_253,D_254)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1686,c_1753])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_337,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k2_partfun1(A_132,B_133,C_134,D_135) = k7_relat_1(C_134,D_135)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133)))
      | ~ v1_funct_1(C_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_339,plain,(
    ! [D_135] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_135) = k7_relat_1('#skF_4',D_135)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_337])).

tff(c_345,plain,(
    ! [D_135] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_135) = k7_relat_1('#skF_4',D_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_339])).

tff(c_872,plain,(
    ! [D_135] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_135) = k7_relat_1('#skF_4',D_135) ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_345])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_1016,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1020,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_871,c_1016])).

tff(c_1031,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_871,c_871,c_1020])).

tff(c_1687,plain,(
    ! [B_195,C_196,D_197] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_195),C_196,u1_struct_0(D_197)) = k2_tmap_1('#skF_2',B_195,C_196,D_197)
      | ~ m1_pre_topc(D_197,'#skF_2')
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_195))))
      | ~ v1_funct_2(C_196,u1_struct_0('#skF_3'),u1_struct_0(B_195))
      | ~ v1_funct_1(C_196)
      | ~ l1_pre_topc(B_195)
      | ~ v2_pre_topc(B_195)
      | v2_struct_0(B_195) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1031])).

tff(c_1691,plain,(
    ! [D_197] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_197)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_197)
      | ~ m1_pre_topc(D_197,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_879,c_1687])).

tff(c_1701,plain,(
    ! [D_197] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_197)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_197)
      | ~ m1_pre_topc(D_197,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_880,c_872,c_1691])).

tff(c_1756,plain,(
    ! [D_204] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_204)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_204)
      | ~ m1_pre_topc(D_204,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1701])).

tff(c_114,plain,(
    ! [C_85,A_86,B_87] :
      ( v1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_122,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_114])).

tff(c_158,plain,(
    ! [C_101,A_102,B_103] :
      ( v4_relat_1(C_101,A_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_166,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_158])).

tff(c_180,plain,(
    ! [B_109,A_110] :
      ( k7_relat_1(B_109,A_110) = B_109
      | ~ v4_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_186,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_166,c_180])).

tff(c_192,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_186])).

tff(c_874,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_192])).

tff(c_1762,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1756,c_874])).

tff(c_1777,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1762])).

tff(c_54,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_876,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_54])).

tff(c_1785,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1777,c_876])).

tff(c_3393,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_3390,c_1785])).

tff(c_3398,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_880,c_3393])).

tff(c_3400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1686,c_3398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:04:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.95/3.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.36/3.02  
% 8.36/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.36/3.02  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.36/3.02  
% 8.36/3.02  %Foreground sorts:
% 8.36/3.02  
% 8.36/3.02  
% 8.36/3.02  %Background operators:
% 8.36/3.02  
% 8.36/3.02  
% 8.36/3.02  %Foreground operators:
% 8.36/3.02  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.36/3.02  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 8.36/3.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.36/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.36/3.02  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 8.36/3.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.36/3.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.36/3.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.36/3.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.36/3.02  tff('#skF_2', type, '#skF_2': $i).
% 8.36/3.02  tff('#skF_3', type, '#skF_3': $i).
% 8.36/3.02  tff('#skF_1', type, '#skF_1': $i).
% 8.36/3.02  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.36/3.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.36/3.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.36/3.02  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 8.36/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.36/3.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.36/3.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.36/3.02  tff('#skF_4', type, '#skF_4': $i).
% 8.36/3.02  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 8.36/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.36/3.02  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.36/3.02  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.36/3.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.36/3.02  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.36/3.02  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 8.36/3.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.36/3.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.36/3.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.36/3.02  
% 8.36/3.06  tff(f_216, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 8.36/3.06  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.36/3.06  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 8.36/3.06  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 8.36/3.06  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 8.36/3.06  tff(f_158, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 8.36/3.06  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 8.36/3.06  tff(f_176, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 8.36/3.06  tff(f_183, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 8.36/3.06  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.36/3.06  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.36/3.06  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 8.36/3.06  tff(f_76, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 8.36/3.06  tff(f_57, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.36/3.06  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 8.36/3.06  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.36/3.06  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.36/3.06  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 8.36/3.06  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.36/3.06  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_88, plain, (![B_80, A_81]: (l1_pre_topc(B_80) | ~m1_pre_topc(B_80, A_81) | ~l1_pre_topc(A_81))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.36/3.06  tff(c_91, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_88])).
% 8.36/3.06  tff(c_94, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_91])).
% 8.36/3.06  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_293, plain, (![A_129, B_130]: (m1_pre_topc(A_129, g1_pre_topc(u1_struct_0(B_130), u1_pre_topc(B_130))) | ~m1_pre_topc(A_129, B_130) | ~l1_pre_topc(B_130) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.36/3.06  tff(c_310, plain, (![A_129]: (m1_pre_topc(A_129, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_129, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_129))), inference(superposition, [status(thm), theory('equality')], [c_56, c_293])).
% 8.36/3.06  tff(c_368, plain, (![A_139]: (m1_pre_topc(A_139, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_139, '#skF_2') | ~l1_pre_topc(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_310])).
% 8.36/3.06  tff(c_32, plain, (![B_25, A_23]: (m1_pre_topc(B_25, A_23) | ~m1_pre_topc(B_25, g1_pre_topc(u1_struct_0(A_23), u1_pre_topc(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.36/3.06  tff(c_376, plain, (![A_139]: (m1_pre_topc(A_139, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_139, '#skF_2') | ~l1_pre_topc(A_139))), inference(resolution, [status(thm)], [c_368, c_32])).
% 8.36/3.06  tff(c_395, plain, (![A_140]: (m1_pre_topc(A_140, '#skF_3') | ~m1_pre_topc(A_140, '#skF_2') | ~l1_pre_topc(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_376])).
% 8.36/3.06  tff(c_409, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_395])).
% 8.36/3.06  tff(c_419, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_409])).
% 8.36/3.06  tff(c_44, plain, (![B_52, A_50]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_52), u1_pre_topc(B_52)), A_50) | ~m1_pre_topc(B_52, A_50) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.36/3.06  tff(c_241, plain, (![B_124, A_125]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_124), u1_pre_topc(B_124)), A_125) | ~m1_pre_topc(B_124, A_125) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.36/3.06  tff(c_24, plain, (![B_20, A_18]: (l1_pre_topc(B_20) | ~m1_pre_topc(B_20, A_18) | ~l1_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.36/3.06  tff(c_280, plain, (![B_127, A_128]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_127), u1_pre_topc(B_127))) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_241, c_24])).
% 8.36/3.06  tff(c_286, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_280])).
% 8.36/3.06  tff(c_291, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_286])).
% 8.36/3.06  tff(c_257, plain, (![A_125]: (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_125) | ~m1_pre_topc('#skF_2', A_125) | ~l1_pre_topc(A_125))), inference(superposition, [status(thm), theory('equality')], [c_56, c_241])).
% 8.36/3.06  tff(c_402, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_257, c_395])).
% 8.36/3.06  tff(c_413, plain, (m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_291, c_402])).
% 8.36/3.06  tff(c_436, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_413])).
% 8.36/3.06  tff(c_234, plain, (![B_121, A_122]: (m1_pre_topc(B_121, A_122) | ~m1_pre_topc(B_121, g1_pre_topc(u1_struct_0(A_122), u1_pre_topc(A_122))) | ~l1_pre_topc(A_122))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.36/3.06  tff(c_237, plain, (![B_121]: (m1_pre_topc(B_121, '#skF_2') | ~m1_pre_topc(B_121, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_234])).
% 8.36/3.06  tff(c_239, plain, (![B_121]: (m1_pre_topc(B_121, '#skF_2') | ~m1_pre_topc(B_121, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_237])).
% 8.36/3.06  tff(c_299, plain, (![A_129]: (m1_pre_topc(A_129, '#skF_2') | ~m1_pre_topc(A_129, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_129))), inference(resolution, [status(thm)], [c_293, c_239])).
% 8.36/3.06  tff(c_314, plain, (![A_129]: (m1_pre_topc(A_129, '#skF_2') | ~m1_pre_topc(A_129, '#skF_3') | ~l1_pre_topc(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_299])).
% 8.36/3.06  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_213, plain, (![A_114]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_114), u1_pre_topc(A_114))) | ~l1_pre_topc(A_114) | ~v2_pre_topc(A_114))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.36/3.06  tff(c_216, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_213])).
% 8.36/3.06  tff(c_218, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_216])).
% 8.36/3.06  tff(c_443, plain, (![C_141, A_142]: (m1_pre_topc(C_141, A_142) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_141), u1_pre_topc(C_141)), A_142) | ~l1_pre_topc(C_141) | ~v2_pre_topc(C_141) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_141), u1_pre_topc(C_141))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_141), u1_pre_topc(C_141))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_176])).
% 8.36/3.06  tff(c_464, plain, (![A_142]: (m1_pre_topc('#skF_2', A_142) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_142) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_142))), inference(superposition, [status(thm), theory('equality')], [c_56, c_443])).
% 8.36/3.06  tff(c_485, plain, (![A_144]: (m1_pre_topc('#skF_2', A_144) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_144) | ~l1_pre_topc(A_144))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_56, c_291, c_56, c_70, c_68, c_464])).
% 8.36/3.06  tff(c_493, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_314, c_485])).
% 8.36/3.06  tff(c_510, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_68, c_493])).
% 8.36/3.06  tff(c_511, plain, (~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_436, c_510])).
% 8.36/3.06  tff(c_522, plain, (~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_44, c_511])).
% 8.36/3.06  tff(c_529, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_419, c_522])).
% 8.36/3.06  tff(c_531, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_413])).
% 8.36/3.06  tff(c_388, plain, (![A_139]: (m1_pre_topc(A_139, '#skF_3') | ~m1_pre_topc(A_139, '#skF_2') | ~l1_pre_topc(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_376])).
% 8.36/3.06  tff(c_534, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_531, c_388])).
% 8.36/3.06  tff(c_544, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_534])).
% 8.36/3.06  tff(c_219, plain, (![B_115, A_116]: (m1_subset_1(u1_struct_0(B_115), k1_zfmisc_1(u1_struct_0(A_116))) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116))), inference(cnfTransformation, [status(thm)], [f_183])).
% 8.36/3.06  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.36/3.06  tff(c_223, plain, (![B_115, A_116]: (r1_tarski(u1_struct_0(B_115), u1_struct_0(A_116)) | ~m1_pre_topc(B_115, A_116) | ~l1_pre_topc(A_116))), inference(resolution, [status(thm)], [c_219, c_8])).
% 8.36/3.06  tff(c_224, plain, (![B_117, A_118]: (r1_tarski(u1_struct_0(B_117), u1_struct_0(A_118)) | ~m1_pre_topc(B_117, A_118) | ~l1_pre_topc(A_118))), inference(resolution, [status(thm)], [c_219, c_8])).
% 8.36/3.06  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.36/3.06  tff(c_710, plain, (![B_151, A_152]: (u1_struct_0(B_151)=u1_struct_0(A_152) | ~r1_tarski(u1_struct_0(A_152), u1_struct_0(B_151)) | ~m1_pre_topc(B_151, A_152) | ~l1_pre_topc(A_152))), inference(resolution, [status(thm)], [c_224, c_2])).
% 8.36/3.06  tff(c_808, plain, (![B_158, A_159]: (u1_struct_0(B_158)=u1_struct_0(A_159) | ~m1_pre_topc(A_159, B_158) | ~l1_pre_topc(B_158) | ~m1_pre_topc(B_158, A_159) | ~l1_pre_topc(A_159))), inference(resolution, [status(thm)], [c_223, c_710])).
% 8.36/3.06  tff(c_834, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_808])).
% 8.36/3.06  tff(c_871, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_544, c_68, c_834])).
% 8.36/3.06  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_60, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_764, plain, (![A_155, D_153, F_156, C_157, B_154]: (r1_funct_2(A_155, B_154, C_157, D_153, F_156, F_156) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(C_157, D_153))) | ~v1_funct_2(F_156, C_157, D_153) | ~m1_subset_1(F_156, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))) | ~v1_funct_2(F_156, A_155, B_154) | ~v1_funct_1(F_156) | v1_xboole_0(D_153) | v1_xboole_0(B_154))), inference(cnfTransformation, [status(thm)], [f_122])).
% 8.36/3.06  tff(c_766, plain, (![A_155, B_154]: (r1_funct_2(A_155, B_154, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))) | ~v1_funct_2('#skF_4', A_155, B_154) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_154))), inference(resolution, [status(thm)], [c_58, c_764])).
% 8.36/3.06  tff(c_772, plain, (![A_155, B_154]: (r1_funct_2(A_155, B_154, u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))) | ~v1_funct_2('#skF_4', A_155, B_154) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_154))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_766])).
% 8.36/3.06  tff(c_1670, plain, (![A_155, B_154]: (r1_funct_2(A_155, B_154, u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))) | ~v1_funct_2('#skF_4', A_155, B_154) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_154))), inference(demodulation, [status(thm), theory('equality')], [c_871, c_772])).
% 8.36/3.06  tff(c_1671, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1670])).
% 8.36/3.06  tff(c_26, plain, (![A_21]: (~v1_xboole_0(u1_struct_0(A_21)) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.36/3.06  tff(c_1674, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1671, c_26])).
% 8.36/3.06  tff(c_1677, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_78, c_1674])).
% 8.36/3.06  tff(c_1680, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1677])).
% 8.36/3.06  tff(c_1684, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1680])).
% 8.36/3.06  tff(c_1686, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1670])).
% 8.36/3.06  tff(c_99, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_58, c_8])).
% 8.36/3.06  tff(c_878, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_871, c_99])).
% 8.36/3.06  tff(c_880, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_871, c_60])).
% 8.36/3.06  tff(c_879, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_871, c_58])).
% 8.36/3.06  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.36/3.06  tff(c_1745, plain, (![C_203, A_200, D_199, B_202, A_201]: (r1_funct_2(A_200, B_202, C_203, D_199, A_201, A_201) | ~v1_funct_2(A_201, C_203, D_199) | ~m1_subset_1(A_201, k1_zfmisc_1(k2_zfmisc_1(A_200, B_202))) | ~v1_funct_2(A_201, A_200, B_202) | ~v1_funct_1(A_201) | v1_xboole_0(D_199) | v1_xboole_0(B_202) | ~r1_tarski(A_201, k2_zfmisc_1(C_203, D_199)))), inference(resolution, [status(thm)], [c_10, c_764])).
% 8.36/3.06  tff(c_1747, plain, (![C_203, D_199]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_203, D_199, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_203, D_199) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_199) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_203, D_199)))), inference(resolution, [status(thm)], [c_879, c_1745])).
% 8.36/3.06  tff(c_1753, plain, (![C_203, D_199]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_203, D_199, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_203, D_199) | v1_xboole_0(D_199) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_203, D_199)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_880, c_1747])).
% 8.36/3.06  tff(c_3390, plain, (![C_253, D_254]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_253, D_254, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_253, D_254) | v1_xboole_0(D_254) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_253, D_254)))), inference(negUnitSimplification, [status(thm)], [c_1686, c_1753])).
% 8.36/3.06  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_337, plain, (![A_132, B_133, C_134, D_135]: (k2_partfun1(A_132, B_133, C_134, D_135)=k7_relat_1(C_134, D_135) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))) | ~v1_funct_1(C_134))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.36/3.06  tff(c_339, plain, (![D_135]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_135)=k7_relat_1('#skF_4', D_135) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_337])).
% 8.36/3.06  tff(c_345, plain, (![D_135]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_135)=k7_relat_1('#skF_4', D_135))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_339])).
% 8.36/3.06  tff(c_872, plain, (![D_135]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_135)=k7_relat_1('#skF_4', D_135))), inference(demodulation, [status(thm), theory('equality')], [c_871, c_345])).
% 8.36/3.06  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_1016, plain, (![A_166, B_167, C_168, D_169]: (k2_partfun1(u1_struct_0(A_166), u1_struct_0(B_167), C_168, u1_struct_0(D_169))=k2_tmap_1(A_166, B_167, C_168, D_169) | ~m1_pre_topc(D_169, A_166) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_166), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0(A_166), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_pre_topc(B_167) | ~v2_pre_topc(B_167) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(cnfTransformation, [status(thm)], [f_149])).
% 8.36/3.06  tff(c_1020, plain, (![B_167, C_168, D_169]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_167), C_168, u1_struct_0(D_169))=k2_tmap_1('#skF_2', B_167, C_168, D_169) | ~m1_pre_topc(D_169, '#skF_2') | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0('#skF_2'), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_pre_topc(B_167) | ~v2_pre_topc(B_167) | v2_struct_0(B_167) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_871, c_1016])).
% 8.36/3.06  tff(c_1031, plain, (![B_167, C_168, D_169]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_167), C_168, u1_struct_0(D_169))=k2_tmap_1('#skF_2', B_167, C_168, D_169) | ~m1_pre_topc(D_169, '#skF_2') | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_167)))) | ~v1_funct_2(C_168, u1_struct_0('#skF_3'), u1_struct_0(B_167)) | ~v1_funct_1(C_168) | ~l1_pre_topc(B_167) | ~v2_pre_topc(B_167) | v2_struct_0(B_167) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_871, c_871, c_1020])).
% 8.36/3.06  tff(c_1687, plain, (![B_195, C_196, D_197]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_195), C_196, u1_struct_0(D_197))=k2_tmap_1('#skF_2', B_195, C_196, D_197) | ~m1_pre_topc(D_197, '#skF_2') | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_195)))) | ~v1_funct_2(C_196, u1_struct_0('#skF_3'), u1_struct_0(B_195)) | ~v1_funct_1(C_196) | ~l1_pre_topc(B_195) | ~v2_pre_topc(B_195) | v2_struct_0(B_195))), inference(negUnitSimplification, [status(thm)], [c_72, c_1031])).
% 8.36/3.06  tff(c_1691, plain, (![D_197]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_197))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_197) | ~m1_pre_topc(D_197, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_879, c_1687])).
% 8.36/3.06  tff(c_1701, plain, (![D_197]: (k7_relat_1('#skF_4', u1_struct_0(D_197))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_197) | ~m1_pre_topc(D_197, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_880, c_872, c_1691])).
% 8.36/3.06  tff(c_1756, plain, (![D_204]: (k7_relat_1('#skF_4', u1_struct_0(D_204))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_204) | ~m1_pre_topc(D_204, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_78, c_1701])).
% 8.36/3.06  tff(c_114, plain, (![C_85, A_86, B_87]: (v1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.36/3.06  tff(c_122, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_114])).
% 8.36/3.06  tff(c_158, plain, (![C_101, A_102, B_103]: (v4_relat_1(C_101, A_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.36/3.06  tff(c_166, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_158])).
% 8.36/3.06  tff(c_180, plain, (![B_109, A_110]: (k7_relat_1(B_109, A_110)=B_109 | ~v4_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.36/3.06  tff(c_186, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_166, c_180])).
% 8.36/3.06  tff(c_192, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_122, c_186])).
% 8.36/3.06  tff(c_874, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_871, c_192])).
% 8.36/3.06  tff(c_1762, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1756, c_874])).
% 8.36/3.06  tff(c_1777, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1762])).
% 8.36/3.06  tff(c_54, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 8.36/3.06  tff(c_876, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_871, c_54])).
% 8.36/3.06  tff(c_1785, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1777, c_876])).
% 8.36/3.06  tff(c_3393, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_3390, c_1785])).
% 8.36/3.06  tff(c_3398, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_880, c_3393])).
% 8.36/3.06  tff(c_3400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1686, c_3398])).
% 8.36/3.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.36/3.06  
% 8.36/3.06  Inference rules
% 8.36/3.06  ----------------------
% 8.36/3.06  #Ref     : 0
% 8.36/3.06  #Sup     : 629
% 8.36/3.06  #Fact    : 0
% 8.36/3.06  #Define  : 0
% 8.36/3.06  #Split   : 7
% 8.36/3.06  #Chain   : 0
% 8.36/3.06  #Close   : 0
% 8.36/3.06  
% 8.36/3.06  Ordering : KBO
% 8.36/3.06  
% 8.36/3.06  Simplification rules
% 8.36/3.06  ----------------------
% 8.36/3.06  #Subsume      : 78
% 8.36/3.06  #Demod        : 1261
% 8.36/3.06  #Tautology    : 267
% 8.36/3.06  #SimpNegUnit  : 17
% 8.36/3.06  #BackRed      : 13
% 8.36/3.06  
% 8.36/3.06  #Partial instantiations: 0
% 8.36/3.06  #Strategies tried      : 1
% 8.36/3.06  
% 8.36/3.06  Timing (in seconds)
% 8.36/3.06  ----------------------
% 8.36/3.07  Preprocessing        : 0.60
% 8.36/3.07  Parsing              : 0.31
% 8.36/3.07  CNF conversion       : 0.05
% 8.36/3.07  Main loop            : 1.51
% 8.36/3.07  Inferencing          : 0.48
% 8.36/3.07  Reduction            : 0.57
% 8.36/3.07  Demodulation         : 0.42
% 8.36/3.07  BG Simplification    : 0.06
% 8.36/3.07  Subsumption          : 0.30
% 8.36/3.07  Abstraction          : 0.07
% 8.36/3.07  MUC search           : 0.00
% 8.36/3.07  Cooper               : 0.00
% 8.36/3.07  Total                : 2.20
% 8.36/3.07  Index Insertion      : 0.00
% 8.36/3.07  Index Deletion       : 0.00
% 8.36/3.07  Index Matching       : 0.00
% 8.36/3.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
