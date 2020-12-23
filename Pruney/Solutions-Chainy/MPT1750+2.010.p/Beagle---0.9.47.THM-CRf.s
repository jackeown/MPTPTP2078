%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:52 EST 2020

% Result     : Theorem 4.22s
% Output     : CNFRefutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :  172 (1361 expanded)
%              Number of leaves         :   49 ( 468 expanded)
%              Depth                    :   21
%              Number of atoms          :  395 (5255 expanded)
%              Number of equality atoms :   42 ( 549 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_219,negated_conjecture,(
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

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_172,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_103,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_168,axiom,(
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

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_134,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_161,axiom,(
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

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_30,plain,(
    ! [A_22] :
      ( l1_struct_0(A_22)
      | ~ l1_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_100,plain,(
    ! [B_84,A_85] :
      ( l1_pre_topc(B_84)
      | ~ m1_pre_topc(B_84,A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_106,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_100])).

tff(c_110,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_106])).

tff(c_50,plain,(
    ! [A_57] :
      ( m1_pre_topc(A_57,A_57)
      | ~ l1_pre_topc(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_238,plain,(
    ! [A_125,B_126] :
      ( m1_pre_topc(A_125,g1_pre_topc(u1_struct_0(B_126),u1_pre_topc(B_126)))
      | ~ m1_pre_topc(A_125,B_126)
      | ~ l1_pre_topc(B_126)
      | ~ l1_pre_topc(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_251,plain,(
    ! [A_125] :
      ( m1_pre_topc(A_125,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_125,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_238])).

tff(c_266,plain,(
    ! [A_128] :
      ( m1_pre_topc(A_128,g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_128,'#skF_2')
      | ~ l1_pre_topc(A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_251])).

tff(c_36,plain,(
    ! [B_29,A_27] :
      ( m1_pre_topc(B_29,A_27)
      | ~ m1_pre_topc(B_29,g1_pre_topc(u1_struct_0(A_27),u1_pre_topc(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_272,plain,(
    ! [A_128] :
      ( m1_pre_topc(A_128,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(A_128,'#skF_2')
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_266,c_36])).

tff(c_281,plain,(
    ! [A_129] :
      ( m1_pre_topc(A_129,'#skF_3')
      | ~ m1_pre_topc(A_129,'#skF_2')
      | ~ l1_pre_topc(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_272])).

tff(c_288,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_281])).

tff(c_295,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_288])).

tff(c_212,plain,(
    ! [B_118,A_119] :
      ( m1_subset_1(u1_struct_0(B_118),k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_216,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(u1_struct_0(B_118),u1_struct_0(A_119))
      | ~ m1_pre_topc(B_118,A_119)
      | ~ l1_pre_topc(A_119) ) ),
    inference(resolution,[status(thm)],[c_212,c_8])).

tff(c_217,plain,(
    ! [B_120,A_121] :
      ( r1_tarski(u1_struct_0(B_120),u1_struct_0(A_121))
      | ~ m1_pre_topc(B_120,A_121)
      | ~ l1_pre_topc(A_121) ) ),
    inference(resolution,[status(thm)],[c_212,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_332,plain,(
    ! [B_135,A_136] :
      ( u1_struct_0(B_135) = u1_struct_0(A_136)
      | ~ r1_tarski(u1_struct_0(A_136),u1_struct_0(B_135))
      | ~ m1_pre_topc(B_135,A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_217,c_2])).

tff(c_343,plain,(
    ! [B_137,A_138] :
      ( u1_struct_0(B_137) = u1_struct_0(A_138)
      | ~ m1_pre_topc(A_138,B_137)
      | ~ l1_pre_topc(B_137)
      | ~ m1_pre_topc(B_137,A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_216,c_332])).

tff(c_357,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_343])).

tff(c_374,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_295,c_70,c_357])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_116,plain,(
    ! [C_87,A_88,B_89] :
      ( v1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_148,plain,(
    ! [C_97,A_98,B_99] :
      ( v4_relat_1(C_97,A_98)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_98,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_156,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_148])).

tff(c_197,plain,(
    ! [B_114,A_115] :
      ( k1_relat_1(B_114) = A_115
      | ~ v1_partfun1(B_114,A_115)
      | ~ v4_relat_1(B_114,A_115)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_203,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_156,c_197])).

tff(c_209,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_203])).

tff(c_210,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_378,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_210])).

tff(c_62,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_383,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_62])).

tff(c_382,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_60])).

tff(c_20,plain,(
    ! [C_15,A_12,B_13] :
      ( v1_partfun1(C_15,A_12)
      | ~ v1_funct_2(C_15,A_12,B_13)
      | ~ v1_funct_1(C_15)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13)))
      | v1_xboole_0(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_452,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_382,c_20])).

tff(c_469,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_383,c_452])).

tff(c_470,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_469])).

tff(c_34,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(u1_struct_0(A_26))
      | ~ l1_struct_0(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_483,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_470,c_34])).

tff(c_486,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_483])).

tff(c_489,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_486])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_489])).

tff(c_494,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_500,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_62])).

tff(c_499,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_60])).

tff(c_1325,plain,(
    ! [C_200,B_203,F_201,D_202,A_199] :
      ( r1_funct_2(A_199,B_203,C_200,D_202,F_201,F_201)
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(C_200,D_202)))
      | ~ v1_funct_2(F_201,C_200,D_202)
      | ~ m1_subset_1(F_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_203)))
      | ~ v1_funct_2(F_201,A_199,B_203)
      | ~ v1_funct_1(F_201)
      | v1_xboole_0(D_202)
      | v1_xboole_0(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1327,plain,(
    ! [A_199,B_203] :
      ( r1_funct_2(A_199,B_203,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_199,B_203)))
      | ~ v1_funct_2('#skF_4',A_199,B_203)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_203) ) ),
    inference(resolution,[status(thm)],[c_499,c_1325])).

tff(c_1333,plain,(
    ! [A_199,B_203] :
      ( r1_funct_2(A_199,B_203,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_199,B_203)))
      | ~ v1_funct_2('#skF_4',A_199,B_203)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_203) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_500,c_1327])).

tff(c_1537,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1333])).

tff(c_1540,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1537,c_34])).

tff(c_1543,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1540])).

tff(c_1546,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1543])).

tff(c_1550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1546])).

tff(c_1552,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1333])).

tff(c_115,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_8])).

tff(c_498,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_115])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1804,plain,(
    ! [A_252,B_251,D_250,A_253,C_254] :
      ( r1_funct_2(A_252,B_251,C_254,D_250,A_253,A_253)
      | ~ v1_funct_2(A_253,C_254,D_250)
      | ~ m1_subset_1(A_253,k1_zfmisc_1(k2_zfmisc_1(A_252,B_251)))
      | ~ v1_funct_2(A_253,A_252,B_251)
      | ~ v1_funct_1(A_253)
      | v1_xboole_0(D_250)
      | v1_xboole_0(B_251)
      | ~ r1_tarski(A_253,k2_zfmisc_1(C_254,D_250)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1325])).

tff(c_1806,plain,(
    ! [C_254,D_250] :
      ( r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),C_254,D_250,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_254,D_250)
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_250)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_254,D_250)) ) ),
    inference(resolution,[status(thm)],[c_499,c_1804])).

tff(c_1812,plain,(
    ! [C_254,D_250] :
      ( r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),C_254,D_250,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_254,D_250)
      | v1_xboole_0(D_250)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_254,D_250)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_500,c_1806])).

tff(c_1813,plain,(
    ! [C_254,D_250] :
      ( r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),C_254,D_250,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_254,D_250)
      | v1_xboole_0(D_250)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_254,D_250)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1552,c_1812])).

tff(c_523,plain,(
    ! [B_142,A_143] :
      ( m1_subset_1(u1_struct_0(B_142),k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ m1_pre_topc(B_142,A_143)
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_532,plain,(
    ! [B_142] :
      ( m1_subset_1(u1_struct_0(B_142),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_142,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_523])).

tff(c_585,plain,(
    ! [B_144] :
      ( m1_subset_1(u1_struct_0(B_144),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_144,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_532])).

tff(c_591,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_relat_1('#skF_4')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_585])).

tff(c_612,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_591])).

tff(c_615,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_612])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_615])).

tff(c_621,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_591])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_764,plain,(
    ! [A_162,B_163,C_164,D_165] :
      ( k2_partfun1(A_162,B_163,C_164,D_165) = k7_relat_1(C_164,D_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_162,B_163)))
      | ~ v1_funct_1(C_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_766,plain,(
    ! [D_165] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_165) = k7_relat_1('#skF_4',D_165)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_499,c_764])).

tff(c_772,plain,(
    ! [D_165] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_165) = k7_relat_1('#skF_4',D_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_766])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1609,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( k2_partfun1(u1_struct_0(A_235),u1_struct_0(B_236),C_237,u1_struct_0(D_238)) = k2_tmap_1(A_235,B_236,C_237,D_238)
      | ~ m1_pre_topc(D_238,A_235)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235),u1_struct_0(B_236))))
      | ~ v1_funct_2(C_237,u1_struct_0(A_235),u1_struct_0(B_236))
      | ~ v1_funct_1(C_237)
      | ~ l1_pre_topc(B_236)
      | ~ v2_pre_topc(B_236)
      | v2_struct_0(B_236)
      | ~ l1_pre_topc(A_235)
      | ~ v2_pre_topc(A_235)
      | v2_struct_0(A_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1891,plain,(
    ! [A_263,B_264,A_265,D_266] :
      ( k2_partfun1(u1_struct_0(A_263),u1_struct_0(B_264),A_265,u1_struct_0(D_266)) = k2_tmap_1(A_263,B_264,A_265,D_266)
      | ~ m1_pre_topc(D_266,A_263)
      | ~ v1_funct_2(A_265,u1_struct_0(A_263),u1_struct_0(B_264))
      | ~ v1_funct_1(A_265)
      | ~ l1_pre_topc(B_264)
      | ~ v2_pre_topc(B_264)
      | v2_struct_0(B_264)
      | ~ l1_pre_topc(A_263)
      | ~ v2_pre_topc(A_263)
      | v2_struct_0(A_263)
      | ~ r1_tarski(A_265,k2_zfmisc_1(u1_struct_0(A_263),u1_struct_0(B_264))) ) ),
    inference(resolution,[status(thm)],[c_10,c_1609])).

tff(c_1897,plain,(
    ! [B_264,A_265,D_266] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_264),A_265,u1_struct_0(D_266)) = k2_tmap_1('#skF_2',B_264,A_265,D_266)
      | ~ m1_pre_topc(D_266,'#skF_2')
      | ~ v1_funct_2(A_265,u1_struct_0('#skF_2'),u1_struct_0(B_264))
      | ~ v1_funct_1(A_265)
      | ~ l1_pre_topc(B_264)
      | ~ v2_pre_topc(B_264)
      | v2_struct_0(B_264)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_265,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_264))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_1891])).

tff(c_1910,plain,(
    ! [B_264,A_265,D_266] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_264),A_265,u1_struct_0(D_266)) = k2_tmap_1('#skF_2',B_264,A_265,D_266)
      | ~ m1_pre_topc(D_266,'#skF_2')
      | ~ v1_funct_2(A_265,k1_relat_1('#skF_4'),u1_struct_0(B_264))
      | ~ v1_funct_1(A_265)
      | ~ l1_pre_topc(B_264)
      | ~ v2_pre_topc(B_264)
      | v2_struct_0(B_264)
      | v2_struct_0('#skF_2')
      | ~ r1_tarski(A_265,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_264))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_494,c_494,c_1897])).

tff(c_2015,plain,(
    ! [B_270,A_271,D_272] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_270),A_271,u1_struct_0(D_272)) = k2_tmap_1('#skF_2',B_270,A_271,D_272)
      | ~ m1_pre_topc(D_272,'#skF_2')
      | ~ v1_funct_2(A_271,k1_relat_1('#skF_4'),u1_struct_0(B_270))
      | ~ v1_funct_1(A_271)
      | ~ l1_pre_topc(B_270)
      | ~ v2_pre_topc(B_270)
      | v2_struct_0(B_270)
      | ~ r1_tarski(A_271,k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_270))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1910])).

tff(c_2019,plain,(
    ! [D_272] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_272)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_272)
      | ~ m1_pre_topc(D_272,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_498,c_2015])).

tff(c_2030,plain,(
    ! [D_272] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_272)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_272)
      | ~ m1_pre_topc(D_272,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_64,c_500,c_772,c_2019])).

tff(c_2036,plain,(
    ! [D_273] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_273)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_273)
      | ~ m1_pre_topc(D_273,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2030])).

tff(c_2048,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_2036])).

tff(c_2054,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_621,c_2048])).

tff(c_12,plain,(
    ! [A_5] :
      ( k7_relat_1(A_5,k1_relat_1(A_5)) = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2058,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2054,c_12])).

tff(c_2065,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_2058])).

tff(c_2069,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2065,c_2054])).

tff(c_661,plain,(
    ! [A_153,B_154] :
      ( m1_pre_topc(A_153,g1_pre_topc(u1_struct_0(B_154),u1_pre_topc(B_154)))
      | ~ m1_pre_topc(A_153,B_154)
      | ~ l1_pre_topc(B_154)
      | ~ l1_pre_topc(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_673,plain,(
    ! [A_153] :
      ( m1_pre_topc(A_153,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_153,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ l1_pre_topc(A_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_661])).

tff(c_727,plain,(
    ! [A_160] :
      ( m1_pre_topc(A_160,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ m1_pre_topc(A_160,'#skF_2')
      | ~ l1_pre_topc(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_673])).

tff(c_496,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_58])).

tff(c_625,plain,(
    ! [B_29] :
      ( m1_pre_topc(B_29,'#skF_3')
      | ~ m1_pre_topc(B_29,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_36])).

tff(c_629,plain,(
    ! [B_29] :
      ( m1_pre_topc(B_29,'#skF_3')
      | ~ m1_pre_topc(B_29,g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_625])).

tff(c_740,plain,(
    ! [A_161] :
      ( m1_pre_topc(A_161,'#skF_3')
      | ~ m1_pre_topc(A_161,'#skF_2')
      | ~ l1_pre_topc(A_161) ) ),
    inference(resolution,[status(thm)],[c_727,c_629])).

tff(c_746,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_621,c_740])).

tff(c_757,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_746])).

tff(c_642,plain,(
    ! [B_148,A_149] :
      ( r1_tarski(u1_struct_0(B_148),u1_struct_0(A_149))
      | ~ m1_pre_topc(B_148,A_149)
      | ~ l1_pre_topc(A_149) ) ),
    inference(resolution,[status(thm)],[c_523,c_8])).

tff(c_647,plain,(
    ! [A_149] :
      ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_149))
      | ~ m1_pre_topc('#skF_2',A_149)
      | ~ l1_pre_topc(A_149) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_642])).

tff(c_604,plain,(
    ! [B_147] :
      ( r1_tarski(u1_struct_0(B_147),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc(B_147,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_585,c_8])).

tff(c_796,plain,(
    ! [B_167] :
      ( u1_struct_0(B_167) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(B_167))
      | ~ m1_pre_topc(B_167,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_604,c_2])).

tff(c_806,plain,(
    ! [A_168] :
      ( u1_struct_0(A_168) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc(A_168,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_168)
      | ~ l1_pre_topc(A_168) ) ),
    inference(resolution,[status(thm)],[c_647,c_796])).

tff(c_815,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_806])).

tff(c_825,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_757,c_815])).

tff(c_2045,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_2036])).

tff(c_2052,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2045])).

tff(c_2102,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_2052])).

tff(c_56,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_546,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_494,c_56])).

tff(c_827,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_546])).

tff(c_2103,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2102,c_827])).

tff(c_2110,plain,
    ( ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_1813,c_2103])).

tff(c_2116,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_500,c_2110])).

tff(c_2118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1552,c_2116])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:13:53 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.22/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.76  
% 4.22/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.22/1.76  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.22/1.76  
% 4.22/1.76  %Foreground sorts:
% 4.22/1.76  
% 4.22/1.76  
% 4.22/1.76  %Background operators:
% 4.22/1.76  
% 4.22/1.76  
% 4.22/1.76  %Foreground operators:
% 4.22/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.22/1.76  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.22/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.22/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.22/1.76  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.22/1.76  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.22/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.22/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.22/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.22/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.22/1.76  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 4.22/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.22/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.22/1.76  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.22/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.22/1.76  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.22/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.22/1.76  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.22/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.22/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.22/1.76  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 4.22/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.22/1.76  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.22/1.76  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.22/1.76  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.22/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.22/1.76  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.22/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.22/1.76  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.22/1.76  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.22/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.22/1.76  
% 4.60/1.79  tff(f_219, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 4.60/1.79  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.60/1.79  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.60/1.79  tff(f_172, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.60/1.79  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.60/1.79  tff(f_103, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.60/1.79  tff(f_168, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.60/1.79  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.60/1.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.60/1.79  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.60/1.79  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.60/1.79  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 4.60/1.79  tff(f_63, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 4.60/1.79  tff(f_96, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.60/1.79  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 4.60/1.79  tff(f_77, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 4.60/1.79  tff(f_161, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.60/1.79  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 4.60/1.79  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_30, plain, (![A_22]: (l1_struct_0(A_22) | ~l1_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.60/1.79  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_100, plain, (![B_84, A_85]: (l1_pre_topc(B_84) | ~m1_pre_topc(B_84, A_85) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.60/1.79  tff(c_106, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_66, c_100])).
% 4.60/1.79  tff(c_110, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_106])).
% 4.60/1.79  tff(c_50, plain, (![A_57]: (m1_pre_topc(A_57, A_57) | ~l1_pre_topc(A_57))), inference(cnfTransformation, [status(thm)], [f_172])).
% 4.60/1.79  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_238, plain, (![A_125, B_126]: (m1_pre_topc(A_125, g1_pre_topc(u1_struct_0(B_126), u1_pre_topc(B_126))) | ~m1_pre_topc(A_125, B_126) | ~l1_pre_topc(B_126) | ~l1_pre_topc(A_125))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.79  tff(c_251, plain, (![A_125]: (m1_pre_topc(A_125, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_125, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_125))), inference(superposition, [status(thm), theory('equality')], [c_58, c_238])).
% 4.60/1.79  tff(c_266, plain, (![A_128]: (m1_pre_topc(A_128, g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_128, '#skF_2') | ~l1_pre_topc(A_128))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_251])).
% 4.60/1.79  tff(c_36, plain, (![B_29, A_27]: (m1_pre_topc(B_29, A_27) | ~m1_pre_topc(B_29, g1_pre_topc(u1_struct_0(A_27), u1_pre_topc(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.60/1.79  tff(c_272, plain, (![A_128]: (m1_pre_topc(A_128, '#skF_3') | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(A_128, '#skF_2') | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_266, c_36])).
% 4.60/1.79  tff(c_281, plain, (![A_129]: (m1_pre_topc(A_129, '#skF_3') | ~m1_pre_topc(A_129, '#skF_2') | ~l1_pre_topc(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_272])).
% 4.60/1.79  tff(c_288, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_281])).
% 4.60/1.79  tff(c_295, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_288])).
% 4.60/1.79  tff(c_212, plain, (![B_118, A_119]: (m1_subset_1(u1_struct_0(B_118), k1_zfmisc_1(u1_struct_0(A_119))) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.60/1.79  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.60/1.79  tff(c_216, plain, (![B_118, A_119]: (r1_tarski(u1_struct_0(B_118), u1_struct_0(A_119)) | ~m1_pre_topc(B_118, A_119) | ~l1_pre_topc(A_119))), inference(resolution, [status(thm)], [c_212, c_8])).
% 4.60/1.79  tff(c_217, plain, (![B_120, A_121]: (r1_tarski(u1_struct_0(B_120), u1_struct_0(A_121)) | ~m1_pre_topc(B_120, A_121) | ~l1_pre_topc(A_121))), inference(resolution, [status(thm)], [c_212, c_8])).
% 4.60/1.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.60/1.79  tff(c_332, plain, (![B_135, A_136]: (u1_struct_0(B_135)=u1_struct_0(A_136) | ~r1_tarski(u1_struct_0(A_136), u1_struct_0(B_135)) | ~m1_pre_topc(B_135, A_136) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_217, c_2])).
% 4.60/1.79  tff(c_343, plain, (![B_137, A_138]: (u1_struct_0(B_137)=u1_struct_0(A_138) | ~m1_pre_topc(A_138, B_137) | ~l1_pre_topc(B_137) | ~m1_pre_topc(B_137, A_138) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_216, c_332])).
% 4.60/1.79  tff(c_357, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_343])).
% 4.60/1.79  tff(c_374, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_295, c_70, c_357])).
% 4.60/1.79  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_116, plain, (![C_87, A_88, B_89]: (v1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.60/1.79  tff(c_124, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_116])).
% 4.60/1.79  tff(c_148, plain, (![C_97, A_98, B_99]: (v4_relat_1(C_97, A_98) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_98, B_99))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.60/1.79  tff(c_156, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_60, c_148])).
% 4.60/1.79  tff(c_197, plain, (![B_114, A_115]: (k1_relat_1(B_114)=A_115 | ~v1_partfun1(B_114, A_115) | ~v4_relat_1(B_114, A_115) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.60/1.79  tff(c_203, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_156, c_197])).
% 4.60/1.79  tff(c_209, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_203])).
% 4.60/1.79  tff(c_210, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_209])).
% 4.60/1.79  tff(c_378, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_210])).
% 4.60/1.79  tff(c_62, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_383, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_62])).
% 4.60/1.79  tff(c_382, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_374, c_60])).
% 4.60/1.79  tff(c_20, plain, (![C_15, A_12, B_13]: (v1_partfun1(C_15, A_12) | ~v1_funct_2(C_15, A_12, B_13) | ~v1_funct_1(C_15) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))) | v1_xboole_0(B_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.60/1.79  tff(c_452, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_382, c_20])).
% 4.60/1.79  tff(c_469, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_383, c_452])).
% 4.60/1.79  tff(c_470, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_378, c_469])).
% 4.60/1.79  tff(c_34, plain, (![A_26]: (~v1_xboole_0(u1_struct_0(A_26)) | ~l1_struct_0(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.60/1.79  tff(c_483, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_470, c_34])).
% 4.60/1.79  tff(c_486, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_80, c_483])).
% 4.60/1.79  tff(c_489, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_486])).
% 4.60/1.79  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_489])).
% 4.60/1.79  tff(c_494, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_209])).
% 4.60/1.79  tff(c_500, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_62])).
% 4.60/1.79  tff(c_499, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_60])).
% 4.60/1.79  tff(c_1325, plain, (![C_200, B_203, F_201, D_202, A_199]: (r1_funct_2(A_199, B_203, C_200, D_202, F_201, F_201) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(C_200, D_202))) | ~v1_funct_2(F_201, C_200, D_202) | ~m1_subset_1(F_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_203))) | ~v1_funct_2(F_201, A_199, B_203) | ~v1_funct_1(F_201) | v1_xboole_0(D_202) | v1_xboole_0(B_203))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.60/1.79  tff(c_1327, plain, (![A_199, B_203]: (r1_funct_2(A_199, B_203, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_199, B_203))) | ~v1_funct_2('#skF_4', A_199, B_203) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_203))), inference(resolution, [status(thm)], [c_499, c_1325])).
% 4.60/1.79  tff(c_1333, plain, (![A_199, B_203]: (r1_funct_2(A_199, B_203, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_199, B_203))) | ~v1_funct_2('#skF_4', A_199, B_203) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_203))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_500, c_1327])).
% 4.60/1.79  tff(c_1537, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1333])).
% 4.60/1.79  tff(c_1540, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1537, c_34])).
% 4.60/1.79  tff(c_1543, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_80, c_1540])).
% 4.60/1.79  tff(c_1546, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1543])).
% 4.60/1.79  tff(c_1550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1546])).
% 4.60/1.79  tff(c_1552, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1333])).
% 4.60/1.79  tff(c_115, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_60, c_8])).
% 4.60/1.79  tff(c_498, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_115])).
% 4.60/1.79  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.60/1.79  tff(c_1804, plain, (![A_252, B_251, D_250, A_253, C_254]: (r1_funct_2(A_252, B_251, C_254, D_250, A_253, A_253) | ~v1_funct_2(A_253, C_254, D_250) | ~m1_subset_1(A_253, k1_zfmisc_1(k2_zfmisc_1(A_252, B_251))) | ~v1_funct_2(A_253, A_252, B_251) | ~v1_funct_1(A_253) | v1_xboole_0(D_250) | v1_xboole_0(B_251) | ~r1_tarski(A_253, k2_zfmisc_1(C_254, D_250)))), inference(resolution, [status(thm)], [c_10, c_1325])).
% 4.60/1.79  tff(c_1806, plain, (![C_254, D_250]: (r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), C_254, D_250, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_254, D_250) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_250) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_254, D_250)))), inference(resolution, [status(thm)], [c_499, c_1804])).
% 4.60/1.79  tff(c_1812, plain, (![C_254, D_250]: (r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), C_254, D_250, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_254, D_250) | v1_xboole_0(D_250) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_254, D_250)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_500, c_1806])).
% 4.60/1.79  tff(c_1813, plain, (![C_254, D_250]: (r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), C_254, D_250, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_254, D_250) | v1_xboole_0(D_250) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_254, D_250)))), inference(negUnitSimplification, [status(thm)], [c_1552, c_1812])).
% 4.60/1.79  tff(c_523, plain, (![B_142, A_143]: (m1_subset_1(u1_struct_0(B_142), k1_zfmisc_1(u1_struct_0(A_143))) | ~m1_pre_topc(B_142, A_143) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.60/1.79  tff(c_532, plain, (![B_142]: (m1_subset_1(u1_struct_0(B_142), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_142, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_494, c_523])).
% 4.60/1.79  tff(c_585, plain, (![B_144]: (m1_subset_1(u1_struct_0(B_144), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_144, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_532])).
% 4.60/1.79  tff(c_591, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_494, c_585])).
% 4.60/1.79  tff(c_612, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_591])).
% 4.60/1.79  tff(c_615, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_612])).
% 4.60/1.79  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_615])).
% 4.60/1.79  tff(c_621, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_591])).
% 4.60/1.79  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_764, plain, (![A_162, B_163, C_164, D_165]: (k2_partfun1(A_162, B_163, C_164, D_165)=k7_relat_1(C_164, D_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_162, B_163))) | ~v1_funct_1(C_164))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.60/1.79  tff(c_766, plain, (![D_165]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_165)=k7_relat_1('#skF_4', D_165) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_499, c_764])).
% 4.60/1.79  tff(c_772, plain, (![D_165]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_165)=k7_relat_1('#skF_4', D_165))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_766])).
% 4.60/1.79  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_1609, plain, (![A_235, B_236, C_237, D_238]: (k2_partfun1(u1_struct_0(A_235), u1_struct_0(B_236), C_237, u1_struct_0(D_238))=k2_tmap_1(A_235, B_236, C_237, D_238) | ~m1_pre_topc(D_238, A_235) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_235), u1_struct_0(B_236)))) | ~v1_funct_2(C_237, u1_struct_0(A_235), u1_struct_0(B_236)) | ~v1_funct_1(C_237) | ~l1_pre_topc(B_236) | ~v2_pre_topc(B_236) | v2_struct_0(B_236) | ~l1_pre_topc(A_235) | ~v2_pre_topc(A_235) | v2_struct_0(A_235))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.60/1.79  tff(c_1891, plain, (![A_263, B_264, A_265, D_266]: (k2_partfun1(u1_struct_0(A_263), u1_struct_0(B_264), A_265, u1_struct_0(D_266))=k2_tmap_1(A_263, B_264, A_265, D_266) | ~m1_pre_topc(D_266, A_263) | ~v1_funct_2(A_265, u1_struct_0(A_263), u1_struct_0(B_264)) | ~v1_funct_1(A_265) | ~l1_pre_topc(B_264) | ~v2_pre_topc(B_264) | v2_struct_0(B_264) | ~l1_pre_topc(A_263) | ~v2_pre_topc(A_263) | v2_struct_0(A_263) | ~r1_tarski(A_265, k2_zfmisc_1(u1_struct_0(A_263), u1_struct_0(B_264))))), inference(resolution, [status(thm)], [c_10, c_1609])).
% 4.60/1.79  tff(c_1897, plain, (![B_264, A_265, D_266]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_264), A_265, u1_struct_0(D_266))=k2_tmap_1('#skF_2', B_264, A_265, D_266) | ~m1_pre_topc(D_266, '#skF_2') | ~v1_funct_2(A_265, u1_struct_0('#skF_2'), u1_struct_0(B_264)) | ~v1_funct_1(A_265) | ~l1_pre_topc(B_264) | ~v2_pre_topc(B_264) | v2_struct_0(B_264) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~r1_tarski(A_265, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_264))))), inference(superposition, [status(thm), theory('equality')], [c_494, c_1891])).
% 4.60/1.79  tff(c_1910, plain, (![B_264, A_265, D_266]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_264), A_265, u1_struct_0(D_266))=k2_tmap_1('#skF_2', B_264, A_265, D_266) | ~m1_pre_topc(D_266, '#skF_2') | ~v1_funct_2(A_265, k1_relat_1('#skF_4'), u1_struct_0(B_264)) | ~v1_funct_1(A_265) | ~l1_pre_topc(B_264) | ~v2_pre_topc(B_264) | v2_struct_0(B_264) | v2_struct_0('#skF_2') | ~r1_tarski(A_265, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_264))))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_494, c_494, c_1897])).
% 4.60/1.79  tff(c_2015, plain, (![B_270, A_271, D_272]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_270), A_271, u1_struct_0(D_272))=k2_tmap_1('#skF_2', B_270, A_271, D_272) | ~m1_pre_topc(D_272, '#skF_2') | ~v1_funct_2(A_271, k1_relat_1('#skF_4'), u1_struct_0(B_270)) | ~v1_funct_1(A_271) | ~l1_pre_topc(B_270) | ~v2_pre_topc(B_270) | v2_struct_0(B_270) | ~r1_tarski(A_271, k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_270))))), inference(negUnitSimplification, [status(thm)], [c_74, c_1910])).
% 4.60/1.79  tff(c_2019, plain, (![D_272]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_272))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_272) | ~m1_pre_topc(D_272, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_498, c_2015])).
% 4.60/1.79  tff(c_2030, plain, (![D_272]: (k7_relat_1('#skF_4', u1_struct_0(D_272))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_272) | ~m1_pre_topc(D_272, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_64, c_500, c_772, c_2019])).
% 4.60/1.79  tff(c_2036, plain, (![D_273]: (k7_relat_1('#skF_4', u1_struct_0(D_273))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_273) | ~m1_pre_topc(D_273, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_80, c_2030])).
% 4.60/1.79  tff(c_2048, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_494, c_2036])).
% 4.60/1.79  tff(c_2054, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_621, c_2048])).
% 4.60/1.79  tff(c_12, plain, (![A_5]: (k7_relat_1(A_5, k1_relat_1(A_5))=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.60/1.79  tff(c_2058, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2054, c_12])).
% 4.60/1.79  tff(c_2065, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_2058])).
% 4.60/1.79  tff(c_2069, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2065, c_2054])).
% 4.60/1.79  tff(c_661, plain, (![A_153, B_154]: (m1_pre_topc(A_153, g1_pre_topc(u1_struct_0(B_154), u1_pre_topc(B_154))) | ~m1_pre_topc(A_153, B_154) | ~l1_pre_topc(B_154) | ~l1_pre_topc(A_153))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.60/1.79  tff(c_673, plain, (![A_153]: (m1_pre_topc(A_153, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_153, '#skF_2') | ~l1_pre_topc('#skF_2') | ~l1_pre_topc(A_153))), inference(superposition, [status(thm), theory('equality')], [c_494, c_661])).
% 4.60/1.79  tff(c_727, plain, (![A_160]: (m1_pre_topc(A_160, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc(A_160, '#skF_2') | ~l1_pre_topc(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_673])).
% 4.60/1.79  tff(c_496, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_58])).
% 4.60/1.79  tff(c_625, plain, (![B_29]: (m1_pre_topc(B_29, '#skF_3') | ~m1_pre_topc(B_29, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_496, c_36])).
% 4.60/1.79  tff(c_629, plain, (![B_29]: (m1_pre_topc(B_29, '#skF_3') | ~m1_pre_topc(B_29, g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_625])).
% 4.60/1.79  tff(c_740, plain, (![A_161]: (m1_pre_topc(A_161, '#skF_3') | ~m1_pre_topc(A_161, '#skF_2') | ~l1_pre_topc(A_161))), inference(resolution, [status(thm)], [c_727, c_629])).
% 4.60/1.79  tff(c_746, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_621, c_740])).
% 4.60/1.79  tff(c_757, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_746])).
% 4.60/1.79  tff(c_642, plain, (![B_148, A_149]: (r1_tarski(u1_struct_0(B_148), u1_struct_0(A_149)) | ~m1_pre_topc(B_148, A_149) | ~l1_pre_topc(A_149))), inference(resolution, [status(thm)], [c_523, c_8])).
% 4.60/1.79  tff(c_647, plain, (![A_149]: (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_149)) | ~m1_pre_topc('#skF_2', A_149) | ~l1_pre_topc(A_149))), inference(superposition, [status(thm), theory('equality')], [c_494, c_642])).
% 4.60/1.79  tff(c_604, plain, (![B_147]: (r1_tarski(u1_struct_0(B_147), k1_relat_1('#skF_4')) | ~m1_pre_topc(B_147, '#skF_2'))), inference(resolution, [status(thm)], [c_585, c_8])).
% 4.60/1.79  tff(c_796, plain, (![B_167]: (u1_struct_0(B_167)=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(B_167)) | ~m1_pre_topc(B_167, '#skF_2'))), inference(resolution, [status(thm)], [c_604, c_2])).
% 4.60/1.79  tff(c_806, plain, (![A_168]: (u1_struct_0(A_168)=k1_relat_1('#skF_4') | ~m1_pre_topc(A_168, '#skF_2') | ~m1_pre_topc('#skF_2', A_168) | ~l1_pre_topc(A_168))), inference(resolution, [status(thm)], [c_647, c_796])).
% 4.60/1.79  tff(c_815, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_806])).
% 4.60/1.79  tff(c_825, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_757, c_815])).
% 4.60/1.79  tff(c_2045, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_825, c_2036])).
% 4.60/1.79  tff(c_2052, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2045])).
% 4.60/1.79  tff(c_2102, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_2052])).
% 4.60/1.79  tff(c_56, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 4.60/1.79  tff(c_546, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_494, c_56])).
% 4.60/1.79  tff(c_827, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_825, c_546])).
% 4.60/1.79  tff(c_2103, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2102, c_827])).
% 4.60/1.79  tff(c_2110, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_1813, c_2103])).
% 4.60/1.79  tff(c_2116, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_498, c_500, c_2110])).
% 4.60/1.79  tff(c_2118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1552, c_2116])).
% 4.60/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.79  
% 4.60/1.79  Inference rules
% 4.60/1.79  ----------------------
% 4.60/1.79  #Ref     : 0
% 4.60/1.79  #Sup     : 409
% 4.60/1.79  #Fact    : 0
% 4.60/1.79  #Define  : 0
% 4.60/1.79  #Split   : 10
% 4.60/1.79  #Chain   : 0
% 4.60/1.79  #Close   : 0
% 4.60/1.79  
% 4.60/1.79  Ordering : KBO
% 4.60/1.79  
% 4.60/1.79  Simplification rules
% 4.60/1.79  ----------------------
% 4.60/1.79  #Subsume      : 102
% 4.60/1.79  #Demod        : 622
% 4.60/1.79  #Tautology    : 171
% 4.60/1.79  #SimpNegUnit  : 24
% 4.60/1.79  #BackRed      : 22
% 4.60/1.79  
% 4.60/1.79  #Partial instantiations: 0
% 4.60/1.79  #Strategies tried      : 1
% 4.60/1.79  
% 4.60/1.79  Timing (in seconds)
% 4.60/1.79  ----------------------
% 4.60/1.79  Preprocessing        : 0.37
% 4.60/1.79  Parsing              : 0.20
% 4.60/1.79  CNF conversion       : 0.03
% 4.60/1.79  Main loop            : 0.63
% 4.60/1.79  Inferencing          : 0.20
% 4.60/1.79  Reduction            : 0.23
% 4.60/1.79  Demodulation         : 0.17
% 4.60/1.79  BG Simplification    : 0.03
% 4.60/1.79  Subsumption          : 0.12
% 4.60/1.79  Abstraction          : 0.03
% 4.60/1.79  MUC search           : 0.00
% 4.60/1.79  Cooper               : 0.00
% 4.60/1.79  Total                : 1.05
% 4.60/1.79  Index Insertion      : 0.00
% 4.60/1.79  Index Deletion       : 0.00
% 4.60/1.79  Index Matching       : 0.00
% 4.60/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
