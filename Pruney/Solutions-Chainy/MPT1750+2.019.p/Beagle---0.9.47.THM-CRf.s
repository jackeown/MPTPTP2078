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
% DateTime   : Thu Dec  3 10:26:54 EST 2020

% Result     : Theorem 6.35s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 717 expanded)
%              Number of leaves         :   49 ( 265 expanded)
%              Depth                    :   19
%              Number of atoms          :  309 (2865 expanded)
%              Number of equality atoms :   31 ( 258 expanded)
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

tff(f_212,negated_conjecture,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_175,axiom,(
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

tff(f_78,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_179,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_168,axiom,(
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

tff(f_86,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_26,plain,(
    ! [A_19] :
      ( l1_struct_0(A_19)
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_83,plain,(
    ! [B_75,A_76] :
      ( l1_pre_topc(B_75)
      | ~ m1_pre_topc(B_75,A_76)
      | ~ l1_pre_topc(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_89,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_83])).

tff(c_93,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_89])).

tff(c_281,plain,(
    ! [B_127,A_128] :
      ( m1_subset_1(u1_struct_0(B_127),k1_zfmisc_1(u1_struct_0(A_128)))
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_285,plain,(
    ! [B_127,A_128] :
      ( r1_tarski(u1_struct_0(B_127),u1_struct_0(A_128))
      | ~ m1_pre_topc(B_127,A_128)
      | ~ l1_pre_topc(A_128) ) ),
    inference(resolution,[status(thm)],[c_281,c_8])).

tff(c_286,plain,(
    ! [B_129,A_130] :
      ( r1_tarski(u1_struct_0(B_129),u1_struct_0(A_130))
      | ~ m1_pre_topc(B_129,A_130)
      | ~ l1_pre_topc(A_130) ) ),
    inference(resolution,[status(thm)],[c_281,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_316,plain,(
    ! [B_135,A_136] :
      ( u1_struct_0(B_135) = u1_struct_0(A_136)
      | ~ r1_tarski(u1_struct_0(A_136),u1_struct_0(B_135))
      | ~ m1_pre_topc(B_135,A_136)
      | ~ l1_pre_topc(A_136) ) ),
    inference(resolution,[status(thm)],[c_286,c_2])).

tff(c_327,plain,(
    ! [B_137,A_138] :
      ( u1_struct_0(B_137) = u1_struct_0(A_138)
      | ~ m1_pre_topc(A_138,B_137)
      | ~ l1_pre_topc(B_137)
      | ~ m1_pre_topc(B_137,A_138)
      | ~ l1_pre_topc(A_138) ) ),
    inference(resolution,[status(thm)],[c_285,c_316])).

tff(c_333,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_327])).

tff(c_341,plain,
    ( u1_struct_0('#skF_2') = u1_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_68,c_333])).

tff(c_342,plain,(
    ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_56,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_30,plain,(
    ! [A_23] :
      ( m1_subset_1(u1_pre_topc(A_23),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_23))))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_225,plain,(
    ! [A_112,B_113] :
      ( l1_pre_topc(g1_pre_topc(A_112,B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(k1_zfmisc_1(A_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_235,plain,(
    ! [A_114] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(A_114),u1_pre_topc(A_114)))
      | ~ l1_pre_topc(A_114) ) ),
    inference(resolution,[status(thm)],[c_30,c_225])).

tff(c_238,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_235])).

tff(c_240,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_238])).

tff(c_52,plain,(
    ! [A_60] :
      ( m1_pre_topc(A_60,A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_290,plain,(
    ! [B_131,A_132] :
      ( m1_pre_topc(B_131,A_132)
      | ~ m1_pre_topc(B_131,g1_pre_topc(u1_struct_0(A_132),u1_pre_topc(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_300,plain,(
    ! [A_132] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(A_132),u1_pre_topc(A_132)),A_132)
      | ~ l1_pre_topc(A_132)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(A_132),u1_pre_topc(A_132))) ) ),
    inference(resolution,[status(thm)],[c_52,c_290])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_275,plain,(
    ! [A_126] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_126),u1_pre_topc(A_126)))
      | ~ l1_pre_topc(A_126)
      | ~ v2_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_278,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_275])).

tff(c_280,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_278])).

tff(c_520,plain,(
    ! [C_158,A_159] :
      ( m1_pre_topc(C_158,A_159)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_158),u1_pre_topc(C_158)),A_159)
      | ~ l1_pre_topc(C_158)
      | ~ v2_pre_topc(C_158)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_158),u1_pre_topc(C_158)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_158),u1_pre_topc(C_158)))
      | ~ l1_pre_topc(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_538,plain,(
    ! [A_159] :
      ( m1_pre_topc('#skF_2',A_159)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_159)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_520])).

tff(c_558,plain,(
    ! [A_160] :
      ( m1_pre_topc('#skF_2',A_160)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_56,c_240,c_56,c_70,c_68,c_538])).

tff(c_569,plain,
    ( m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_300,c_558])).

tff(c_583,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_93,c_569])).

tff(c_585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_342,c_583])).

tff(c_586,plain,(
    u1_struct_0('#skF_2') = u1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_60,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_616,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_60])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_615,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_58])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_864,plain,(
    ! [B_172,F_174,D_171,C_175,A_173] :
      ( r1_funct_2(A_173,B_172,C_175,D_171,F_174,F_174)
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(C_175,D_171)))
      | ~ v1_funct_2(F_174,C_175,D_171)
      | ~ m1_subset_1(F_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_172)))
      | ~ v1_funct_2(F_174,A_173,B_172)
      | ~ v1_funct_1(F_174)
      | v1_xboole_0(D_171)
      | v1_xboole_0(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1539,plain,(
    ! [A_213,B_216,D_214,A_215,C_212] :
      ( r1_funct_2(A_213,B_216,C_212,D_214,A_215,A_215)
      | ~ v1_funct_2(A_215,C_212,D_214)
      | ~ m1_subset_1(A_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_216)))
      | ~ v1_funct_2(A_215,A_213,B_216)
      | ~ v1_funct_1(A_215)
      | v1_xboole_0(D_214)
      | v1_xboole_0(B_216)
      | ~ r1_tarski(A_215,k2_zfmisc_1(C_212,D_214)) ) ),
    inference(resolution,[status(thm)],[c_10,c_864])).

tff(c_1541,plain,(
    ! [C_212,D_214] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_212,D_214,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_212,D_214)
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_214)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_212,D_214)) ) ),
    inference(resolution,[status(thm)],[c_615,c_1539])).

tff(c_1547,plain,(
    ! [C_212,D_214] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_212,D_214,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_212,D_214)
      | v1_xboole_0(D_214)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_212,D_214)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_616,c_1541])).

tff(c_4092,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1547])).

tff(c_32,plain,(
    ! [A_24] :
      ( ~ v1_xboole_0(u1_struct_0(A_24))
      | ~ l1_struct_0(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4095,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4092,c_32])).

tff(c_4098,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4095])).

tff(c_4101,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_4098])).

tff(c_4105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4101])).

tff(c_4107,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1547])).

tff(c_114,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_8])).

tff(c_614,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_114])).

tff(c_4177,plain,(
    ! [C_270,D_271] :
      ( r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),C_270,D_271,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_270,D_271)
      | v1_xboole_0(D_271)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_270,D_271)) ) ),
    inference(splitRight,[status(thm)],[c_1547])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_588,plain,(
    ! [A_161,B_162,C_163,D_164] :
      ( k2_partfun1(A_161,B_162,C_163,D_164) = k7_relat_1(C_163,D_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_funct_1(C_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_590,plain,(
    ! [D_164] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_164) = k7_relat_1('#skF_4',D_164)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_58,c_588])).

tff(c_596,plain,(
    ! [D_164] : k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),'#skF_4',D_164) = k7_relat_1('#skF_4',D_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_590])).

tff(c_890,plain,(
    ! [D_164] : k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',D_164) = k7_relat_1('#skF_4',D_164) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_596])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_1029,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k2_partfun1(u1_struct_0(A_189),u1_struct_0(B_190),C_191,u1_struct_0(D_192)) = k2_tmap_1(A_189,B_190,C_191,D_192)
      | ~ m1_pre_topc(D_192,A_189)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_189),u1_struct_0(B_190))))
      | ~ v1_funct_2(C_191,u1_struct_0(A_189),u1_struct_0(B_190))
      | ~ v1_funct_1(C_191)
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc(A_189)
      | ~ v2_pre_topc(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_1033,plain,(
    ! [B_190,C_191,D_192] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_190),C_191,u1_struct_0(D_192)) = k2_tmap_1('#skF_2',B_190,C_191,D_192)
      | ~ m1_pre_topc(D_192,'#skF_2')
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_190))))
      | ~ v1_funct_2(C_191,u1_struct_0('#skF_2'),u1_struct_0(B_190))
      | ~ v1_funct_1(C_191)
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_586,c_1029])).

tff(c_1044,plain,(
    ! [B_190,C_191,D_192] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_190),C_191,u1_struct_0(D_192)) = k2_tmap_1('#skF_2',B_190,C_191,D_192)
      | ~ m1_pre_topc(D_192,'#skF_2')
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_190))))
      | ~ v1_funct_2(C_191,u1_struct_0('#skF_3'),u1_struct_0(B_190))
      | ~ v1_funct_1(C_191)
      | ~ l1_pre_topc(B_190)
      | ~ v2_pre_topc(B_190)
      | v2_struct_0(B_190)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_586,c_586,c_1033])).

tff(c_1439,plain,(
    ! [B_207,C_208,D_209] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0(B_207),C_208,u1_struct_0(D_209)) = k2_tmap_1('#skF_2',B_207,C_208,D_209)
      | ~ m1_pre_topc(D_209,'#skF_2')
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_207))))
      | ~ v1_funct_2(C_208,u1_struct_0('#skF_3'),u1_struct_0(B_207))
      | ~ v1_funct_1(C_208)
      | ~ l1_pre_topc(B_207)
      | ~ v2_pre_topc(B_207)
      | v2_struct_0(B_207) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1044])).

tff(c_1443,plain,(
    ! [D_209] :
      ( k2_partfun1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_209)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_209)
      | ~ m1_pre_topc(D_209,'#skF_2')
      | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_615,c_1439])).

tff(c_1453,plain,(
    ! [D_209] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_209)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_209)
      | ~ m1_pre_topc(D_209,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_616,c_890,c_1443])).

tff(c_1500,plain,(
    ! [D_211] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_211)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_211)
      | ~ m1_pre_topc(D_211,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1453])).

tff(c_14,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_113,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_14])).

tff(c_138,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_146,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_58,c_138])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k7_relat_1(B_6,A_5) = B_6
      | ~ v4_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_150,plain,
    ( k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_12])).

tff(c_153,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_150])).

tff(c_612,plain,(
    k7_relat_1('#skF_4',u1_struct_0('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_153])).

tff(c_1506,plain,
    ( k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4'
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1500,c_612])).

tff(c_1521,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1506])).

tff(c_54,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_610,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_54])).

tff(c_1529,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1521,c_610])).

tff(c_4180,plain,
    ( ~ v1_funct_2('#skF_4',u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_4177,c_1529])).

tff(c_4185,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_616,c_4180])).

tff(c_4187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4107,c_4185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.09/0.28  % Computer   : n014.cluster.edu
% 0.09/0.28  % Model      : x86_64 x86_64
% 0.09/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.28  % Memory     : 8042.1875MB
% 0.09/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % DateTime   : Tue Dec  1 12:03:22 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.13/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.35/2.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.35/2.27  
% 6.35/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.35/2.27  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.35/2.27  
% 6.35/2.27  %Foreground sorts:
% 6.35/2.27  
% 6.35/2.27  
% 6.35/2.27  %Background operators:
% 6.35/2.27  
% 6.35/2.27  
% 6.35/2.27  %Foreground operators:
% 6.35/2.27  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.35/2.27  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.35/2.27  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.35/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.35/2.27  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.35/2.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.35/2.27  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.35/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.35/2.27  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.35/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.35/2.27  tff('#skF_3', type, '#skF_3': $i).
% 6.35/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.35/2.27  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.35/2.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.35/2.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.35/2.27  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.35/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.35/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.35/2.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.35/2.27  tff('#skF_4', type, '#skF_4': $i).
% 6.35/2.27  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 6.35/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.35/2.27  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.35/2.27  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.35/2.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.35/2.27  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.35/2.27  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 6.35/2.27  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.35/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.35/2.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.35/2.27  
% 6.62/2.29  tff(f_212, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_tmap_1)).
% 6.62/2.29  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.62/2.29  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.62/2.29  tff(f_175, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.62/2.29  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.62/2.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.62/2.29  tff(f_78, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 6.62/2.29  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 6.62/2.29  tff(f_179, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.62/2.29  tff(f_101, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 6.62/2.29  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 6.62/2.29  tff(f_168, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 6.62/2.29  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 6.62/2.29  tff(f_86, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 6.62/2.29  tff(f_57, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.62/2.29  tff(f_150, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 6.62/2.29  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.62/2.29  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.62/2.29  tff(f_41, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 6.62/2.29  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_26, plain, (![A_19]: (l1_struct_0(A_19) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.62/2.29  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_83, plain, (![B_75, A_76]: (l1_pre_topc(B_75) | ~m1_pre_topc(B_75, A_76) | ~l1_pre_topc(A_76))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.62/2.29  tff(c_89, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_83])).
% 6.62/2.29  tff(c_93, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_89])).
% 6.62/2.29  tff(c_281, plain, (![B_127, A_128]: (m1_subset_1(u1_struct_0(B_127), k1_zfmisc_1(u1_struct_0(A_128))) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128))), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.62/2.29  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.62/2.29  tff(c_285, plain, (![B_127, A_128]: (r1_tarski(u1_struct_0(B_127), u1_struct_0(A_128)) | ~m1_pre_topc(B_127, A_128) | ~l1_pre_topc(A_128))), inference(resolution, [status(thm)], [c_281, c_8])).
% 6.62/2.29  tff(c_286, plain, (![B_129, A_130]: (r1_tarski(u1_struct_0(B_129), u1_struct_0(A_130)) | ~m1_pre_topc(B_129, A_130) | ~l1_pre_topc(A_130))), inference(resolution, [status(thm)], [c_281, c_8])).
% 6.62/2.29  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.62/2.29  tff(c_316, plain, (![B_135, A_136]: (u1_struct_0(B_135)=u1_struct_0(A_136) | ~r1_tarski(u1_struct_0(A_136), u1_struct_0(B_135)) | ~m1_pre_topc(B_135, A_136) | ~l1_pre_topc(A_136))), inference(resolution, [status(thm)], [c_286, c_2])).
% 6.62/2.29  tff(c_327, plain, (![B_137, A_138]: (u1_struct_0(B_137)=u1_struct_0(A_138) | ~m1_pre_topc(A_138, B_137) | ~l1_pre_topc(B_137) | ~m1_pre_topc(B_137, A_138) | ~l1_pre_topc(A_138))), inference(resolution, [status(thm)], [c_285, c_316])).
% 6.62/2.29  tff(c_333, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_64, c_327])).
% 6.62/2.29  tff(c_341, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_68, c_333])).
% 6.62/2.29  tff(c_342, plain, (~m1_pre_topc('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_341])).
% 6.62/2.29  tff(c_56, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_30, plain, (![A_23]: (m1_subset_1(u1_pre_topc(A_23), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_23)))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.62/2.29  tff(c_225, plain, (![A_112, B_113]: (l1_pre_topc(g1_pre_topc(A_112, B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1(k1_zfmisc_1(A_112))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.62/2.29  tff(c_235, plain, (![A_114]: (l1_pre_topc(g1_pre_topc(u1_struct_0(A_114), u1_pre_topc(A_114))) | ~l1_pre_topc(A_114))), inference(resolution, [status(thm)], [c_30, c_225])).
% 6.62/2.29  tff(c_238, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_235])).
% 6.62/2.29  tff(c_240, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_238])).
% 6.62/2.29  tff(c_52, plain, (![A_60]: (m1_pre_topc(A_60, A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_179])).
% 6.62/2.29  tff(c_290, plain, (![B_131, A_132]: (m1_pre_topc(B_131, A_132) | ~m1_pre_topc(B_131, g1_pre_topc(u1_struct_0(A_132), u1_pre_topc(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.62/2.29  tff(c_300, plain, (![A_132]: (m1_pre_topc(g1_pre_topc(u1_struct_0(A_132), u1_pre_topc(A_132)), A_132) | ~l1_pre_topc(A_132) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(A_132), u1_pre_topc(A_132))))), inference(resolution, [status(thm)], [c_52, c_290])).
% 6.62/2.29  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_275, plain, (![A_126]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_126), u1_pre_topc(A_126))) | ~l1_pre_topc(A_126) | ~v2_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.62/2.29  tff(c_278, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_56, c_275])).
% 6.62/2.29  tff(c_280, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_278])).
% 6.62/2.29  tff(c_520, plain, (![C_158, A_159]: (m1_pre_topc(C_158, A_159) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_158), u1_pre_topc(C_158)), A_159) | ~l1_pre_topc(C_158) | ~v2_pre_topc(C_158) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_158), u1_pre_topc(C_158))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_158), u1_pre_topc(C_158))) | ~l1_pre_topc(A_159))), inference(cnfTransformation, [status(thm)], [f_168])).
% 6.62/2.29  tff(c_538, plain, (![A_159]: (m1_pre_topc('#skF_2', A_159) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_159) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_159))), inference(superposition, [status(thm), theory('equality')], [c_56, c_520])).
% 6.62/2.29  tff(c_558, plain, (![A_160]: (m1_pre_topc('#skF_2', A_160) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_160) | ~l1_pre_topc(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_56, c_240, c_56, c_70, c_68, c_538])).
% 6.62/2.29  tff(c_569, plain, (m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3')))), inference(resolution, [status(thm)], [c_300, c_558])).
% 6.62/2.29  tff(c_583, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_240, c_93, c_569])).
% 6.62/2.29  tff(c_585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_342, c_583])).
% 6.62/2.29  tff(c_586, plain, (u1_struct_0('#skF_2')=u1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_341])).
% 6.62/2.29  tff(c_60, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_616, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_60])).
% 6.62/2.29  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_615, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_58])).
% 6.62/2.29  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.62/2.29  tff(c_864, plain, (![B_172, F_174, D_171, C_175, A_173]: (r1_funct_2(A_173, B_172, C_175, D_171, F_174, F_174) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(C_175, D_171))) | ~v1_funct_2(F_174, C_175, D_171) | ~m1_subset_1(F_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_172))) | ~v1_funct_2(F_174, A_173, B_172) | ~v1_funct_1(F_174) | v1_xboole_0(D_171) | v1_xboole_0(B_172))), inference(cnfTransformation, [status(thm)], [f_123])).
% 6.62/2.29  tff(c_1539, plain, (![A_213, B_216, D_214, A_215, C_212]: (r1_funct_2(A_213, B_216, C_212, D_214, A_215, A_215) | ~v1_funct_2(A_215, C_212, D_214) | ~m1_subset_1(A_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_216))) | ~v1_funct_2(A_215, A_213, B_216) | ~v1_funct_1(A_215) | v1_xboole_0(D_214) | v1_xboole_0(B_216) | ~r1_tarski(A_215, k2_zfmisc_1(C_212, D_214)))), inference(resolution, [status(thm)], [c_10, c_864])).
% 6.62/2.29  tff(c_1541, plain, (![C_212, D_214]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_212, D_214, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_212, D_214) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_214) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_212, D_214)))), inference(resolution, [status(thm)], [c_615, c_1539])).
% 6.62/2.29  tff(c_1547, plain, (![C_212, D_214]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_212, D_214, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_212, D_214) | v1_xboole_0(D_214) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_212, D_214)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_616, c_1541])).
% 6.62/2.29  tff(c_4092, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1547])).
% 6.62/2.29  tff(c_32, plain, (![A_24]: (~v1_xboole_0(u1_struct_0(A_24)) | ~l1_struct_0(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.62/2.29  tff(c_4095, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4092, c_32])).
% 6.62/2.29  tff(c_4098, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_78, c_4095])).
% 6.62/2.29  tff(c_4101, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_26, c_4098])).
% 6.62/2.29  tff(c_4105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_4101])).
% 6.62/2.29  tff(c_4107, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_1547])).
% 6.62/2.29  tff(c_114, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_58, c_8])).
% 6.62/2.29  tff(c_614, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_114])).
% 6.62/2.29  tff(c_4177, plain, (![C_270, D_271]: (r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), C_270, D_271, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_270, D_271) | v1_xboole_0(D_271) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_270, D_271)))), inference(splitRight, [status(thm)], [c_1547])).
% 6.62/2.29  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_588, plain, (![A_161, B_162, C_163, D_164]: (k2_partfun1(A_161, B_162, C_163, D_164)=k7_relat_1(C_163, D_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_funct_1(C_163))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.62/2.29  tff(c_590, plain, (![D_164]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_164)=k7_relat_1('#skF_4', D_164) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_58, c_588])).
% 6.62/2.29  tff(c_596, plain, (![D_164]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), '#skF_4', D_164)=k7_relat_1('#skF_4', D_164))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_590])).
% 6.62/2.29  tff(c_890, plain, (![D_164]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', D_164)=k7_relat_1('#skF_4', D_164))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_596])).
% 6.62/2.29  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_1029, plain, (![A_189, B_190, C_191, D_192]: (k2_partfun1(u1_struct_0(A_189), u1_struct_0(B_190), C_191, u1_struct_0(D_192))=k2_tmap_1(A_189, B_190, C_191, D_192) | ~m1_pre_topc(D_192, A_189) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_189), u1_struct_0(B_190)))) | ~v1_funct_2(C_191, u1_struct_0(A_189), u1_struct_0(B_190)) | ~v1_funct_1(C_191) | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | ~l1_pre_topc(A_189) | ~v2_pre_topc(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.62/2.29  tff(c_1033, plain, (![B_190, C_191, D_192]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_190), C_191, u1_struct_0(D_192))=k2_tmap_1('#skF_2', B_190, C_191, D_192) | ~m1_pre_topc(D_192, '#skF_2') | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_190)))) | ~v1_funct_2(C_191, u1_struct_0('#skF_2'), u1_struct_0(B_190)) | ~v1_funct_1(C_191) | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_586, c_1029])).
% 6.62/2.29  tff(c_1044, plain, (![B_190, C_191, D_192]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_190), C_191, u1_struct_0(D_192))=k2_tmap_1('#skF_2', B_190, C_191, D_192) | ~m1_pre_topc(D_192, '#skF_2') | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_190)))) | ~v1_funct_2(C_191, u1_struct_0('#skF_3'), u1_struct_0(B_190)) | ~v1_funct_1(C_191) | ~l1_pre_topc(B_190) | ~v2_pre_topc(B_190) | v2_struct_0(B_190) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_586, c_586, c_1033])).
% 6.62/2.29  tff(c_1439, plain, (![B_207, C_208, D_209]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0(B_207), C_208, u1_struct_0(D_209))=k2_tmap_1('#skF_2', B_207, C_208, D_209) | ~m1_pre_topc(D_209, '#skF_2') | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_207)))) | ~v1_funct_2(C_208, u1_struct_0('#skF_3'), u1_struct_0(B_207)) | ~v1_funct_1(C_208) | ~l1_pre_topc(B_207) | ~v2_pre_topc(B_207) | v2_struct_0(B_207))), inference(negUnitSimplification, [status(thm)], [c_72, c_1044])).
% 6.62/2.29  tff(c_1443, plain, (![D_209]: (k2_partfun1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_209))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_209) | ~m1_pre_topc(D_209, '#skF_2') | ~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_615, c_1439])).
% 6.62/2.29  tff(c_1453, plain, (![D_209]: (k7_relat_1('#skF_4', u1_struct_0(D_209))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_209) | ~m1_pre_topc(D_209, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_616, c_890, c_1443])).
% 6.62/2.29  tff(c_1500, plain, (![D_211]: (k7_relat_1('#skF_4', u1_struct_0(D_211))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_211) | ~m1_pre_topc(D_211, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_78, c_1453])).
% 6.62/2.29  tff(c_14, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.62/2.29  tff(c_113, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_58, c_14])).
% 6.62/2.29  tff(c_138, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.62/2.29  tff(c_146, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_138])).
% 6.62/2.29  tff(c_12, plain, (![B_6, A_5]: (k7_relat_1(B_6, A_5)=B_6 | ~v4_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.62/2.29  tff(c_150, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_146, c_12])).
% 6.62/2.29  tff(c_153, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_113, c_150])).
% 6.62/2.29  tff(c_612, plain, (k7_relat_1('#skF_4', u1_struct_0('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_586, c_153])).
% 6.62/2.29  tff(c_1506, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4' | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1500, c_612])).
% 6.62/2.29  tff(c_1521, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1506])).
% 6.62/2.29  tff(c_54, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_212])).
% 6.62/2.29  tff(c_610, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_54])).
% 6.62/2.29  tff(c_1529, plain, (~r1_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1521, c_610])).
% 6.62/2.29  tff(c_4180, plain, (~v1_funct_2('#skF_4', u1_struct_0('#skF_3'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_4177, c_1529])).
% 6.62/2.29  tff(c_4185, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_616, c_4180])).
% 6.62/2.29  tff(c_4187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4107, c_4185])).
% 6.62/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.62/2.29  
% 6.62/2.29  Inference rules
% 6.62/2.29  ----------------------
% 6.62/2.29  #Ref     : 0
% 6.62/2.29  #Sup     : 782
% 6.62/2.29  #Fact    : 0
% 6.62/2.29  #Define  : 0
% 6.62/2.29  #Split   : 13
% 6.62/2.29  #Chain   : 0
% 6.62/2.29  #Close   : 0
% 6.62/2.29  
% 6.62/2.29  Ordering : KBO
% 6.62/2.29  
% 6.62/2.29  Simplification rules
% 6.62/2.29  ----------------------
% 6.62/2.29  #Subsume      : 107
% 6.62/2.29  #Demod        : 2408
% 6.62/2.29  #Tautology    : 320
% 6.62/2.29  #SimpNegUnit  : 37
% 6.62/2.29  #BackRed      : 18
% 6.62/2.29  
% 6.62/2.29  #Partial instantiations: 0
% 6.62/2.29  #Strategies tried      : 1
% 6.62/2.29  
% 6.62/2.29  Timing (in seconds)
% 6.62/2.30  ----------------------
% 6.62/2.30  Preprocessing        : 0.37
% 6.62/2.30  Parsing              : 0.19
% 6.62/2.30  CNF conversion       : 0.03
% 6.62/2.30  Main loop            : 1.20
% 6.62/2.30  Inferencing          : 0.34
% 6.62/2.30  Reduction            : 0.53
% 6.62/2.30  Demodulation         : 0.42
% 6.62/2.30  BG Simplification    : 0.04
% 6.62/2.30  Subsumption          : 0.22
% 6.62/2.30  Abstraction          : 0.06
% 6.62/2.30  MUC search           : 0.00
% 6.62/2.30  Cooper               : 0.00
% 6.62/2.30  Total                : 1.62
% 6.62/2.30  Index Insertion      : 0.00
% 6.62/2.30  Index Deletion       : 0.00
% 6.62/2.30  Index Matching       : 0.00
% 6.62/2.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
