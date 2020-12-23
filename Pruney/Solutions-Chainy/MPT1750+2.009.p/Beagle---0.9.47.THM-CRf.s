%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:52 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :  221 (1863 expanded)
%              Number of leaves         :   51 ( 632 expanded)
%              Depth                    :   23
%              Number of atoms          :  559 (7015 expanded)
%              Number of equality atoms :   48 ( 749 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_236,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_189,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_164,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_203,axiom,(
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

tff(f_182,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_79,axiom,(
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

tff(c_80,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_30,plain,(
    ! [A_23] :
      ( l1_struct_0(A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_14,plain,(
    ! [C_9,A_7,B_8] :
      ( v1_relat_1(C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1(A_7,B_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_14])).

tff(c_148,plain,(
    ! [C_103,A_104,B_105] :
      ( v4_relat_1(C_103,A_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_156,plain,(
    v4_relat_1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_148])).

tff(c_214,plain,(
    ! [B_122,A_123] :
      ( k1_relat_1(B_122) = A_123
      | ~ v1_partfun1(B_122,A_123)
      | ~ v4_relat_1(B_122,A_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_220,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_156,c_214])).

tff(c_226,plain,
    ( u1_struct_0('#skF_2') = k1_relat_1('#skF_4')
    | ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_220])).

tff(c_227,plain,(
    ~ v1_partfun1('#skF_4',u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_333,plain,(
    ! [C_153,A_154,B_155] :
      ( v1_partfun1(C_153,A_154)
      | ~ v1_funct_2(C_153,A_154,B_155)
      | ~ v1_funct_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155)))
      | v1_xboole_0(B_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_336,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_4',u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_333])).

tff(c_343,plain,
    ( v1_partfun1('#skF_4',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_336])).

tff(c_344,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_227,c_343])).

tff(c_34,plain,(
    ! [A_27] :
      ( ~ v1_xboole_0(u1_struct_0(A_27))
      | ~ l1_struct_0(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_348,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_344,c_34])).

tff(c_351,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_348])).

tff(c_366,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_351])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_366])).

tff(c_371,plain,(
    u1_struct_0('#skF_2') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_378,plain,(
    v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_66])).

tff(c_377,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_64])).

tff(c_4093,plain,(
    ! [B_408,A_409,D_407,F_410,C_411] :
      ( r1_funct_2(A_409,B_408,C_411,D_407,F_410,F_410)
      | ~ m1_subset_1(F_410,k1_zfmisc_1(k2_zfmisc_1(C_411,D_407)))
      | ~ v1_funct_2(F_410,C_411,D_407)
      | ~ m1_subset_1(F_410,k1_zfmisc_1(k2_zfmisc_1(A_409,B_408)))
      | ~ v1_funct_2(F_410,A_409,B_408)
      | ~ v1_funct_1(F_410)
      | v1_xboole_0(D_407)
      | v1_xboole_0(B_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4095,plain,(
    ! [A_409,B_408] :
      ( r1_funct_2(A_409,B_408,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_409,B_408)))
      | ~ v1_funct_2('#skF_4',A_409,B_408)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_408) ) ),
    inference(resolution,[status(thm)],[c_377,c_4093])).

tff(c_4101,plain,(
    ! [A_409,B_408] :
      ( r1_funct_2(A_409,B_408,k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_409,B_408)))
      | ~ v1_funct_2('#skF_4',A_409,B_408)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | v1_xboole_0(B_408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_378,c_4095])).

tff(c_4323,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4101])).

tff(c_4326,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_4323,c_34])).

tff(c_4329,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4326])).

tff(c_4332,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4329])).

tff(c_4336,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4332])).

tff(c_4338,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4101])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_122,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_64,c_8])).

tff(c_376,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_122])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4973,plain,(
    ! [B_464,C_465,A_462,D_461,A_463] :
      ( r1_funct_2(A_463,B_464,C_465,D_461,A_462,A_462)
      | ~ v1_funct_2(A_462,C_465,D_461)
      | ~ m1_subset_1(A_462,k1_zfmisc_1(k2_zfmisc_1(A_463,B_464)))
      | ~ v1_funct_2(A_462,A_463,B_464)
      | ~ v1_funct_1(A_462)
      | v1_xboole_0(D_461)
      | v1_xboole_0(B_464)
      | ~ r1_tarski(A_462,k2_zfmisc_1(C_465,D_461)) ) ),
    inference(resolution,[status(thm)],[c_10,c_4093])).

tff(c_4975,plain,(
    ! [C_465,D_461] :
      ( r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),C_465,D_461,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_465,D_461)
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0(D_461)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_465,D_461)) ) ),
    inference(resolution,[status(thm)],[c_377,c_4973])).

tff(c_4981,plain,(
    ! [C_465,D_461] :
      ( r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),C_465,D_461,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_465,D_461)
      | v1_xboole_0(D_461)
      | v1_xboole_0(u1_struct_0('#skF_1'))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_465,D_461)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_378,c_4975])).

tff(c_6289,plain,(
    ! [C_518,D_519] :
      ( r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),C_518,D_519,'#skF_4','#skF_4')
      | ~ v1_funct_2('#skF_4',C_518,D_519)
      | v1_xboole_0(D_519)
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(C_518,D_519)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4338,c_4981])).

tff(c_70,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_421,plain,(
    ! [B_159,A_160] :
      ( m1_subset_1(u1_struct_0(B_159),k1_zfmisc_1(u1_struct_0(A_160)))
      | ~ m1_pre_topc(B_159,A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_430,plain,(
    ! [B_159] :
      ( m1_subset_1(u1_struct_0(B_159),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_159,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_421])).

tff(c_472,plain,(
    ! [B_161] :
      ( m1_subset_1(u1_struct_0(B_161),k1_zfmisc_1(k1_relat_1('#skF_4')))
      | ~ m1_pre_topc(B_161,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_430])).

tff(c_478,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_relat_1('#skF_4')))
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_472])).

tff(c_488,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_478])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_36,plain,(
    ! [A_28] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(A_28),u1_pre_topc(A_28)))
      | ~ l1_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_385,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_36])).

tff(c_394,plain,(
    v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_385])).

tff(c_62,plain,(
    g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')) = g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_374,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_62])).

tff(c_565,plain,(
    ! [B_172,A_173] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_172),u1_pre_topc(B_172)),A_173)
      | ~ m1_pre_topc(B_172,A_173)
      | ~ l1_pre_topc(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_32,plain,(
    ! [B_26,A_24] :
      ( l1_pre_topc(B_26)
      | ~ m1_pre_topc(B_26,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_579,plain,(
    ! [B_174,A_175] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_174),u1_pre_topc(B_174)))
      | ~ m1_pre_topc(B_174,A_175)
      | ~ l1_pre_topc(A_175) ) ),
    inference(resolution,[status(thm)],[c_565,c_32])).

tff(c_583,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_579])).

tff(c_587,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_374,c_583])).

tff(c_573,plain,(
    ! [A_173] :
      ( m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),A_173)
      | ~ m1_pre_topc('#skF_3',A_173)
      | ~ l1_pre_topc(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_565])).

tff(c_489,plain,(
    ! [B_163,A_164] :
      ( r1_tarski(u1_struct_0(B_163),u1_struct_0(A_164))
      | ~ m1_pre_topc(B_163,A_164)
      | ~ l1_pre_topc(A_164) ) ),
    inference(resolution,[status(thm)],[c_421,c_8])).

tff(c_494,plain,(
    ! [A_164] :
      ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_164))
      | ~ m1_pre_topc('#skF_2',A_164)
      | ~ l1_pre_topc(A_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_489])).

tff(c_480,plain,(
    ! [B_162] :
      ( r1_tarski(u1_struct_0(B_162),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc(B_162,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_472,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_633,plain,(
    ! [B_183] :
      ( u1_struct_0(B_183) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(B_183))
      | ~ m1_pre_topc(B_183,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_480,c_2])).

tff(c_643,plain,(
    ! [A_184] :
      ( u1_struct_0(A_184) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc(A_184,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_184)
      | ~ l1_pre_topc(A_184) ) ),
    inference(resolution,[status(thm)],[c_494,c_633])).

tff(c_649,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_573,c_643])).

tff(c_660,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_587,c_649])).

tff(c_817,plain,(
    ~ m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_660])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_818,plain,(
    ! [B_205,C_206,A_207] :
      ( m1_pre_topc(B_205,C_206)
      | ~ r1_tarski(u1_struct_0(B_205),u1_struct_0(C_206))
      | ~ m1_pre_topc(C_206,A_207)
      | ~ m1_pre_topc(B_205,A_207)
      | ~ l1_pre_topc(A_207)
      | ~ v2_pre_topc(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_833,plain,(
    ! [B_208,A_209] :
      ( m1_pre_topc(B_208,B_208)
      | ~ m1_pre_topc(B_208,A_209)
      | ~ l1_pre_topc(A_209)
      | ~ v2_pre_topc(A_209) ) ),
    inference(resolution,[status(thm)],[c_6,c_818])).

tff(c_843,plain,(
    ! [A_173] :
      ( m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(A_173)
      | ~ m1_pre_topc('#skF_3',A_173)
      | ~ l1_pre_topc(A_173) ) ),
    inference(resolution,[status(thm)],[c_573,c_833])).

tff(c_888,plain,(
    ! [A_210] :
      ( ~ v2_pre_topc(A_210)
      | ~ m1_pre_topc('#skF_3',A_210)
      | ~ l1_pre_topc(A_210) ) ),
    inference(splitLeft,[status(thm)],[c_843])).

tff(c_894,plain,
    ( ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_888])).

tff(c_901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_894])).

tff(c_902,plain,(
    m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_947,plain,(
    ! [C_214,A_215] :
      ( m1_pre_topc(C_214,A_215)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_214),u1_pre_topc(C_214)),A_215)
      | ~ l1_pre_topc(C_214)
      | ~ v2_pre_topc(C_214)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_214),u1_pre_topc(C_214)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_214),u1_pre_topc(C_214)))
      | ~ l1_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_956,plain,(
    ! [A_215] :
      ( m1_pre_topc('#skF_2',A_215)
      | ~ m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),A_215)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_947])).

tff(c_962,plain,(
    ! [A_216] :
      ( m1_pre_topc('#skF_2',A_216)
      | ~ m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),A_216)
      | ~ l1_pre_topc(A_216) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_371,c_587,c_371,c_76,c_74,c_956])).

tff(c_965,plain,
    ( m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_902,c_962])).

tff(c_974,plain,(
    m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_965])).

tff(c_976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_817,c_974])).

tff(c_978,plain,(
    m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_660])).

tff(c_1149,plain,(
    ! [B_217,C_218,A_219] :
      ( m1_pre_topc(B_217,C_218)
      | ~ r1_tarski(u1_struct_0(B_217),u1_struct_0(C_218))
      | ~ m1_pre_topc(C_218,A_219)
      | ~ m1_pre_topc(B_217,A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1199,plain,(
    ! [B_220,A_221] :
      ( m1_pre_topc(B_220,B_220)
      | ~ m1_pre_topc(B_220,A_221)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221) ) ),
    inference(resolution,[status(thm)],[c_6,c_1149])).

tff(c_1203,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_978,c_1199])).

tff(c_1217,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_587,c_1203])).

tff(c_1219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_488,c_1217])).

tff(c_1221,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_478])).

tff(c_1251,plain,(
    ! [B_222,A_223] :
      ( r1_tarski(u1_struct_0(B_222),u1_struct_0(A_223))
      | ~ m1_pre_topc(B_222,A_223)
      | ~ l1_pre_topc(A_223) ) ),
    inference(resolution,[status(thm)],[c_421,c_8])).

tff(c_1264,plain,(
    ! [A_226] :
      ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_226))
      | ~ m1_pre_topc('#skF_2',A_226)
      | ~ l1_pre_topc(A_226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1251])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k7_relat_1(B_6,A_5) = B_6
      | ~ r1_tarski(k1_relat_1(B_6),A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1267,plain,(
    ! [A_226] :
      ( k7_relat_1('#skF_4',u1_struct_0(A_226)) = '#skF_4'
      | ~ v1_relat_1('#skF_4')
      | ~ m1_pre_topc('#skF_2',A_226)
      | ~ l1_pre_topc(A_226) ) ),
    inference(resolution,[status(thm)],[c_1264,c_12])).

tff(c_1279,plain,(
    ! [A_227] :
      ( k7_relat_1('#skF_4',u1_struct_0(A_227)) = '#skF_4'
      | ~ m1_pre_topc('#skF_2',A_227)
      | ~ l1_pre_topc(A_227) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_1267])).

tff(c_1288,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4'
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1279])).

tff(c_1292,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1221,c_1288])).

tff(c_94,plain,(
    ! [B_87,A_88] :
      ( l1_pre_topc(B_87)
      | ~ m1_pre_topc(B_87,A_88)
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_94])).

tff(c_100,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_97])).

tff(c_1256,plain,(
    ! [A_223] :
      ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_223))
      | ~ m1_pre_topc('#skF_2',A_223)
      | ~ l1_pre_topc(A_223) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1251])).

tff(c_1402,plain,(
    ! [B_242] :
      ( u1_struct_0(B_242) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(B_242))
      | ~ m1_pre_topc(B_242,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_480,c_2])).

tff(c_1412,plain,(
    ! [A_243] :
      ( u1_struct_0(A_243) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc(A_243,'#skF_2')
      | ~ m1_pre_topc('#skF_2',A_243)
      | ~ l1_pre_topc(A_243) ) ),
    inference(resolution,[status(thm)],[c_1256,c_1402])).

tff(c_1425,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1412])).

tff(c_1440,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1425])).

tff(c_1441,plain,(
    ~ m1_pre_topc('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1440])).

tff(c_1926,plain,(
    ! [B_284,C_285,A_286] :
      ( m1_pre_topc(B_284,C_285)
      | ~ r1_tarski(u1_struct_0(B_284),u1_struct_0(C_285))
      | ~ m1_pre_topc(C_285,A_286)
      | ~ m1_pre_topc(B_284,A_286)
      | ~ l1_pre_topc(A_286)
      | ~ v2_pre_topc(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1942,plain,(
    ! [B_287,A_288] :
      ( m1_pre_topc(B_287,B_287)
      | ~ m1_pre_topc(B_287,A_288)
      | ~ l1_pre_topc(A_288)
      | ~ v2_pre_topc(A_288) ) ),
    inference(resolution,[status(thm)],[c_6,c_1926])).

tff(c_1954,plain,
    ( m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1942])).

tff(c_1966,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1954])).

tff(c_1330,plain,(
    ! [B_231,A_232] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_231),u1_pre_topc(B_231)),A_232)
      | ~ m1_pre_topc(B_231,A_232)
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1338,plain,(
    ! [A_232] :
      ( m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),A_232)
      | ~ m1_pre_topc('#skF_3',A_232)
      | ~ l1_pre_topc(A_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_1330])).

tff(c_1344,plain,(
    ! [B_233,A_234] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(B_233),u1_pre_topc(B_233)))
      | ~ m1_pre_topc(B_233,A_234)
      | ~ l1_pre_topc(A_234) ) ),
    inference(resolution,[status(thm)],[c_1330,c_32])).

tff(c_1350,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1344])).

tff(c_1357,plain,(
    l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_374,c_1350])).

tff(c_1341,plain,(
    ! [A_232] :
      ( m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),A_232)
      | ~ m1_pre_topc('#skF_2',A_232)
      | ~ l1_pre_topc(A_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1330])).

tff(c_1415,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1341,c_1412])).

tff(c_1428,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1221,c_1357,c_1415])).

tff(c_1530,plain,(
    ~ m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1428])).

tff(c_1531,plain,(
    ! [B_257,C_258,A_259] :
      ( m1_pre_topc(B_257,C_258)
      | ~ r1_tarski(u1_struct_0(B_257),u1_struct_0(C_258))
      | ~ m1_pre_topc(C_258,A_259)
      | ~ m1_pre_topc(B_257,A_259)
      | ~ l1_pre_topc(A_259)
      | ~ v2_pre_topc(A_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1543,plain,(
    ! [B_260,A_261] :
      ( m1_pre_topc(B_260,B_260)
      | ~ m1_pre_topc(B_260,A_261)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261) ) ),
    inference(resolution,[status(thm)],[c_6,c_1531])).

tff(c_1555,plain,(
    ! [A_232] :
      ( m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(A_232)
      | ~ m1_pre_topc('#skF_3',A_232)
      | ~ l1_pre_topc(A_232) ) ),
    inference(resolution,[status(thm)],[c_1338,c_1543])).

tff(c_1591,plain,(
    ! [A_262] :
      ( ~ v2_pre_topc(A_262)
      | ~ m1_pre_topc('#skF_3',A_262)
      | ~ l1_pre_topc(A_262) ) ),
    inference(splitLeft,[status(thm)],[c_1555])).

tff(c_1597,plain,
    ( ~ v2_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_1591])).

tff(c_1604,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_76,c_1597])).

tff(c_1605,plain,(
    m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1555])).

tff(c_1782,plain,(
    ! [C_280,A_281] :
      ( m1_pre_topc(C_280,A_281)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_280),u1_pre_topc(C_280)),A_281)
      | ~ l1_pre_topc(C_280)
      | ~ v2_pre_topc(C_280)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_280),u1_pre_topc(C_280)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_280),u1_pre_topc(C_280)))
      | ~ l1_pre_topc(A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1791,plain,(
    ! [A_281] :
      ( m1_pre_topc('#skF_2',A_281)
      | ~ m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),A_281)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'),u1_pre_topc('#skF_2')))
      | ~ l1_pre_topc(A_281) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1782])).

tff(c_1797,plain,(
    ! [A_282] :
      ( m1_pre_topc('#skF_2',A_282)
      | ~ m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),A_282)
      | ~ l1_pre_topc(A_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_371,c_1357,c_371,c_76,c_74,c_1791])).

tff(c_1800,plain,
    ( m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1605,c_1797])).

tff(c_1809,plain,(
    m1_pre_topc('#skF_2',g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1800])).

tff(c_1811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1530,c_1809])).

tff(c_1812,plain,(
    u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2'))) = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1428])).

tff(c_431,plain,(
    ! [B_159,A_160] :
      ( r1_tarski(u1_struct_0(B_159),u1_struct_0(A_160))
      | ~ m1_pre_topc(B_159,A_160)
      | ~ l1_pre_topc(A_160) ) ),
    inference(resolution,[status(thm)],[c_421,c_8])).

tff(c_2083,plain,(
    ! [A_292] :
      ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_292))
      | ~ m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'),u1_pre_topc('#skF_2')),A_292)
      | ~ l1_pre_topc(A_292) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1812,c_431])).

tff(c_2098,plain,(
    ! [A_293] :
      ( r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(A_293))
      | ~ m1_pre_topc('#skF_3',A_293)
      | ~ l1_pre_topc(A_293) ) ),
    inference(resolution,[status(thm)],[c_1338,c_2083])).

tff(c_486,plain,(
    ! [B_162] :
      ( u1_struct_0(B_162) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(B_162))
      | ~ m1_pre_topc(B_162,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_480,c_2])).

tff(c_2206,plain,(
    ! [A_299] :
      ( u1_struct_0(A_299) = k1_relat_1('#skF_4')
      | ~ m1_pre_topc(A_299,'#skF_2')
      | ~ m1_pre_topc('#skF_3',A_299)
      | ~ l1_pre_topc(A_299) ) ),
    inference(resolution,[status(thm)],[c_2098,c_486])).

tff(c_2219,plain,
    ( u1_struct_0('#skF_3') = k1_relat_1('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2206])).

tff(c_2234,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1966,c_2219])).

tff(c_3404,plain,(
    ! [C_366,A_367] :
      ( m1_pre_topc('#skF_2',C_366)
      | ~ r1_tarski(k1_relat_1('#skF_4'),u1_struct_0(C_366))
      | ~ m1_pre_topc(C_366,A_367)
      | ~ m1_pre_topc('#skF_2',A_367)
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_1926])).

tff(c_3410,plain,(
    ! [A_367] :
      ( m1_pre_topc('#skF_2','#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
      | ~ m1_pre_topc('#skF_3',A_367)
      | ~ m1_pre_topc('#skF_2',A_367)
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2234,c_3404])).

tff(c_3421,plain,(
    ! [A_367] :
      ( m1_pre_topc('#skF_2','#skF_3')
      | ~ m1_pre_topc('#skF_3',A_367)
      | ~ m1_pre_topc('#skF_2',A_367)
      | ~ l1_pre_topc(A_367)
      | ~ v2_pre_topc(A_367) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3410])).

tff(c_3427,plain,(
    ! [A_368] :
      ( ~ m1_pre_topc('#skF_3',A_368)
      | ~ m1_pre_topc('#skF_2',A_368)
      | ~ l1_pre_topc(A_368)
      | ~ v2_pre_topc(A_368) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1441,c_3421])).

tff(c_3433,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_1221,c_3427])).

tff(c_3440,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_3433])).

tff(c_3441,plain,(
    u1_struct_0('#skF_3') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1440])).

tff(c_82,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_1383,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k2_partfun1(A_237,B_238,C_239,D_240) = k7_relat_1(C_239,D_240)
      | ~ m1_subset_1(C_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ v1_funct_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1385,plain,(
    ! [D_240] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_240) = k7_relat_1('#skF_4',D_240)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_377,c_1383])).

tff(c_1391,plain,(
    ! [D_240] : k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',D_240) = k7_relat_1('#skF_4',D_240) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1385])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_4391,plain,(
    ! [A_427,B_428,C_429,D_430] :
      ( k2_partfun1(u1_struct_0(A_427),u1_struct_0(B_428),C_429,u1_struct_0(D_430)) = k2_tmap_1(A_427,B_428,C_429,D_430)
      | ~ m1_pre_topc(D_430,A_427)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_427),u1_struct_0(B_428))))
      | ~ v1_funct_2(C_429,u1_struct_0(A_427),u1_struct_0(B_428))
      | ~ v1_funct_1(C_429)
      | ~ l1_pre_topc(B_428)
      | ~ v2_pre_topc(B_428)
      | v2_struct_0(B_428)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_4401,plain,(
    ! [B_428,C_429,D_430] :
      ( k2_partfun1(u1_struct_0('#skF_2'),u1_struct_0(B_428),C_429,u1_struct_0(D_430)) = k2_tmap_1('#skF_2',B_428,C_429,D_430)
      | ~ m1_pre_topc(D_430,'#skF_2')
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_428))))
      | ~ v1_funct_2(C_429,u1_struct_0('#skF_2'),u1_struct_0(B_428))
      | ~ v1_funct_1(C_429)
      | ~ l1_pre_topc(B_428)
      | ~ v2_pre_topc(B_428)
      | v2_struct_0(B_428)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_4391])).

tff(c_4418,plain,(
    ! [B_428,C_429,D_430] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_428),C_429,u1_struct_0(D_430)) = k2_tmap_1('#skF_2',B_428,C_429,D_430)
      | ~ m1_pre_topc(D_430,'#skF_2')
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_428))))
      | ~ v1_funct_2(C_429,k1_relat_1('#skF_4'),u1_struct_0(B_428))
      | ~ v1_funct_1(C_429)
      | ~ l1_pre_topc(B_428)
      | ~ v2_pre_topc(B_428)
      | v2_struct_0(B_428)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_371,c_371,c_4401])).

tff(c_4713,plain,(
    ! [B_452,C_453,D_454] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0(B_452),C_453,u1_struct_0(D_454)) = k2_tmap_1('#skF_2',B_452,C_453,D_454)
      | ~ m1_pre_topc(D_454,'#skF_2')
      | ~ m1_subset_1(C_453,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0(B_452))))
      | ~ v1_funct_2(C_453,k1_relat_1('#skF_4'),u1_struct_0(B_452))
      | ~ v1_funct_1(C_453)
      | ~ l1_pre_topc(B_452)
      | ~ v2_pre_topc(B_452)
      | v2_struct_0(B_452) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_4418])).

tff(c_4719,plain,(
    ! [D_454] :
      ( k2_partfun1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',u1_struct_0(D_454)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_454)
      | ~ m1_pre_topc(D_454,'#skF_2')
      | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_377,c_4713])).

tff(c_4732,plain,(
    ! [D_454] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_454)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_454)
      | ~ m1_pre_topc(D_454,'#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_68,c_378,c_1391,c_4719])).

tff(c_4739,plain,(
    ! [D_455] :
      ( k7_relat_1('#skF_4',u1_struct_0(D_455)) = k2_tmap_1('#skF_2','#skF_1','#skF_4',D_455)
      | ~ m1_pre_topc(D_455,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_4732])).

tff(c_4760,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3441,c_4739])).

tff(c_4771,plain,(
    k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1292,c_4760])).

tff(c_60,plain,(
    ~ r1_funct_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_373,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),u1_struct_0('#skF_3'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_60])).

tff(c_3461,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4',k2_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3441,c_373])).

tff(c_4778,plain,(
    ~ r1_funct_2(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),k1_relat_1('#skF_4'),u1_struct_0('#skF_1'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4771,c_3461])).

tff(c_6292,plain,
    ( ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1'))
    | ~ r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),u1_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6289,c_4778])).

tff(c_6297,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_376,c_378,c_6292])).

tff(c_6299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4338,c_6297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.75  
% 7.65/2.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/2.75  %$ r1_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_relat_1 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k2_tmap_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.65/2.75  
% 7.65/2.75  %Foreground sorts:
% 7.65/2.75  
% 7.65/2.75  
% 7.65/2.75  %Background operators:
% 7.65/2.75  
% 7.65/2.75  
% 7.65/2.75  %Foreground operators:
% 7.65/2.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.65/2.75  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.65/2.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.65/2.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.65/2.75  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.65/2.75  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.65/2.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.65/2.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.65/2.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.65/2.75  tff('#skF_2', type, '#skF_2': $i).
% 7.65/2.75  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.65/2.75  tff('#skF_3', type, '#skF_3': $i).
% 7.65/2.75  tff('#skF_1', type, '#skF_1': $i).
% 7.65/2.75  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.65/2.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.65/2.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.65/2.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.65/2.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.65/2.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.65/2.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.65/2.75  tff('#skF_4', type, '#skF_4': $i).
% 7.65/2.75  tff(r1_funct_2, type, r1_funct_2: ($i * $i * $i * $i * $i * $i) > $o).
% 7.65/2.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.65/2.75  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.65/2.75  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.65/2.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.65/2.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.65/2.75  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 7.65/2.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.65/2.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.65/2.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.65/2.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.65/2.75  
% 7.90/2.78  tff(f_236, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) => r1_funct_2(u1_struct_0(B), u1_struct_0(A), u1_struct_0(C), u1_struct_0(A), D, k2_tmap_1(B, A, D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_tmap_1)).
% 7.90/2.78  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.90/2.78  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.90/2.78  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.90/2.78  tff(f_73, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 7.90/2.78  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.90/2.78  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.90/2.78  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((((((~v1_xboole_0(B) & ~v1_xboole_0(D)) & v1_funct_1(E)) & v1_funct_2(E, A, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & v1_funct_2(F, C, D)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (r1_funct_2(A, B, C, D, E, F) <=> (E = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_funct_2)).
% 7.90/2.78  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.90/2.78  tff(f_189, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 7.90/2.78  tff(f_106, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 7.90/2.78  tff(f_164, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 7.90/2.78  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.90/2.78  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.90/2.78  tff(f_203, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 7.90/2.78  tff(f_182, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 7.90/2.78  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 7.90/2.78  tff(f_79, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.90/2.78  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 7.90/2.78  tff(c_80, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_30, plain, (![A_23]: (l1_struct_0(A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.90/2.78  tff(c_84, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_14, plain, (![C_9, A_7, B_8]: (v1_relat_1(C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1(A_7, B_8))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.90/2.78  tff(c_121, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_14])).
% 7.90/2.78  tff(c_148, plain, (![C_103, A_104, B_105]: (v4_relat_1(C_103, A_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.90/2.78  tff(c_156, plain, (v4_relat_1('#skF_4', u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_148])).
% 7.90/2.78  tff(c_214, plain, (![B_122, A_123]: (k1_relat_1(B_122)=A_123 | ~v1_partfun1(B_122, A_123) | ~v4_relat_1(B_122, A_123) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.90/2.78  tff(c_220, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_156, c_214])).
% 7.90/2.78  tff(c_226, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4') | ~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_220])).
% 7.90/2.78  tff(c_227, plain, (~v1_partfun1('#skF_4', u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_226])).
% 7.90/2.78  tff(c_66, plain, (v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_333, plain, (![C_153, A_154, B_155]: (v1_partfun1(C_153, A_154) | ~v1_funct_2(C_153, A_154, B_155) | ~v1_funct_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))) | v1_xboole_0(B_155))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.90/2.78  tff(c_336, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_4', u1_struct_0('#skF_2'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_64, c_333])).
% 7.90/2.78  tff(c_343, plain, (v1_partfun1('#skF_4', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_336])).
% 7.90/2.78  tff(c_344, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_227, c_343])).
% 7.90/2.78  tff(c_34, plain, (![A_27]: (~v1_xboole_0(u1_struct_0(A_27)) | ~l1_struct_0(A_27) | v2_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.90/2.78  tff(c_348, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_344, c_34])).
% 7.90/2.78  tff(c_351, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_84, c_348])).
% 7.90/2.78  tff(c_366, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_351])).
% 7.90/2.78  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_366])).
% 7.90/2.78  tff(c_371, plain, (u1_struct_0('#skF_2')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_226])).
% 7.90/2.78  tff(c_378, plain, (v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_66])).
% 7.90/2.78  tff(c_377, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_64])).
% 7.90/2.78  tff(c_4093, plain, (![B_408, A_409, D_407, F_410, C_411]: (r1_funct_2(A_409, B_408, C_411, D_407, F_410, F_410) | ~m1_subset_1(F_410, k1_zfmisc_1(k2_zfmisc_1(C_411, D_407))) | ~v1_funct_2(F_410, C_411, D_407) | ~m1_subset_1(F_410, k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))) | ~v1_funct_2(F_410, A_409, B_408) | ~v1_funct_1(F_410) | v1_xboole_0(D_407) | v1_xboole_0(B_408))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.90/2.78  tff(c_4095, plain, (![A_409, B_408]: (r1_funct_2(A_409, B_408, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))) | ~v1_funct_2('#skF_4', A_409, B_408) | ~v1_funct_1('#skF_4') | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_408))), inference(resolution, [status(thm)], [c_377, c_4093])).
% 7.90/2.78  tff(c_4101, plain, (![A_409, B_408]: (r1_funct_2(A_409, B_408, k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_409, B_408))) | ~v1_funct_2('#skF_4', A_409, B_408) | v1_xboole_0(u1_struct_0('#skF_1')) | v1_xboole_0(B_408))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_378, c_4095])).
% 7.90/2.78  tff(c_4323, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_4101])).
% 7.90/2.78  tff(c_4326, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_4323, c_34])).
% 7.90/2.78  tff(c_4329, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_84, c_4326])).
% 7.90/2.78  tff(c_4332, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4329])).
% 7.90/2.78  tff(c_4336, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_4332])).
% 7.90/2.78  tff(c_4338, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_4101])).
% 7.90/2.78  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.90/2.78  tff(c_122, plain, (r1_tarski('#skF_4', k2_zfmisc_1(u1_struct_0('#skF_2'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_64, c_8])).
% 7.90/2.78  tff(c_376, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_122])).
% 7.90/2.78  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.90/2.78  tff(c_4973, plain, (![B_464, C_465, A_462, D_461, A_463]: (r1_funct_2(A_463, B_464, C_465, D_461, A_462, A_462) | ~v1_funct_2(A_462, C_465, D_461) | ~m1_subset_1(A_462, k1_zfmisc_1(k2_zfmisc_1(A_463, B_464))) | ~v1_funct_2(A_462, A_463, B_464) | ~v1_funct_1(A_462) | v1_xboole_0(D_461) | v1_xboole_0(B_464) | ~r1_tarski(A_462, k2_zfmisc_1(C_465, D_461)))), inference(resolution, [status(thm)], [c_10, c_4093])).
% 7.90/2.78  tff(c_4975, plain, (![C_465, D_461]: (r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), C_465, D_461, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_465, D_461) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | v1_xboole_0(D_461) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_465, D_461)))), inference(resolution, [status(thm)], [c_377, c_4973])).
% 7.90/2.78  tff(c_4981, plain, (![C_465, D_461]: (r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), C_465, D_461, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_465, D_461) | v1_xboole_0(D_461) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_465, D_461)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_378, c_4975])).
% 7.90/2.78  tff(c_6289, plain, (![C_518, D_519]: (r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), C_518, D_519, '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', C_518, D_519) | v1_xboole_0(D_519) | ~r1_tarski('#skF_4', k2_zfmisc_1(C_518, D_519)))), inference(negUnitSimplification, [status(thm)], [c_4338, c_4981])).
% 7.90/2.78  tff(c_70, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_421, plain, (![B_159, A_160]: (m1_subset_1(u1_struct_0(B_159), k1_zfmisc_1(u1_struct_0(A_160))) | ~m1_pre_topc(B_159, A_160) | ~l1_pre_topc(A_160))), inference(cnfTransformation, [status(thm)], [f_189])).
% 7.90/2.78  tff(c_430, plain, (![B_159]: (m1_subset_1(u1_struct_0(B_159), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_159, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_421])).
% 7.90/2.78  tff(c_472, plain, (![B_161]: (m1_subset_1(u1_struct_0(B_161), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc(B_161, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_430])).
% 7.90/2.78  tff(c_478, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_relat_1('#skF_4'))) | ~m1_pre_topc('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_371, c_472])).
% 7.90/2.78  tff(c_488, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_478])).
% 7.90/2.78  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_36, plain, (![A_28]: (v2_pre_topc(g1_pre_topc(u1_struct_0(A_28), u1_pre_topc(A_28))) | ~l1_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.90/2.78  tff(c_385, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_371, c_36])).
% 7.90/2.78  tff(c_394, plain, (v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_385])).
% 7.90/2.78  tff(c_62, plain, (g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))=g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_374, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_62])).
% 7.90/2.78  tff(c_565, plain, (![B_172, A_173]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_172), u1_pre_topc(B_172)), A_173) | ~m1_pre_topc(B_172, A_173) | ~l1_pre_topc(A_173))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.90/2.78  tff(c_32, plain, (![B_26, A_24]: (l1_pre_topc(B_26) | ~m1_pre_topc(B_26, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.90/2.78  tff(c_579, plain, (![B_174, A_175]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_174), u1_pre_topc(B_174))) | ~m1_pre_topc(B_174, A_175) | ~l1_pre_topc(A_175))), inference(resolution, [status(thm)], [c_565, c_32])).
% 7.90/2.78  tff(c_583, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_579])).
% 7.90/2.78  tff(c_587, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_374, c_583])).
% 7.90/2.78  tff(c_573, plain, (![A_173]: (m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), A_173) | ~m1_pre_topc('#skF_3', A_173) | ~l1_pre_topc(A_173))), inference(superposition, [status(thm), theory('equality')], [c_374, c_565])).
% 7.90/2.78  tff(c_489, plain, (![B_163, A_164]: (r1_tarski(u1_struct_0(B_163), u1_struct_0(A_164)) | ~m1_pre_topc(B_163, A_164) | ~l1_pre_topc(A_164))), inference(resolution, [status(thm)], [c_421, c_8])).
% 7.90/2.78  tff(c_494, plain, (![A_164]: (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_164)) | ~m1_pre_topc('#skF_2', A_164) | ~l1_pre_topc(A_164))), inference(superposition, [status(thm), theory('equality')], [c_371, c_489])).
% 7.90/2.78  tff(c_480, plain, (![B_162]: (r1_tarski(u1_struct_0(B_162), k1_relat_1('#skF_4')) | ~m1_pre_topc(B_162, '#skF_2'))), inference(resolution, [status(thm)], [c_472, c_8])).
% 7.90/2.78  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.90/2.78  tff(c_633, plain, (![B_183]: (u1_struct_0(B_183)=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(B_183)) | ~m1_pre_topc(B_183, '#skF_2'))), inference(resolution, [status(thm)], [c_480, c_2])).
% 7.90/2.78  tff(c_643, plain, (![A_184]: (u1_struct_0(A_184)=k1_relat_1('#skF_4') | ~m1_pre_topc(A_184, '#skF_2') | ~m1_pre_topc('#skF_2', A_184) | ~l1_pre_topc(A_184))), inference(resolution, [status(thm)], [c_494, c_633])).
% 7.90/2.78  tff(c_649, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_573, c_643])).
% 7.90/2.78  tff(c_660, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_587, c_649])).
% 7.90/2.78  tff(c_817, plain, (~m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_660])).
% 7.90/2.78  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.90/2.78  tff(c_818, plain, (![B_205, C_206, A_207]: (m1_pre_topc(B_205, C_206) | ~r1_tarski(u1_struct_0(B_205), u1_struct_0(C_206)) | ~m1_pre_topc(C_206, A_207) | ~m1_pre_topc(B_205, A_207) | ~l1_pre_topc(A_207) | ~v2_pre_topc(A_207))), inference(cnfTransformation, [status(thm)], [f_203])).
% 7.90/2.78  tff(c_833, plain, (![B_208, A_209]: (m1_pre_topc(B_208, B_208) | ~m1_pre_topc(B_208, A_209) | ~l1_pre_topc(A_209) | ~v2_pre_topc(A_209))), inference(resolution, [status(thm)], [c_6, c_818])).
% 7.90/2.78  tff(c_843, plain, (![A_173]: (m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(A_173) | ~m1_pre_topc('#skF_3', A_173) | ~l1_pre_topc(A_173))), inference(resolution, [status(thm)], [c_573, c_833])).
% 7.90/2.78  tff(c_888, plain, (![A_210]: (~v2_pre_topc(A_210) | ~m1_pre_topc('#skF_3', A_210) | ~l1_pre_topc(A_210))), inference(splitLeft, [status(thm)], [c_843])).
% 7.90/2.78  tff(c_894, plain, (~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_888])).
% 7.90/2.78  tff(c_901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_894])).
% 7.90/2.78  tff(c_902, plain, (m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_843])).
% 7.90/2.78  tff(c_947, plain, (![C_214, A_215]: (m1_pre_topc(C_214, A_215) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_214), u1_pre_topc(C_214)), A_215) | ~l1_pre_topc(C_214) | ~v2_pre_topc(C_214) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_214), u1_pre_topc(C_214))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_214), u1_pre_topc(C_214))) | ~l1_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.90/2.78  tff(c_956, plain, (![A_215]: (m1_pre_topc('#skF_2', A_215) | ~m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), A_215) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_215))), inference(superposition, [status(thm), theory('equality')], [c_371, c_947])).
% 7.90/2.78  tff(c_962, plain, (![A_216]: (m1_pre_topc('#skF_2', A_216) | ~m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), A_216) | ~l1_pre_topc(A_216))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_371, c_587, c_371, c_76, c_74, c_956])).
% 7.90/2.78  tff(c_965, plain, (m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_902, c_962])).
% 7.90/2.78  tff(c_974, plain, (m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_587, c_965])).
% 7.90/2.78  tff(c_976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_817, c_974])).
% 7.90/2.78  tff(c_978, plain, (m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_660])).
% 7.90/2.78  tff(c_1149, plain, (![B_217, C_218, A_219]: (m1_pre_topc(B_217, C_218) | ~r1_tarski(u1_struct_0(B_217), u1_struct_0(C_218)) | ~m1_pre_topc(C_218, A_219) | ~m1_pre_topc(B_217, A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219))), inference(cnfTransformation, [status(thm)], [f_203])).
% 7.90/2.78  tff(c_1199, plain, (![B_220, A_221]: (m1_pre_topc(B_220, B_220) | ~m1_pre_topc(B_220, A_221) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221))), inference(resolution, [status(thm)], [c_6, c_1149])).
% 7.90/2.78  tff(c_1203, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_978, c_1199])).
% 7.90/2.78  tff(c_1217, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_587, c_1203])).
% 7.90/2.78  tff(c_1219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_488, c_1217])).
% 7.90/2.78  tff(c_1221, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_478])).
% 7.90/2.78  tff(c_1251, plain, (![B_222, A_223]: (r1_tarski(u1_struct_0(B_222), u1_struct_0(A_223)) | ~m1_pre_topc(B_222, A_223) | ~l1_pre_topc(A_223))), inference(resolution, [status(thm)], [c_421, c_8])).
% 7.90/2.78  tff(c_1264, plain, (![A_226]: (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_226)) | ~m1_pre_topc('#skF_2', A_226) | ~l1_pre_topc(A_226))), inference(superposition, [status(thm), theory('equality')], [c_371, c_1251])).
% 7.90/2.78  tff(c_12, plain, (![B_6, A_5]: (k7_relat_1(B_6, A_5)=B_6 | ~r1_tarski(k1_relat_1(B_6), A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.90/2.78  tff(c_1267, plain, (![A_226]: (k7_relat_1('#skF_4', u1_struct_0(A_226))='#skF_4' | ~v1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', A_226) | ~l1_pre_topc(A_226))), inference(resolution, [status(thm)], [c_1264, c_12])).
% 7.90/2.78  tff(c_1279, plain, (![A_227]: (k7_relat_1('#skF_4', u1_struct_0(A_227))='#skF_4' | ~m1_pre_topc('#skF_2', A_227) | ~l1_pre_topc(A_227))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_1267])).
% 7.90/2.78  tff(c_1288, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4' | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_371, c_1279])).
% 7.90/2.78  tff(c_1292, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1221, c_1288])).
% 7.90/2.78  tff(c_94, plain, (![B_87, A_88]: (l1_pre_topc(B_87) | ~m1_pre_topc(B_87, A_88) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.90/2.78  tff(c_97, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_94])).
% 7.90/2.78  tff(c_100, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_97])).
% 7.90/2.78  tff(c_1256, plain, (![A_223]: (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_223)) | ~m1_pre_topc('#skF_2', A_223) | ~l1_pre_topc(A_223))), inference(superposition, [status(thm), theory('equality')], [c_371, c_1251])).
% 7.90/2.78  tff(c_1402, plain, (![B_242]: (u1_struct_0(B_242)=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(B_242)) | ~m1_pre_topc(B_242, '#skF_2'))), inference(resolution, [status(thm)], [c_480, c_2])).
% 7.90/2.78  tff(c_1412, plain, (![A_243]: (u1_struct_0(A_243)=k1_relat_1('#skF_4') | ~m1_pre_topc(A_243, '#skF_2') | ~m1_pre_topc('#skF_2', A_243) | ~l1_pre_topc(A_243))), inference(resolution, [status(thm)], [c_1256, c_1402])).
% 7.90/2.78  tff(c_1425, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_1412])).
% 7.90/2.78  tff(c_1440, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1425])).
% 7.90/2.78  tff(c_1441, plain, (~m1_pre_topc('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_1440])).
% 7.90/2.78  tff(c_1926, plain, (![B_284, C_285, A_286]: (m1_pre_topc(B_284, C_285) | ~r1_tarski(u1_struct_0(B_284), u1_struct_0(C_285)) | ~m1_pre_topc(C_285, A_286) | ~m1_pre_topc(B_284, A_286) | ~l1_pre_topc(A_286) | ~v2_pre_topc(A_286))), inference(cnfTransformation, [status(thm)], [f_203])).
% 7.90/2.78  tff(c_1942, plain, (![B_287, A_288]: (m1_pre_topc(B_287, B_287) | ~m1_pre_topc(B_287, A_288) | ~l1_pre_topc(A_288) | ~v2_pre_topc(A_288))), inference(resolution, [status(thm)], [c_6, c_1926])).
% 7.90/2.78  tff(c_1954, plain, (m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1942])).
% 7.90/2.78  tff(c_1966, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1954])).
% 7.90/2.78  tff(c_1330, plain, (![B_231, A_232]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_231), u1_pre_topc(B_231)), A_232) | ~m1_pre_topc(B_231, A_232) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_164])).
% 7.90/2.78  tff(c_1338, plain, (![A_232]: (m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), A_232) | ~m1_pre_topc('#skF_3', A_232) | ~l1_pre_topc(A_232))), inference(superposition, [status(thm), theory('equality')], [c_374, c_1330])).
% 7.90/2.78  tff(c_1344, plain, (![B_233, A_234]: (l1_pre_topc(g1_pre_topc(u1_struct_0(B_233), u1_pre_topc(B_233))) | ~m1_pre_topc(B_233, A_234) | ~l1_pre_topc(A_234))), inference(resolution, [status(thm)], [c_1330, c_32])).
% 7.90/2.78  tff(c_1350, plain, (l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1344])).
% 7.90/2.78  tff(c_1357, plain, (l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_374, c_1350])).
% 7.90/2.78  tff(c_1341, plain, (![A_232]: (m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), A_232) | ~m1_pre_topc('#skF_2', A_232) | ~l1_pre_topc(A_232))), inference(superposition, [status(thm), theory('equality')], [c_371, c_1330])).
% 7.90/2.78  tff(c_1415, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1341, c_1412])).
% 7.90/2.78  tff(c_1428, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1221, c_1357, c_1415])).
% 7.90/2.78  tff(c_1530, plain, (~m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(splitLeft, [status(thm)], [c_1428])).
% 7.90/2.78  tff(c_1531, plain, (![B_257, C_258, A_259]: (m1_pre_topc(B_257, C_258) | ~r1_tarski(u1_struct_0(B_257), u1_struct_0(C_258)) | ~m1_pre_topc(C_258, A_259) | ~m1_pre_topc(B_257, A_259) | ~l1_pre_topc(A_259) | ~v2_pre_topc(A_259))), inference(cnfTransformation, [status(thm)], [f_203])).
% 7.90/2.78  tff(c_1543, plain, (![B_260, A_261]: (m1_pre_topc(B_260, B_260) | ~m1_pre_topc(B_260, A_261) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261))), inference(resolution, [status(thm)], [c_6, c_1531])).
% 7.90/2.78  tff(c_1555, plain, (![A_232]: (m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(A_232) | ~m1_pre_topc('#skF_3', A_232) | ~l1_pre_topc(A_232))), inference(resolution, [status(thm)], [c_1338, c_1543])).
% 7.90/2.78  tff(c_1591, plain, (![A_262]: (~v2_pre_topc(A_262) | ~m1_pre_topc('#skF_3', A_262) | ~l1_pre_topc(A_262))), inference(splitLeft, [status(thm)], [c_1555])).
% 7.90/2.78  tff(c_1597, plain, (~v2_pre_topc('#skF_2') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_70, c_1591])).
% 7.90/2.78  tff(c_1604, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_76, c_1597])).
% 7.90/2.78  tff(c_1605, plain, (m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(splitRight, [status(thm)], [c_1555])).
% 7.90/2.78  tff(c_1782, plain, (![C_280, A_281]: (m1_pre_topc(C_280, A_281) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_280), u1_pre_topc(C_280)), A_281) | ~l1_pre_topc(C_280) | ~v2_pre_topc(C_280) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_280), u1_pre_topc(C_280))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_280), u1_pre_topc(C_280))) | ~l1_pre_topc(A_281))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.90/2.78  tff(c_1791, plain, (![A_281]: (m1_pre_topc('#skF_2', A_281) | ~m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), A_281) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_2'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(A_281))), inference(superposition, [status(thm), theory('equality')], [c_371, c_1782])).
% 7.90/2.78  tff(c_1797, plain, (![A_282]: (m1_pre_topc('#skF_2', A_282) | ~m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), A_282) | ~l1_pre_topc(A_282))), inference(demodulation, [status(thm), theory('equality')], [c_394, c_371, c_1357, c_371, c_76, c_74, c_1791])).
% 7.90/2.78  tff(c_1800, plain, (m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2'))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(resolution, [status(thm)], [c_1605, c_1797])).
% 7.90/2.78  tff(c_1809, plain, (m1_pre_topc('#skF_2', g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1800])).
% 7.90/2.78  tff(c_1811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1530, c_1809])).
% 7.90/2.78  tff(c_1812, plain, (u1_struct_0(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')))=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1428])).
% 7.90/2.78  tff(c_431, plain, (![B_159, A_160]: (r1_tarski(u1_struct_0(B_159), u1_struct_0(A_160)) | ~m1_pre_topc(B_159, A_160) | ~l1_pre_topc(A_160))), inference(resolution, [status(thm)], [c_421, c_8])).
% 7.90/2.78  tff(c_2083, plain, (![A_292]: (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_292)) | ~m1_pre_topc(g1_pre_topc(k1_relat_1('#skF_4'), u1_pre_topc('#skF_2')), A_292) | ~l1_pre_topc(A_292))), inference(superposition, [status(thm), theory('equality')], [c_1812, c_431])).
% 7.90/2.78  tff(c_2098, plain, (![A_293]: (r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(A_293)) | ~m1_pre_topc('#skF_3', A_293) | ~l1_pre_topc(A_293))), inference(resolution, [status(thm)], [c_1338, c_2083])).
% 7.90/2.78  tff(c_486, plain, (![B_162]: (u1_struct_0(B_162)=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(B_162)) | ~m1_pre_topc(B_162, '#skF_2'))), inference(resolution, [status(thm)], [c_480, c_2])).
% 7.90/2.78  tff(c_2206, plain, (![A_299]: (u1_struct_0(A_299)=k1_relat_1('#skF_4') | ~m1_pre_topc(A_299, '#skF_2') | ~m1_pre_topc('#skF_3', A_299) | ~l1_pre_topc(A_299))), inference(resolution, [status(thm)], [c_2098, c_486])).
% 7.90/2.78  tff(c_2219, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2206])).
% 7.90/2.78  tff(c_2234, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1966, c_2219])).
% 7.90/2.78  tff(c_3404, plain, (![C_366, A_367]: (m1_pre_topc('#skF_2', C_366) | ~r1_tarski(k1_relat_1('#skF_4'), u1_struct_0(C_366)) | ~m1_pre_topc(C_366, A_367) | ~m1_pre_topc('#skF_2', A_367) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367))), inference(superposition, [status(thm), theory('equality')], [c_371, c_1926])).
% 7.90/2.78  tff(c_3410, plain, (![A_367]: (m1_pre_topc('#skF_2', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~m1_pre_topc('#skF_3', A_367) | ~m1_pre_topc('#skF_2', A_367) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367))), inference(superposition, [status(thm), theory('equality')], [c_2234, c_3404])).
% 7.90/2.78  tff(c_3421, plain, (![A_367]: (m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', A_367) | ~m1_pre_topc('#skF_2', A_367) | ~l1_pre_topc(A_367) | ~v2_pre_topc(A_367))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3410])).
% 7.90/2.78  tff(c_3427, plain, (![A_368]: (~m1_pre_topc('#skF_3', A_368) | ~m1_pre_topc('#skF_2', A_368) | ~l1_pre_topc(A_368) | ~v2_pre_topc(A_368))), inference(negUnitSimplification, [status(thm)], [c_1441, c_3421])).
% 7.90/2.78  tff(c_3433, plain, (~m1_pre_topc('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_1221, c_3427])).
% 7.90/2.78  tff(c_3440, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_3433])).
% 7.90/2.78  tff(c_3441, plain, (u1_struct_0('#skF_3')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_1440])).
% 7.90/2.78  tff(c_82, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_1383, plain, (![A_237, B_238, C_239, D_240]: (k2_partfun1(A_237, B_238, C_239, D_240)=k7_relat_1(C_239, D_240) | ~m1_subset_1(C_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~v1_funct_1(C_239))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.90/2.78  tff(c_1385, plain, (![D_240]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_240)=k7_relat_1('#skF_4', D_240) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_377, c_1383])).
% 7.90/2.78  tff(c_1391, plain, (![D_240]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', D_240)=k7_relat_1('#skF_4', D_240))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1385])).
% 7.90/2.78  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_4391, plain, (![A_427, B_428, C_429, D_430]: (k2_partfun1(u1_struct_0(A_427), u1_struct_0(B_428), C_429, u1_struct_0(D_430))=k2_tmap_1(A_427, B_428, C_429, D_430) | ~m1_pre_topc(D_430, A_427) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_427), u1_struct_0(B_428)))) | ~v1_funct_2(C_429, u1_struct_0(A_427), u1_struct_0(B_428)) | ~v1_funct_1(C_429) | ~l1_pre_topc(B_428) | ~v2_pre_topc(B_428) | v2_struct_0(B_428) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(cnfTransformation, [status(thm)], [f_155])).
% 7.90/2.78  tff(c_4401, plain, (![B_428, C_429, D_430]: (k2_partfun1(u1_struct_0('#skF_2'), u1_struct_0(B_428), C_429, u1_struct_0(D_430))=k2_tmap_1('#skF_2', B_428, C_429, D_430) | ~m1_pre_topc(D_430, '#skF_2') | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_428)))) | ~v1_funct_2(C_429, u1_struct_0('#skF_2'), u1_struct_0(B_428)) | ~v1_funct_1(C_429) | ~l1_pre_topc(B_428) | ~v2_pre_topc(B_428) | v2_struct_0(B_428) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_4391])).
% 7.90/2.78  tff(c_4418, plain, (![B_428, C_429, D_430]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_428), C_429, u1_struct_0(D_430))=k2_tmap_1('#skF_2', B_428, C_429, D_430) | ~m1_pre_topc(D_430, '#skF_2') | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_428)))) | ~v1_funct_2(C_429, k1_relat_1('#skF_4'), u1_struct_0(B_428)) | ~v1_funct_1(C_429) | ~l1_pre_topc(B_428) | ~v2_pre_topc(B_428) | v2_struct_0(B_428) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_371, c_371, c_4401])).
% 7.90/2.78  tff(c_4713, plain, (![B_452, C_453, D_454]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0(B_452), C_453, u1_struct_0(D_454))=k2_tmap_1('#skF_2', B_452, C_453, D_454) | ~m1_pre_topc(D_454, '#skF_2') | ~m1_subset_1(C_453, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0(B_452)))) | ~v1_funct_2(C_453, k1_relat_1('#skF_4'), u1_struct_0(B_452)) | ~v1_funct_1(C_453) | ~l1_pre_topc(B_452) | ~v2_pre_topc(B_452) | v2_struct_0(B_452))), inference(negUnitSimplification, [status(thm)], [c_78, c_4418])).
% 7.90/2.78  tff(c_4719, plain, (![D_454]: (k2_partfun1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', u1_struct_0(D_454))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_454) | ~m1_pre_topc(D_454, '#skF_2') | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_377, c_4713])).
% 7.90/2.78  tff(c_4732, plain, (![D_454]: (k7_relat_1('#skF_4', u1_struct_0(D_454))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_454) | ~m1_pre_topc(D_454, '#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_68, c_378, c_1391, c_4719])).
% 7.90/2.78  tff(c_4739, plain, (![D_455]: (k7_relat_1('#skF_4', u1_struct_0(D_455))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', D_455) | ~m1_pre_topc(D_455, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_84, c_4732])).
% 7.90/2.78  tff(c_4760, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3441, c_4739])).
% 7.90/2.78  tff(c_4771, plain, (k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1292, c_4760])).
% 7.90/2.78  tff(c_60, plain, (~r1_funct_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_236])).
% 7.90/2.78  tff(c_373, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), u1_struct_0('#skF_3'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_371, c_60])).
% 7.90/2.78  tff(c_3461, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', k2_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3441, c_373])).
% 7.90/2.78  tff(c_4778, plain, (~r1_funct_2(k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), k1_relat_1('#skF_4'), u1_struct_0('#skF_1'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4771, c_3461])).
% 7.90/2.78  tff(c_6292, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1')) | ~r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6289, c_4778])).
% 7.90/2.78  tff(c_6297, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_376, c_378, c_6292])).
% 7.90/2.78  tff(c_6299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4338, c_6297])).
% 7.90/2.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/2.78  
% 7.90/2.78  Inference rules
% 7.90/2.78  ----------------------
% 7.90/2.78  #Ref     : 0
% 7.90/2.78  #Sup     : 1271
% 7.90/2.78  #Fact    : 0
% 7.90/2.78  #Define  : 0
% 7.90/2.78  #Split   : 32
% 7.90/2.78  #Chain   : 0
% 7.90/2.78  #Close   : 0
% 7.90/2.78  
% 7.90/2.78  Ordering : KBO
% 7.90/2.78  
% 7.90/2.78  Simplification rules
% 7.90/2.78  ----------------------
% 7.90/2.78  #Subsume      : 212
% 7.90/2.78  #Demod        : 2382
% 7.90/2.78  #Tautology    : 582
% 7.90/2.78  #SimpNegUnit  : 43
% 7.90/2.78  #BackRed      : 41
% 7.90/2.78  
% 7.90/2.78  #Partial instantiations: 0
% 7.90/2.78  #Strategies tried      : 1
% 7.90/2.78  
% 7.90/2.78  Timing (in seconds)
% 7.90/2.78  ----------------------
% 7.90/2.79  Preprocessing        : 0.62
% 7.90/2.79  Parsing              : 0.33
% 7.90/2.79  CNF conversion       : 0.05
% 7.90/2.79  Main loop            : 1.34
% 7.90/2.79  Inferencing          : 0.41
% 7.90/2.79  Reduction            : 0.52
% 7.90/2.79  Demodulation         : 0.39
% 7.90/2.79  BG Simplification    : 0.06
% 7.90/2.79  Subsumption          : 0.25
% 7.90/2.79  Abstraction          : 0.06
% 7.90/2.79  MUC search           : 0.00
% 7.90/2.79  Cooper               : 0.00
% 7.90/2.79  Total                : 2.03
% 7.90/2.79  Index Insertion      : 0.00
% 7.90/2.79  Index Deletion       : 0.00
% 7.90/2.79  Index Matching       : 0.00
% 7.90/2.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
