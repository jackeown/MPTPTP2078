%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:33 EST 2020

% Result     : Theorem 26.36s
% Output     : CNFRefutation 26.54s
% Verified   : 
% Statistics : Number of formulae       :  197 (8611 expanded)
%              Number of leaves         :   52 (3008 expanded)
%              Depth                    :   23
%              Number of atoms          :  567 (41336 expanded)
%              Number of equality atoms :   66 (5251 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_315,negated_conjecture,(
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
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_212,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_124,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v3_pre_topc(B,A)
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
        <=> ( v3_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
            & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

tff(f_201,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_151,axiom,(
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

tff(f_183,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_208,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_254,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(c_62,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_94,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_80,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_145,plain,(
    ! [B_287,A_288] :
      ( l1_pre_topc(B_287)
      | ~ m1_pre_topc(B_287,A_288)
      | ~ l1_pre_topc(A_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_145])).

tff(c_158,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_151])).

tff(c_12,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,(
    ! [A_285] :
      ( u1_struct_0(A_285) = k2_struct_0(A_285)
      | ~ l1_struct_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_126,plain,(
    ! [A_8] :
      ( u1_struct_0(A_8) = k2_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_122])).

tff(c_165,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_158,c_126])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_170,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_70])).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_96,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_84,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_154,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_145])).

tff(c_161,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_154])).

tff(c_54,plain,(
    ! [A_90] :
      ( m1_pre_topc(A_90,A_90)
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_212])).

tff(c_188,plain,(
    ! [B_290,A_291] :
      ( v2_pre_topc(B_290)
      | ~ m1_pre_topc(B_290,A_291)
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_197,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_188])).

tff(c_204,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_197])).

tff(c_169,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_161,c_126])).

tff(c_72,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_176,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_72])).

tff(c_247,plain,(
    ! [A_294] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_294),u1_pre_topc(A_294)))
      | ~ l1_pre_topc(A_294)
      | ~ v2_pre_topc(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_250,plain,
    ( v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_247])).

tff(c_261,plain,(
    v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_161,c_176,c_250])).

tff(c_268,plain,(
    ! [A_295] :
      ( g1_pre_topc(u1_struct_0(A_295),u1_pre_topc(A_295)) = A_295
      | ~ v1_pre_topc(A_295)
      | ~ l1_pre_topc(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_286,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_268])).

tff(c_298,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_261,c_286])).

tff(c_205,plain,(
    ! [A_292] :
      ( m1_subset_1(u1_pre_topc(A_292),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_292))))
      | ~ l1_pre_topc(A_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_208,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_205])).

tff(c_219,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_208])).

tff(c_386,plain,(
    ! [C_300,A_301,D_302,B_303] :
      ( C_300 = A_301
      | g1_pre_topc(C_300,D_302) != g1_pre_topc(A_301,B_303)
      | ~ m1_subset_1(B_303,k1_zfmisc_1(k1_zfmisc_1(A_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_398,plain,(
    ! [C_300,D_302] :
      ( k2_struct_0('#skF_3') = C_300
      | g1_pre_topc(C_300,D_302) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_386])).

tff(c_403,plain,(
    ! [C_304,D_305] :
      ( k2_struct_0('#skF_3') = C_304
      | g1_pre_topc(C_304,D_305) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_398])).

tff(c_413,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_403])).

tff(c_418,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_176])).

tff(c_211,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_205])).

tff(c_221,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_211])).

tff(c_500,plain,(
    ! [D_308,B_309,C_310,A_311] :
      ( D_308 = B_309
      | g1_pre_topc(C_310,D_308) != g1_pre_topc(A_311,B_309)
      | ~ m1_subset_1(B_309,k1_zfmisc_1(k1_zfmisc_1(A_311))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_508,plain,(
    ! [D_308,C_310] :
      ( u1_pre_topc('#skF_4') = D_308
      | g1_pre_topc(C_310,D_308) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_500])).

tff(c_515,plain,(
    ! [D_312,C_313] :
      ( u1_pre_topc('#skF_4') = D_312
      | g1_pre_topc(C_313,D_312) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_508])).

tff(c_525,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_418,c_515])).

tff(c_420,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_169])).

tff(c_723,plain,(
    ! [A_326,B_327] :
      ( m1_pre_topc(A_326,g1_pre_topc(u1_struct_0(B_327),u1_pre_topc(B_327)))
      | ~ m1_pre_topc(A_326,B_327)
      | ~ l1_pre_topc(B_327)
      | ~ l1_pre_topc(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_744,plain,(
    ! [A_326] :
      ( m1_pre_topc(A_326,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_326,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_326) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_723])).

tff(c_774,plain,(
    ! [A_328] :
      ( m1_pre_topc(A_328,'#skF_4')
      | ~ m1_pre_topc(A_328,'#skF_3')
      | ~ l1_pre_topc(A_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_298,c_525,c_744])).

tff(c_785,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_774])).

tff(c_792,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_785])).

tff(c_194,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_188])).

tff(c_201,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_194])).

tff(c_40,plain,(
    ! [A_33] :
      ( v3_pre_topc(k2_struct_0(A_33),A_33)
      | ~ l1_pre_topc(A_33)
      | ~ v2_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_425,plain,
    ( v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_40])).

tff(c_429,plain,(
    v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_161,c_425])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_961,plain,(
    ! [B_337,A_338] :
      ( v3_pre_topc(B_337,g1_pre_topc(u1_struct_0(A_338),u1_pre_topc(A_338)))
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0(A_338)))
      | ~ v3_pre_topc(B_337,A_338)
      | ~ l1_pre_topc(A_338)
      | ~ v2_pre_topc(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_967,plain,(
    ! [B_337] :
      ( v3_pre_topc(B_337,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))
      | ~ m1_subset_1(B_337,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ v3_pre_topc(B_337,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_961])).

tff(c_1083,plain,(
    ! [B_345] :
      ( v3_pre_topc(B_345,'#skF_4')
      | ~ m1_subset_1(B_345,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_345,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_161,c_420,c_298,c_525,c_967])).

tff(c_1093,plain,
    ( v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_101,c_1083])).

tff(c_1098,plain,(
    v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_1093])).

tff(c_1304,plain,(
    ! [B_356,A_357] :
      ( v1_tsep_1(B_356,A_357)
      | ~ v3_pre_topc(u1_struct_0(B_356),A_357)
      | ~ m1_subset_1(u1_struct_0(B_356),k1_zfmisc_1(u1_struct_0(A_357)))
      | ~ m1_pre_topc(B_356,A_357)
      | ~ l1_pre_topc(A_357)
      | ~ v2_pre_topc(A_357) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_1499,plain,(
    ! [B_365] :
      ( v1_tsep_1(B_365,B_365)
      | ~ v3_pre_topc(u1_struct_0(B_365),B_365)
      | ~ m1_pre_topc(B_365,B_365)
      | ~ l1_pre_topc(B_365)
      | ~ v2_pre_topc(B_365) ) ),
    inference(resolution,[status(thm)],[c_101,c_1304])).

tff(c_1509,plain,
    ( v1_tsep_1('#skF_4','#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_1499])).

tff(c_1520,plain,
    ( v1_tsep_1('#skF_4','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_158,c_1098,c_1509])).

tff(c_1636,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1520])).

tff(c_1694,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1636])).

tff(c_1698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_1694])).

tff(c_1700,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1520])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_88,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_127,plain,(
    ! [A_286] :
      ( u1_struct_0(A_286) = k2_struct_0(A_286)
      | ~ l1_pre_topc(A_286) ) ),
    inference(resolution,[status(thm)],[c_12,c_122])).

tff(c_135,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_127])).

tff(c_76,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_140,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_76])).

tff(c_182,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_140])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_175,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_135,c_74])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_90,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_1945,plain,(
    ! [A_376,B_377,C_378,D_379] :
      ( k2_partfun1(u1_struct_0(A_376),u1_struct_0(B_377),C_378,u1_struct_0(D_379)) = k2_tmap_1(A_376,B_377,C_378,D_379)
      | ~ m1_pre_topc(D_379,A_376)
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_376),u1_struct_0(B_377))))
      | ~ v1_funct_2(C_378,u1_struct_0(A_376),u1_struct_0(B_377))
      | ~ v1_funct_1(C_378)
      | ~ l1_pre_topc(B_377)
      | ~ v2_pre_topc(B_377)
      | v2_struct_0(B_377)
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_1951,plain,(
    ! [B_377,C_378,D_379] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_377),C_378,u1_struct_0(D_379)) = k2_tmap_1('#skF_4',B_377,C_378,D_379)
      | ~ m1_pre_topc(D_379,'#skF_4')
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_377))))
      | ~ v1_funct_2(C_378,u1_struct_0('#skF_4'),u1_struct_0(B_377))
      | ~ v1_funct_1(C_378)
      | ~ l1_pre_topc(B_377)
      | ~ v2_pre_topc(B_377)
      | v2_struct_0(B_377)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_1945])).

tff(c_1972,plain,(
    ! [B_377,C_378,D_379] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_377),C_378,u1_struct_0(D_379)) = k2_tmap_1('#skF_4',B_377,C_378,D_379)
      | ~ m1_pre_topc(D_379,'#skF_4')
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_377))))
      | ~ v1_funct_2(C_378,k2_struct_0('#skF_4'),u1_struct_0(B_377))
      | ~ v1_funct_1(C_378)
      | ~ l1_pre_topc(B_377)
      | ~ v2_pre_topc(B_377)
      | v2_struct_0(B_377)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_158,c_165,c_165,c_1951])).

tff(c_3963,plain,(
    ! [B_501,C_502,D_503] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_501),C_502,u1_struct_0(D_503)) = k2_tmap_1('#skF_4',B_501,C_502,D_503)
      | ~ m1_pre_topc(D_503,'#skF_4')
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_501))))
      | ~ v1_funct_2(C_502,k2_struct_0('#skF_4'),u1_struct_0(B_501))
      | ~ v1_funct_1(C_502)
      | ~ l1_pre_topc(B_501)
      | ~ v2_pre_topc(B_501)
      | v2_struct_0(B_501) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1972])).

tff(c_3969,plain,(
    ! [C_502,D_503] :
      ( k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),C_502,u1_struct_0(D_503)) = k2_tmap_1('#skF_4','#skF_2',C_502,D_503)
      | ~ m1_pre_topc(D_503,'#skF_4')
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_502,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(C_502)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_3963])).

tff(c_3982,plain,(
    ! [C_502,D_503] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_502,u1_struct_0(D_503)) = k2_tmap_1('#skF_4','#skF_2',C_502,D_503)
      | ~ m1_pre_topc(D_503,'#skF_4')
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_502,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_502)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_135,c_135,c_3969])).

tff(c_4297,plain,(
    ! [C_514,D_515] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),C_514,u1_struct_0(D_515)) = k2_tmap_1('#skF_4','#skF_2',C_514,D_515)
      | ~ m1_pre_topc(D_515,'#skF_4')
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(C_514,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(C_514) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_3982])).

tff(c_4299,plain,(
    ! [D_515] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_515)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_515)
      | ~ m1_pre_topc(D_515,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_175,c_4297])).

tff(c_4307,plain,(
    ! [D_516] :
      ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_516)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_516)
      | ~ m1_pre_topc(D_516,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_182,c_4299])).

tff(c_4319,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_4307])).

tff(c_4331,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1700,c_4319])).

tff(c_2090,plain,(
    ! [A_386,B_383,C_387,D_385,E_384] :
      ( k3_tmap_1(A_386,B_383,C_387,D_385,E_384) = k2_partfun1(u1_struct_0(C_387),u1_struct_0(B_383),E_384,u1_struct_0(D_385))
      | ~ m1_pre_topc(D_385,C_387)
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_387),u1_struct_0(B_383))))
      | ~ v1_funct_2(E_384,u1_struct_0(C_387),u1_struct_0(B_383))
      | ~ v1_funct_1(E_384)
      | ~ m1_pre_topc(D_385,A_386)
      | ~ m1_pre_topc(C_387,A_386)
      | ~ l1_pre_topc(B_383)
      | ~ v2_pre_topc(B_383)
      | v2_struct_0(B_383)
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2096,plain,(
    ! [A_386,B_383,D_385,E_384] :
      ( k3_tmap_1(A_386,B_383,'#skF_4',D_385,E_384) = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0(B_383),E_384,u1_struct_0(D_385))
      | ~ m1_pre_topc(D_385,'#skF_4')
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_383))))
      | ~ v1_funct_2(E_384,u1_struct_0('#skF_4'),u1_struct_0(B_383))
      | ~ v1_funct_1(E_384)
      | ~ m1_pre_topc(D_385,A_386)
      | ~ m1_pre_topc('#skF_4',A_386)
      | ~ l1_pre_topc(B_383)
      | ~ v2_pre_topc(B_383)
      | v2_struct_0(B_383)
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_2090])).

tff(c_40312,plain,(
    ! [A_1098,B_1099,D_1100,E_1101] :
      ( k3_tmap_1(A_1098,B_1099,'#skF_4',D_1100,E_1101) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0(B_1099),E_1101,u1_struct_0(D_1100))
      | ~ m1_pre_topc(D_1100,'#skF_4')
      | ~ m1_subset_1(E_1101,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),u1_struct_0(B_1099))))
      | ~ v1_funct_2(E_1101,k2_struct_0('#skF_4'),u1_struct_0(B_1099))
      | ~ v1_funct_1(E_1101)
      | ~ m1_pre_topc(D_1100,A_1098)
      | ~ m1_pre_topc('#skF_4',A_1098)
      | ~ l1_pre_topc(B_1099)
      | ~ v2_pre_topc(B_1099)
      | v2_struct_0(B_1099)
      | ~ l1_pre_topc(A_1098)
      | ~ v2_pre_topc(A_1098)
      | v2_struct_0(A_1098) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_165,c_2096])).

tff(c_40324,plain,(
    ! [A_1098,D_1100,E_1101] :
      ( k3_tmap_1(A_1098,'#skF_2','#skF_4',D_1100,E_1101) = k2_partfun1(k2_struct_0('#skF_4'),u1_struct_0('#skF_2'),E_1101,u1_struct_0(D_1100))
      | ~ m1_pre_topc(D_1100,'#skF_4')
      | ~ m1_subset_1(E_1101,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_1101,k2_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_1101)
      | ~ m1_pre_topc(D_1100,A_1098)
      | ~ m1_pre_topc('#skF_4',A_1098)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1098)
      | ~ v2_pre_topc(A_1098)
      | v2_struct_0(A_1098) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_40312])).

tff(c_40337,plain,(
    ! [A_1098,D_1100,E_1101] :
      ( k3_tmap_1(A_1098,'#skF_2','#skF_4',D_1100,E_1101) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_1101,u1_struct_0(D_1100))
      | ~ m1_pre_topc(D_1100,'#skF_4')
      | ~ m1_subset_1(E_1101,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_1101,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_1101)
      | ~ m1_pre_topc(D_1100,A_1098)
      | ~ m1_pre_topc('#skF_4',A_1098)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_1098)
      | ~ v2_pre_topc(A_1098)
      | v2_struct_0(A_1098) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_135,c_135,c_40324])).

tff(c_59710,plain,(
    ! [A_1393,D_1394,E_1395] :
      ( k3_tmap_1(A_1393,'#skF_2','#skF_4',D_1394,E_1395) = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),E_1395,u1_struct_0(D_1394))
      | ~ m1_pre_topc(D_1394,'#skF_4')
      | ~ m1_subset_1(E_1395,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_1395,k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1(E_1395)
      | ~ m1_pre_topc(D_1394,A_1393)
      | ~ m1_pre_topc('#skF_4',A_1393)
      | ~ l1_pre_topc(A_1393)
      | ~ v2_pre_topc(A_1393)
      | v2_struct_0(A_1393) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_40337])).

tff(c_59712,plain,(
    ! [A_1393,D_1394] :
      ( k3_tmap_1(A_1393,'#skF_2','#skF_4',D_1394,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_1394))
      | ~ m1_pre_topc(D_1394,'#skF_4')
      | ~ v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_1394,A_1393)
      | ~ m1_pre_topc('#skF_4',A_1393)
      | ~ l1_pre_topc(A_1393)
      | ~ v2_pre_topc(A_1393)
      | v2_struct_0(A_1393) ) ),
    inference(resolution,[status(thm)],[c_175,c_59710])).

tff(c_59720,plain,(
    ! [A_1396,D_1397] :
      ( k3_tmap_1(A_1396,'#skF_2','#skF_4',D_1397,'#skF_5') = k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_1397))
      | ~ m1_pre_topc(D_1397,'#skF_4')
      | ~ m1_pre_topc(D_1397,A_1396)
      | ~ m1_pre_topc('#skF_4',A_1396)
      | ~ l1_pre_topc(A_1396)
      | ~ v2_pre_topc(A_1396)
      | v2_struct_0(A_1396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_182,c_59712])).

tff(c_59818,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_59720])).

tff(c_59940,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_80,c_792,c_4331,c_420,c_59818])).

tff(c_59941,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_59940])).

tff(c_66,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_64,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_100,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64])).

tff(c_59946,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59941,c_100])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_635,plain,(
    ! [A_321,B_322] :
      ( m1_pre_topc(A_321,B_322)
      | ~ m1_pre_topc(A_321,g1_pre_topc(u1_struct_0(B_322),u1_pre_topc(B_322)))
      | ~ l1_pre_topc(B_322)
      | ~ l1_pre_topc(A_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_645,plain,(
    ! [A_321] :
      ( m1_pre_topc(A_321,'#skF_3')
      | ~ m1_pre_topc(A_321,g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_321) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_635])).

tff(c_668,plain,(
    ! [A_321] :
      ( m1_pre_topc(A_321,'#skF_3')
      | ~ m1_pre_topc(A_321,'#skF_4')
      | ~ l1_pre_topc(A_321) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_298,c_525,c_645])).

tff(c_1506,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_1499])).

tff(c_1518,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_161,c_429,c_1506])).

tff(c_1525,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1518])).

tff(c_1531,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_668,c_1525])).

tff(c_1544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_792,c_1531])).

tff(c_1546,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1518])).

tff(c_1545,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_1518])).

tff(c_52,plain,(
    ! [B_89,A_87] :
      ( m1_subset_1(u1_struct_0(B_89),k1_zfmisc_1(u1_struct_0(A_87)))
      | ~ m1_pre_topc(B_89,A_87)
      | ~ l1_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1099,plain,(
    ! [B_346,A_347] :
      ( v3_pre_topc(u1_struct_0(B_346),A_347)
      | ~ v1_tsep_1(B_346,A_347)
      | ~ m1_subset_1(u1_struct_0(B_346),k1_zfmisc_1(u1_struct_0(A_347)))
      | ~ m1_pre_topc(B_346,A_347)
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_2200,plain,(
    ! [B_390,A_391] :
      ( v3_pre_topc(u1_struct_0(B_390),A_391)
      | ~ v1_tsep_1(B_390,A_391)
      | ~ v2_pre_topc(A_391)
      | ~ m1_pre_topc(B_390,A_391)
      | ~ l1_pre_topc(A_391) ) ),
    inference(resolution,[status(thm)],[c_52,c_1099])).

tff(c_303,plain,(
    ! [B_296,A_297] :
      ( m1_subset_1(u1_struct_0(B_296),k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ m1_pre_topc(B_296,A_297)
      | ~ l1_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_309,plain,(
    ! [B_296] :
      ( m1_subset_1(u1_struct_0(B_296),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_296,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_303])).

tff(c_329,plain,(
    ! [B_296] :
      ( m1_subset_1(u1_struct_0(B_296),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_296,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_309])).

tff(c_587,plain,(
    ! [B_296] :
      ( m1_subset_1(u1_struct_0(B_296),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_296,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_329])).

tff(c_1094,plain,(
    ! [B_296] :
      ( v3_pre_topc(u1_struct_0(B_296),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_296),'#skF_3')
      | ~ m1_pre_topc(B_296,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_587,c_1083])).

tff(c_2212,plain,(
    ! [B_390] :
      ( v3_pre_topc(u1_struct_0(B_390),'#skF_4')
      | ~ v1_tsep_1(B_390,'#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_390,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2200,c_1094])).

tff(c_2231,plain,(
    ! [B_390] :
      ( v3_pre_topc(u1_struct_0(B_390),'#skF_4')
      | ~ v1_tsep_1(B_390,'#skF_3')
      | ~ m1_pre_topc(B_390,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_204,c_2212])).

tff(c_2280,plain,(
    ! [B_396,A_397] :
      ( v1_tsep_1(B_396,A_397)
      | ~ v3_pre_topc(u1_struct_0(B_396),A_397)
      | ~ v2_pre_topc(A_397)
      | ~ m1_pre_topc(B_396,A_397)
      | ~ l1_pre_topc(A_397) ) ),
    inference(resolution,[status(thm)],[c_52,c_1304])).

tff(c_2283,plain,(
    ! [B_390] :
      ( v1_tsep_1(B_390,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_390,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_tsep_1(B_390,'#skF_3')
      | ~ m1_pre_topc(B_390,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2231,c_2280])).

tff(c_2459,plain,(
    ! [B_408] :
      ( v1_tsep_1(B_408,'#skF_4')
      | ~ m1_pre_topc(B_408,'#skF_4')
      | ~ v1_tsep_1(B_408,'#skF_3')
      | ~ m1_pre_topc(B_408,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_201,c_2283])).

tff(c_2468,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1545,c_2459])).

tff(c_2475,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1546,c_792,c_2468])).

tff(c_4316,plain,
    ( k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_4307])).

tff(c_4329,plain,(
    k2_partfun1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2'),'#skF_5',k2_struct_0('#skF_4')) = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_4316])).

tff(c_4336,plain,(
    k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4331,c_4329])).

tff(c_56,plain,(
    ! [F_153,D_147,A_91,C_139,B_123] :
      ( r1_tmap_1(B_123,A_91,C_139,F_153)
      | ~ r1_tmap_1(D_147,A_91,k2_tmap_1(B_123,A_91,C_139,D_147),F_153)
      | ~ m1_subset_1(F_153,u1_struct_0(D_147))
      | ~ m1_subset_1(F_153,u1_struct_0(B_123))
      | ~ m1_pre_topc(D_147,B_123)
      | ~ v1_tsep_1(D_147,B_123)
      | v2_struct_0(D_147)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_123),u1_struct_0(A_91))))
      | ~ v1_funct_2(C_139,u1_struct_0(B_123),u1_struct_0(A_91))
      | ~ v1_funct_1(C_139)
      | ~ l1_pre_topc(B_123)
      | ~ v2_pre_topc(B_123)
      | v2_struct_0(B_123)
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_4343,plain,(
    ! [F_153] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_153)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_153)
      | ~ m1_subset_1(F_153,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_153,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ v1_tsep_1('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4336,c_56])).

tff(c_4347,plain,(
    ! [F_153] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_153)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_153)
      | ~ m1_subset_1(F_153,k2_struct_0('#skF_4'))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_201,c_158,c_78,c_182,c_135,c_165,c_175,c_135,c_165,c_2475,c_792,c_165,c_420,c_4343])).

tff(c_4348,plain,(
    ! [F_153] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5',F_153)
      | ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_4'),F_153)
      | ~ m1_subset_1(F_153,k2_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_82,c_86,c_4347])).

tff(c_59956,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_59946,c_4348])).

tff(c_59962,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_59956])).

tff(c_59964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_59962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:08:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.36/16.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.47/16.53  
% 26.47/16.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.47/16.53  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 26.47/16.53  
% 26.47/16.53  %Foreground sorts:
% 26.47/16.53  
% 26.47/16.53  
% 26.47/16.53  %Background operators:
% 26.47/16.53  
% 26.47/16.53  
% 26.47/16.53  %Foreground operators:
% 26.47/16.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 26.47/16.53  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 26.47/16.53  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 26.47/16.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 26.47/16.53  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 26.47/16.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.47/16.53  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 26.47/16.53  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 26.47/16.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 26.47/16.53  tff('#skF_7', type, '#skF_7': $i).
% 26.47/16.53  tff('#skF_5', type, '#skF_5': $i).
% 26.47/16.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 26.47/16.53  tff('#skF_6', type, '#skF_6': $i).
% 26.47/16.53  tff('#skF_2', type, '#skF_2': $i).
% 26.47/16.53  tff('#skF_3', type, '#skF_3': $i).
% 26.47/16.53  tff('#skF_1', type, '#skF_1': $i).
% 26.47/16.53  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 26.47/16.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 26.47/16.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 26.47/16.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.47/16.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 26.47/16.53  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 26.47/16.53  tff('#skF_4', type, '#skF_4': $i).
% 26.47/16.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.47/16.53  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 26.47/16.53  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 26.47/16.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 26.47/16.53  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 26.47/16.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 26.47/16.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 26.47/16.53  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 26.47/16.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 26.47/16.53  
% 26.54/16.56  tff(f_315, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 26.54/16.56  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 26.54/16.56  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 26.54/16.56  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 26.54/16.56  tff(f_212, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 26.54/16.56  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 26.54/16.56  tff(f_71, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 26.54/16.56  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 26.54/16.56  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 26.54/16.56  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 26.54/16.56  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 26.54/16.56  tff(f_124, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 26.54/16.56  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 26.54/16.56  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 26.54/16.56  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: ((v3_pre_topc(B, A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) <=> (v3_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 26.54/16.56  tff(f_201, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 26.54/16.56  tff(f_151, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 26.54/16.56  tff(f_183, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 26.54/16.56  tff(f_208, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 26.54/16.56  tff(f_254, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 26.54/16.56  tff(c_62, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_94, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_80, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_145, plain, (![B_287, A_288]: (l1_pre_topc(B_287) | ~m1_pre_topc(B_287, A_288) | ~l1_pre_topc(A_288))), inference(cnfTransformation, [status(thm)], [f_59])).
% 26.54/16.56  tff(c_151, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_80, c_145])).
% 26.54/16.56  tff(c_158, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_151])).
% 26.54/16.56  tff(c_12, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 26.54/16.56  tff(c_122, plain, (![A_285]: (u1_struct_0(A_285)=k2_struct_0(A_285) | ~l1_struct_0(A_285))), inference(cnfTransformation, [status(thm)], [f_48])).
% 26.54/16.56  tff(c_126, plain, (![A_8]: (u1_struct_0(A_8)=k2_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(resolution, [status(thm)], [c_12, c_122])).
% 26.54/16.56  tff(c_165, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_158, c_126])).
% 26.54/16.56  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_170, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_70])).
% 26.54/16.56  tff(c_98, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_96, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_84, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_154, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84, c_145])).
% 26.54/16.56  tff(c_161, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_154])).
% 26.54/16.56  tff(c_54, plain, (![A_90]: (m1_pre_topc(A_90, A_90) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_212])).
% 26.54/16.56  tff(c_188, plain, (![B_290, A_291]: (v2_pre_topc(B_290) | ~m1_pre_topc(B_290, A_291) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291))), inference(cnfTransformation, [status(thm)], [f_44])).
% 26.54/16.56  tff(c_197, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_84, c_188])).
% 26.54/16.56  tff(c_204, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_197])).
% 26.54/16.56  tff(c_169, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_161, c_126])).
% 26.54/16.56  tff(c_72, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_176, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_72])).
% 26.54/16.56  tff(c_247, plain, (![A_294]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_294), u1_pre_topc(A_294))) | ~l1_pre_topc(A_294) | ~v2_pre_topc(A_294))), inference(cnfTransformation, [status(thm)], [f_71])).
% 26.54/16.56  tff(c_250, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_169, c_247])).
% 26.54/16.56  tff(c_261, plain, (v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_161, c_176, c_250])).
% 26.54/16.56  tff(c_268, plain, (![A_295]: (g1_pre_topc(u1_struct_0(A_295), u1_pre_topc(A_295))=A_295 | ~v1_pre_topc(A_295) | ~l1_pre_topc(A_295))), inference(cnfTransformation, [status(thm)], [f_35])).
% 26.54/16.56  tff(c_286, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_165, c_268])).
% 26.54/16.56  tff(c_298, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_261, c_286])).
% 26.54/16.56  tff(c_205, plain, (![A_292]: (m1_subset_1(u1_pre_topc(A_292), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_292)))) | ~l1_pre_topc(A_292))), inference(cnfTransformation, [status(thm)], [f_63])).
% 26.54/16.56  tff(c_208, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_169, c_205])).
% 26.54/16.56  tff(c_219, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_208])).
% 26.54/16.56  tff(c_386, plain, (![C_300, A_301, D_302, B_303]: (C_300=A_301 | g1_pre_topc(C_300, D_302)!=g1_pre_topc(A_301, B_303) | ~m1_subset_1(B_303, k1_zfmisc_1(k1_zfmisc_1(A_301))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 26.54/16.56  tff(c_398, plain, (![C_300, D_302]: (k2_struct_0('#skF_3')=C_300 | g1_pre_topc(C_300, D_302)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_176, c_386])).
% 26.54/16.56  tff(c_403, plain, (![C_304, D_305]: (k2_struct_0('#skF_3')=C_304 | g1_pre_topc(C_304, D_305)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_398])).
% 26.54/16.56  tff(c_413, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_298, c_403])).
% 26.54/16.56  tff(c_418, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_413, c_176])).
% 26.54/16.56  tff(c_211, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_165, c_205])).
% 26.54/16.56  tff(c_221, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_211])).
% 26.54/16.56  tff(c_500, plain, (![D_308, B_309, C_310, A_311]: (D_308=B_309 | g1_pre_topc(C_310, D_308)!=g1_pre_topc(A_311, B_309) | ~m1_subset_1(B_309, k1_zfmisc_1(k1_zfmisc_1(A_311))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 26.54/16.56  tff(c_508, plain, (![D_308, C_310]: (u1_pre_topc('#skF_4')=D_308 | g1_pre_topc(C_310, D_308)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_298, c_500])).
% 26.54/16.56  tff(c_515, plain, (![D_312, C_313]: (u1_pre_topc('#skF_4')=D_312 | g1_pre_topc(C_313, D_312)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_508])).
% 26.54/16.56  tff(c_525, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_418, c_515])).
% 26.54/16.56  tff(c_420, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_169])).
% 26.54/16.56  tff(c_723, plain, (![A_326, B_327]: (m1_pre_topc(A_326, g1_pre_topc(u1_struct_0(B_327), u1_pre_topc(B_327))) | ~m1_pre_topc(A_326, B_327) | ~l1_pre_topc(B_327) | ~l1_pre_topc(A_326))), inference(cnfTransformation, [status(thm)], [f_118])).
% 26.54/16.56  tff(c_744, plain, (![A_326]: (m1_pre_topc(A_326, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_326, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_326))), inference(superposition, [status(thm), theory('equality')], [c_420, c_723])).
% 26.54/16.56  tff(c_774, plain, (![A_328]: (m1_pre_topc(A_328, '#skF_4') | ~m1_pre_topc(A_328, '#skF_3') | ~l1_pre_topc(A_328))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_298, c_525, c_744])).
% 26.54/16.56  tff(c_785, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_54, c_774])).
% 26.54/16.56  tff(c_792, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_161, c_785])).
% 26.54/16.56  tff(c_194, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_80, c_188])).
% 26.54/16.56  tff(c_201, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_194])).
% 26.54/16.56  tff(c_40, plain, (![A_33]: (v3_pre_topc(k2_struct_0(A_33), A_33) | ~l1_pre_topc(A_33) | ~v2_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_124])).
% 26.54/16.56  tff(c_425, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_413, c_40])).
% 26.54/16.56  tff(c_429, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_161, c_425])).
% 26.54/16.56  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 26.54/16.56  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 26.54/16.56  tff(c_101, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 26.54/16.56  tff(c_961, plain, (![B_337, A_338]: (v3_pre_topc(B_337, g1_pre_topc(u1_struct_0(A_338), u1_pre_topc(A_338))) | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0(A_338))) | ~v3_pre_topc(B_337, A_338) | ~l1_pre_topc(A_338) | ~v2_pre_topc(A_338))), inference(cnfTransformation, [status(thm)], [f_109])).
% 26.54/16.56  tff(c_967, plain, (![B_337]: (v3_pre_topc(B_337, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))) | ~m1_subset_1(B_337, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~v3_pre_topc(B_337, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_420, c_961])).
% 26.54/16.56  tff(c_1083, plain, (![B_345]: (v3_pre_topc(B_345, '#skF_4') | ~m1_subset_1(B_345, k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~v3_pre_topc(B_345, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_161, c_420, c_298, c_525, c_967])).
% 26.54/16.56  tff(c_1093, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_101, c_1083])).
% 26.54/16.56  tff(c_1098, plain, (v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_429, c_1093])).
% 26.54/16.56  tff(c_1304, plain, (![B_356, A_357]: (v1_tsep_1(B_356, A_357) | ~v3_pre_topc(u1_struct_0(B_356), A_357) | ~m1_subset_1(u1_struct_0(B_356), k1_zfmisc_1(u1_struct_0(A_357))) | ~m1_pre_topc(B_356, A_357) | ~l1_pre_topc(A_357) | ~v2_pre_topc(A_357))), inference(cnfTransformation, [status(thm)], [f_201])).
% 26.54/16.56  tff(c_1499, plain, (![B_365]: (v1_tsep_1(B_365, B_365) | ~v3_pre_topc(u1_struct_0(B_365), B_365) | ~m1_pre_topc(B_365, B_365) | ~l1_pre_topc(B_365) | ~v2_pre_topc(B_365))), inference(resolution, [status(thm)], [c_101, c_1304])).
% 26.54/16.56  tff(c_1509, plain, (v1_tsep_1('#skF_4', '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_165, c_1499])).
% 26.54/16.56  tff(c_1520, plain, (v1_tsep_1('#skF_4', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_158, c_1098, c_1509])).
% 26.54/16.56  tff(c_1636, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_1520])).
% 26.54/16.56  tff(c_1694, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_54, c_1636])).
% 26.54/16.56  tff(c_1698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_158, c_1694])).
% 26.54/16.56  tff(c_1700, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_1520])).
% 26.54/16.56  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_88, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_127, plain, (![A_286]: (u1_struct_0(A_286)=k2_struct_0(A_286) | ~l1_pre_topc(A_286))), inference(resolution, [status(thm)], [c_12, c_122])).
% 26.54/16.56  tff(c_135, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_88, c_127])).
% 26.54/16.56  tff(c_76, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_140, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_76])).
% 26.54/16.56  tff(c_182, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_140])).
% 26.54/16.56  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_175, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_135, c_74])).
% 26.54/16.56  tff(c_92, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_90, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_82, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_1945, plain, (![A_376, B_377, C_378, D_379]: (k2_partfun1(u1_struct_0(A_376), u1_struct_0(B_377), C_378, u1_struct_0(D_379))=k2_tmap_1(A_376, B_377, C_378, D_379) | ~m1_pre_topc(D_379, A_376) | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_376), u1_struct_0(B_377)))) | ~v1_funct_2(C_378, u1_struct_0(A_376), u1_struct_0(B_377)) | ~v1_funct_1(C_378) | ~l1_pre_topc(B_377) | ~v2_pre_topc(B_377) | v2_struct_0(B_377) | ~l1_pre_topc(A_376) | ~v2_pre_topc(A_376) | v2_struct_0(A_376))), inference(cnfTransformation, [status(thm)], [f_151])).
% 26.54/16.56  tff(c_1951, plain, (![B_377, C_378, D_379]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_377), C_378, u1_struct_0(D_379))=k2_tmap_1('#skF_4', B_377, C_378, D_379) | ~m1_pre_topc(D_379, '#skF_4') | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_377)))) | ~v1_funct_2(C_378, u1_struct_0('#skF_4'), u1_struct_0(B_377)) | ~v1_funct_1(C_378) | ~l1_pre_topc(B_377) | ~v2_pre_topc(B_377) | v2_struct_0(B_377) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_1945])).
% 26.54/16.56  tff(c_1972, plain, (![B_377, C_378, D_379]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_377), C_378, u1_struct_0(D_379))=k2_tmap_1('#skF_4', B_377, C_378, D_379) | ~m1_pre_topc(D_379, '#skF_4') | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_377)))) | ~v1_funct_2(C_378, k2_struct_0('#skF_4'), u1_struct_0(B_377)) | ~v1_funct_1(C_378) | ~l1_pre_topc(B_377) | ~v2_pre_topc(B_377) | v2_struct_0(B_377) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_201, c_158, c_165, c_165, c_1951])).
% 26.54/16.56  tff(c_3963, plain, (![B_501, C_502, D_503]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_501), C_502, u1_struct_0(D_503))=k2_tmap_1('#skF_4', B_501, C_502, D_503) | ~m1_pre_topc(D_503, '#skF_4') | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_501)))) | ~v1_funct_2(C_502, k2_struct_0('#skF_4'), u1_struct_0(B_501)) | ~v1_funct_1(C_502) | ~l1_pre_topc(B_501) | ~v2_pre_topc(B_501) | v2_struct_0(B_501))), inference(negUnitSimplification, [status(thm)], [c_82, c_1972])).
% 26.54/16.56  tff(c_3969, plain, (![C_502, D_503]: (k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), C_502, u1_struct_0(D_503))=k2_tmap_1('#skF_4', '#skF_2', C_502, D_503) | ~m1_pre_topc(D_503, '#skF_4') | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_502, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(C_502) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_3963])).
% 26.54/16.56  tff(c_3982, plain, (![C_502, D_503]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_502, u1_struct_0(D_503))=k2_tmap_1('#skF_4', '#skF_2', C_502, D_503) | ~m1_pre_topc(D_503, '#skF_4') | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_502, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_502) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_135, c_135, c_3969])).
% 26.54/16.56  tff(c_4297, plain, (![C_514, D_515]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), C_514, u1_struct_0(D_515))=k2_tmap_1('#skF_4', '#skF_2', C_514, D_515) | ~m1_pre_topc(D_515, '#skF_4') | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(C_514, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(C_514))), inference(negUnitSimplification, [status(thm)], [c_92, c_3982])).
% 26.54/16.56  tff(c_4299, plain, (![D_515]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_515))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_515) | ~m1_pre_topc(D_515, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_175, c_4297])).
% 26.54/16.56  tff(c_4307, plain, (![D_516]: (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_516))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_516) | ~m1_pre_topc(D_516, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_182, c_4299])).
% 26.54/16.56  tff(c_4319, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_165, c_4307])).
% 26.54/16.56  tff(c_4331, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1700, c_4319])).
% 26.54/16.56  tff(c_2090, plain, (![A_386, B_383, C_387, D_385, E_384]: (k3_tmap_1(A_386, B_383, C_387, D_385, E_384)=k2_partfun1(u1_struct_0(C_387), u1_struct_0(B_383), E_384, u1_struct_0(D_385)) | ~m1_pre_topc(D_385, C_387) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_387), u1_struct_0(B_383)))) | ~v1_funct_2(E_384, u1_struct_0(C_387), u1_struct_0(B_383)) | ~v1_funct_1(E_384) | ~m1_pre_topc(D_385, A_386) | ~m1_pre_topc(C_387, A_386) | ~l1_pre_topc(B_383) | ~v2_pre_topc(B_383) | v2_struct_0(B_383) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(cnfTransformation, [status(thm)], [f_183])).
% 26.54/16.56  tff(c_2096, plain, (![A_386, B_383, D_385, E_384]: (k3_tmap_1(A_386, B_383, '#skF_4', D_385, E_384)=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0(B_383), E_384, u1_struct_0(D_385)) | ~m1_pre_topc(D_385, '#skF_4') | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_383)))) | ~v1_funct_2(E_384, u1_struct_0('#skF_4'), u1_struct_0(B_383)) | ~v1_funct_1(E_384) | ~m1_pre_topc(D_385, A_386) | ~m1_pre_topc('#skF_4', A_386) | ~l1_pre_topc(B_383) | ~v2_pre_topc(B_383) | v2_struct_0(B_383) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(superposition, [status(thm), theory('equality')], [c_165, c_2090])).
% 26.54/16.56  tff(c_40312, plain, (![A_1098, B_1099, D_1100, E_1101]: (k3_tmap_1(A_1098, B_1099, '#skF_4', D_1100, E_1101)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0(B_1099), E_1101, u1_struct_0(D_1100)) | ~m1_pre_topc(D_1100, '#skF_4') | ~m1_subset_1(E_1101, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), u1_struct_0(B_1099)))) | ~v1_funct_2(E_1101, k2_struct_0('#skF_4'), u1_struct_0(B_1099)) | ~v1_funct_1(E_1101) | ~m1_pre_topc(D_1100, A_1098) | ~m1_pre_topc('#skF_4', A_1098) | ~l1_pre_topc(B_1099) | ~v2_pre_topc(B_1099) | v2_struct_0(B_1099) | ~l1_pre_topc(A_1098) | ~v2_pre_topc(A_1098) | v2_struct_0(A_1098))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_165, c_2096])).
% 26.54/16.56  tff(c_40324, plain, (![A_1098, D_1100, E_1101]: (k3_tmap_1(A_1098, '#skF_2', '#skF_4', D_1100, E_1101)=k2_partfun1(k2_struct_0('#skF_4'), u1_struct_0('#skF_2'), E_1101, u1_struct_0(D_1100)) | ~m1_pre_topc(D_1100, '#skF_4') | ~m1_subset_1(E_1101, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_1101, k2_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_1101) | ~m1_pre_topc(D_1100, A_1098) | ~m1_pre_topc('#skF_4', A_1098) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1098) | ~v2_pre_topc(A_1098) | v2_struct_0(A_1098))), inference(superposition, [status(thm), theory('equality')], [c_135, c_40312])).
% 26.54/16.56  tff(c_40337, plain, (![A_1098, D_1100, E_1101]: (k3_tmap_1(A_1098, '#skF_2', '#skF_4', D_1100, E_1101)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_1101, u1_struct_0(D_1100)) | ~m1_pre_topc(D_1100, '#skF_4') | ~m1_subset_1(E_1101, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_1101, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_1101) | ~m1_pre_topc(D_1100, A_1098) | ~m1_pre_topc('#skF_4', A_1098) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_1098) | ~v2_pre_topc(A_1098) | v2_struct_0(A_1098))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_135, c_135, c_40324])).
% 26.54/16.56  tff(c_59710, plain, (![A_1393, D_1394, E_1395]: (k3_tmap_1(A_1393, '#skF_2', '#skF_4', D_1394, E_1395)=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), E_1395, u1_struct_0(D_1394)) | ~m1_pre_topc(D_1394, '#skF_4') | ~m1_subset_1(E_1395, k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2')))) | ~v1_funct_2(E_1395, k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1(E_1395) | ~m1_pre_topc(D_1394, A_1393) | ~m1_pre_topc('#skF_4', A_1393) | ~l1_pre_topc(A_1393) | ~v2_pre_topc(A_1393) | v2_struct_0(A_1393))), inference(negUnitSimplification, [status(thm)], [c_92, c_40337])).
% 26.54/16.56  tff(c_59712, plain, (![A_1393, D_1394]: (k3_tmap_1(A_1393, '#skF_2', '#skF_4', D_1394, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_1394)) | ~m1_pre_topc(D_1394, '#skF_4') | ~v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_1394, A_1393) | ~m1_pre_topc('#skF_4', A_1393) | ~l1_pre_topc(A_1393) | ~v2_pre_topc(A_1393) | v2_struct_0(A_1393))), inference(resolution, [status(thm)], [c_175, c_59710])).
% 26.54/16.56  tff(c_59720, plain, (![A_1396, D_1397]: (k3_tmap_1(A_1396, '#skF_2', '#skF_4', D_1397, '#skF_5')=k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_1397)) | ~m1_pre_topc(D_1397, '#skF_4') | ~m1_pre_topc(D_1397, A_1396) | ~m1_pre_topc('#skF_4', A_1396) | ~l1_pre_topc(A_1396) | ~v2_pre_topc(A_1396) | v2_struct_0(A_1396))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_182, c_59712])).
% 26.54/16.56  tff(c_59818, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_84, c_59720])).
% 26.54/16.56  tff(c_59940, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_80, c_792, c_4331, c_420, c_59818])).
% 26.54/16.56  tff(c_59941, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_98, c_59940])).
% 26.54/16.56  tff(c_66, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_64, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_100, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64])).
% 26.54/16.56  tff(c_59946, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_59941, c_100])).
% 26.54/16.56  tff(c_86, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_315])).
% 26.54/16.56  tff(c_635, plain, (![A_321, B_322]: (m1_pre_topc(A_321, B_322) | ~m1_pre_topc(A_321, g1_pre_topc(u1_struct_0(B_322), u1_pre_topc(B_322))) | ~l1_pre_topc(B_322) | ~l1_pre_topc(A_321))), inference(cnfTransformation, [status(thm)], [f_118])).
% 26.54/16.56  tff(c_645, plain, (![A_321]: (m1_pre_topc(A_321, '#skF_3') | ~m1_pre_topc(A_321, g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_321))), inference(superposition, [status(thm), theory('equality')], [c_420, c_635])).
% 26.54/16.56  tff(c_668, plain, (![A_321]: (m1_pre_topc(A_321, '#skF_3') | ~m1_pre_topc(A_321, '#skF_4') | ~l1_pre_topc(A_321))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_298, c_525, c_645])).
% 26.54/16.56  tff(c_1506, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_420, c_1499])).
% 26.54/16.56  tff(c_1518, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_161, c_429, c_1506])).
% 26.54/16.56  tff(c_1525, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_1518])).
% 26.54/16.56  tff(c_1531, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_668, c_1525])).
% 26.54/16.56  tff(c_1544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_792, c_1531])).
% 26.54/16.56  tff(c_1546, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_1518])).
% 26.54/16.56  tff(c_1545, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_1518])).
% 26.54/16.56  tff(c_52, plain, (![B_89, A_87]: (m1_subset_1(u1_struct_0(B_89), k1_zfmisc_1(u1_struct_0(A_87))) | ~m1_pre_topc(B_89, A_87) | ~l1_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_208])).
% 26.54/16.56  tff(c_1099, plain, (![B_346, A_347]: (v3_pre_topc(u1_struct_0(B_346), A_347) | ~v1_tsep_1(B_346, A_347) | ~m1_subset_1(u1_struct_0(B_346), k1_zfmisc_1(u1_struct_0(A_347))) | ~m1_pre_topc(B_346, A_347) | ~l1_pre_topc(A_347) | ~v2_pre_topc(A_347))), inference(cnfTransformation, [status(thm)], [f_201])).
% 26.54/16.56  tff(c_2200, plain, (![B_390, A_391]: (v3_pre_topc(u1_struct_0(B_390), A_391) | ~v1_tsep_1(B_390, A_391) | ~v2_pre_topc(A_391) | ~m1_pre_topc(B_390, A_391) | ~l1_pre_topc(A_391))), inference(resolution, [status(thm)], [c_52, c_1099])).
% 26.54/16.56  tff(c_303, plain, (![B_296, A_297]: (m1_subset_1(u1_struct_0(B_296), k1_zfmisc_1(u1_struct_0(A_297))) | ~m1_pre_topc(B_296, A_297) | ~l1_pre_topc(A_297))), inference(cnfTransformation, [status(thm)], [f_208])).
% 26.54/16.56  tff(c_309, plain, (![B_296]: (m1_subset_1(u1_struct_0(B_296), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_296, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_303])).
% 26.54/16.56  tff(c_329, plain, (![B_296]: (m1_subset_1(u1_struct_0(B_296), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_296, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_309])).
% 26.54/16.56  tff(c_587, plain, (![B_296]: (m1_subset_1(u1_struct_0(B_296), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_296, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_329])).
% 26.54/16.56  tff(c_1094, plain, (![B_296]: (v3_pre_topc(u1_struct_0(B_296), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_296), '#skF_3') | ~m1_pre_topc(B_296, '#skF_3'))), inference(resolution, [status(thm)], [c_587, c_1083])).
% 26.54/16.56  tff(c_2212, plain, (![B_390]: (v3_pre_topc(u1_struct_0(B_390), '#skF_4') | ~v1_tsep_1(B_390, '#skF_3') | ~v2_pre_topc('#skF_3') | ~m1_pre_topc(B_390, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_2200, c_1094])).
% 26.54/16.56  tff(c_2231, plain, (![B_390]: (v3_pre_topc(u1_struct_0(B_390), '#skF_4') | ~v1_tsep_1(B_390, '#skF_3') | ~m1_pre_topc(B_390, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_204, c_2212])).
% 26.54/16.56  tff(c_2280, plain, (![B_396, A_397]: (v1_tsep_1(B_396, A_397) | ~v3_pre_topc(u1_struct_0(B_396), A_397) | ~v2_pre_topc(A_397) | ~m1_pre_topc(B_396, A_397) | ~l1_pre_topc(A_397))), inference(resolution, [status(thm)], [c_52, c_1304])).
% 26.54/16.56  tff(c_2283, plain, (![B_390]: (v1_tsep_1(B_390, '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc(B_390, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v1_tsep_1(B_390, '#skF_3') | ~m1_pre_topc(B_390, '#skF_3'))), inference(resolution, [status(thm)], [c_2231, c_2280])).
% 26.54/16.56  tff(c_2459, plain, (![B_408]: (v1_tsep_1(B_408, '#skF_4') | ~m1_pre_topc(B_408, '#skF_4') | ~v1_tsep_1(B_408, '#skF_3') | ~m1_pre_topc(B_408, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_201, c_2283])).
% 26.54/16.56  tff(c_2468, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1545, c_2459])).
% 26.54/16.56  tff(c_2475, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1546, c_792, c_2468])).
% 26.54/16.56  tff(c_4316, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_420, c_4307])).
% 26.54/16.56  tff(c_4329, plain, (k2_partfun1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'), '#skF_5', k2_struct_0('#skF_4'))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_792, c_4316])).
% 26.54/16.56  tff(c_4336, plain, (k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4331, c_4329])).
% 26.54/16.56  tff(c_56, plain, (![F_153, D_147, A_91, C_139, B_123]: (r1_tmap_1(B_123, A_91, C_139, F_153) | ~r1_tmap_1(D_147, A_91, k2_tmap_1(B_123, A_91, C_139, D_147), F_153) | ~m1_subset_1(F_153, u1_struct_0(D_147)) | ~m1_subset_1(F_153, u1_struct_0(B_123)) | ~m1_pre_topc(D_147, B_123) | ~v1_tsep_1(D_147, B_123) | v2_struct_0(D_147) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_123), u1_struct_0(A_91)))) | ~v1_funct_2(C_139, u1_struct_0(B_123), u1_struct_0(A_91)) | ~v1_funct_1(C_139) | ~l1_pre_topc(B_123) | ~v2_pre_topc(B_123) | v2_struct_0(B_123) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_254])).
% 26.54/16.56  tff(c_4343, plain, (![F_153]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_153) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_153) | ~m1_subset_1(F_153, u1_struct_0('#skF_3')) | ~m1_subset_1(F_153, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4336, c_56])).
% 26.54/16.56  tff(c_4347, plain, (![F_153]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_153) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_153) | ~m1_subset_1(F_153, k2_struct_0('#skF_4')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_201, c_158, c_78, c_182, c_135, c_165, c_175, c_135, c_165, c_2475, c_792, c_165, c_420, c_4343])).
% 26.54/16.56  tff(c_4348, plain, (![F_153]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', F_153) | ~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_4'), F_153) | ~m1_subset_1(F_153, k2_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_92, c_82, c_86, c_4347])).
% 26.54/16.56  tff(c_59956, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_59946, c_4348])).
% 26.54/16.56  tff(c_59962, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_170, c_59956])).
% 26.54/16.56  tff(c_59964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_59962])).
% 26.54/16.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.54/16.56  
% 26.54/16.56  Inference rules
% 26.54/16.56  ----------------------
% 26.54/16.56  #Ref     : 6
% 26.54/16.56  #Sup     : 13401
% 26.54/16.56  #Fact    : 0
% 26.54/16.56  #Define  : 0
% 26.54/16.56  #Split   : 54
% 26.54/16.56  #Chain   : 0
% 26.54/16.56  #Close   : 0
% 26.54/16.56  
% 26.54/16.56  Ordering : KBO
% 26.54/16.56  
% 26.54/16.56  Simplification rules
% 26.54/16.56  ----------------------
% 26.54/16.56  #Subsume      : 6611
% 26.54/16.56  #Demod        : 34294
% 26.54/16.56  #Tautology    : 1594
% 26.54/16.56  #SimpNegUnit  : 857
% 26.54/16.56  #BackRed      : 15
% 26.54/16.56  
% 26.54/16.56  #Partial instantiations: 0
% 26.54/16.56  #Strategies tried      : 1
% 26.54/16.56  
% 26.54/16.56  Timing (in seconds)
% 26.54/16.56  ----------------------
% 26.54/16.57  Preprocessing        : 0.44
% 26.54/16.57  Parsing              : 0.23
% 26.54/16.57  CNF conversion       : 0.05
% 26.54/16.57  Main loop            : 15.26
% 26.54/16.57  Inferencing          : 2.45
% 26.54/16.57  Reduction            : 5.55
% 26.54/16.57  Demodulation         : 4.44
% 26.54/16.57  BG Simplification    : 0.24
% 26.54/16.57  Subsumption          : 6.41
% 26.54/16.57  Abstraction          : 0.44
% 26.54/16.57  MUC search           : 0.00
% 26.54/16.57  Cooper               : 0.00
% 26.54/16.57  Total                : 15.76
% 26.54/16.57  Index Insertion      : 0.00
% 26.54/16.57  Index Deletion       : 0.00
% 26.54/16.57  Index Matching       : 0.00
% 26.54/16.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
