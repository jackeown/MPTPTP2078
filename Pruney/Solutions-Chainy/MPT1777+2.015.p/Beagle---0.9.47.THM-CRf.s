%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:34 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  136 (1548 expanded)
%              Number of leaves         :   45 ( 556 expanded)
%              Depth                    :   15
%              Number of atoms          :  313 (7372 expanded)
%              Number of equality atoms :   43 ( 939 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_254,negated_conjecture,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_107,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => m1_pre_topc(B,k1_tsep_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_205,axiom,(
    ! [A] :
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
                     => ( ( v1_tsep_1(C,D)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,B,E,F)
                                  <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_100,axiom,(
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

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_64,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_114,plain,(
    ! [B_296,A_297] :
      ( l1_pre_topc(B_296)
      | ~ m1_pre_topc(B_296,A_297)
      | ~ l1_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_120,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_114])).

tff(c_126,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_120])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_90,plain,(
    ! [A_294] :
      ( u1_struct_0(A_294) = k2_struct_0(A_294)
      | ~ l1_struct_0(A_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_94,plain,(
    ! [A_6] :
      ( u1_struct_0(A_6) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_135,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_94])).

tff(c_95,plain,(
    ! [A_295] :
      ( u1_struct_0(A_295) = k2_struct_0(A_295)
      | ~ l1_pre_topc(A_295) ) ),
    inference(resolution,[status(thm)],[c_8,c_90])).

tff(c_103,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_95])).

tff(c_56,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_109,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_56])).

tff(c_146,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_109])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_108,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_54])).

tff(c_152,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_108])).

tff(c_174,plain,(
    ! [B_300,A_301] :
      ( v2_pre_topc(B_300)
      | ~ m1_pre_topc(B_300,A_301)
      | ~ l1_pre_topc(A_301)
      | ~ v2_pre_topc(A_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_177,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_174])).

tff(c_183,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_177])).

tff(c_117,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_114])).

tff(c_123,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_117])).

tff(c_131,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_123,c_94])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_136,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_52])).

tff(c_187,plain,(
    ! [A_302] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_302),u1_pre_topc(A_302)))
      | ~ l1_pre_topc(A_302)
      | ~ v2_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_193,plain,
    ( v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_187])).

tff(c_203,plain,(
    v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_123,c_136,c_193])).

tff(c_208,plain,(
    ! [A_303] :
      ( g1_pre_topc(u1_struct_0(A_303),u1_pre_topc(A_303)) = A_303
      | ~ v1_pre_topc(A_303)
      | ~ l1_pre_topc(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_220,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_208])).

tff(c_233,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_220])).

tff(c_243,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_233])).

tff(c_153,plain,(
    ! [A_299] :
      ( m1_subset_1(u1_pre_topc(A_299),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_299))))
      | ~ l1_pre_topc(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_159,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_153])).

tff(c_169,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_159])).

tff(c_342,plain,(
    ! [C_309,A_310,D_311,B_312] :
      ( C_309 = A_310
      | g1_pre_topc(C_309,D_311) != g1_pre_topc(A_310,B_312)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(k1_zfmisc_1(A_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_354,plain,(
    ! [C_309,D_311] :
      ( k2_struct_0('#skF_3') = C_309
      | g1_pre_topc(C_309,D_311) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_342])).

tff(c_359,plain,(
    ! [C_313,D_314] :
      ( k2_struct_0('#skF_3') = C_313
      | g1_pre_topc(C_313,D_314) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_354])).

tff(c_369,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_359])).

tff(c_275,plain,(
    ! [B_305,A_306] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ m1_pre_topc(B_305,A_306)
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_281,plain,(
    ! [B_305] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_305,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_275])).

tff(c_308,plain,(
    ! [B_307] :
      ( m1_subset_1(u1_struct_0(B_307),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_307,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_281])).

tff(c_314,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_308])).

tff(c_569,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_314])).

tff(c_570,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_569])).

tff(c_376,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_136])).

tff(c_156,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_153])).

tff(c_167,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_156])).

tff(c_495,plain,(
    ! [D_323,B_324,C_325,A_326] :
      ( D_323 = B_324
      | g1_pre_topc(C_325,D_323) != g1_pre_topc(A_326,B_324)
      | ~ m1_subset_1(B_324,k1_zfmisc_1(k1_zfmisc_1(A_326))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_503,plain,(
    ! [D_323,C_325] :
      ( u1_pre_topc('#skF_4') = D_323
      | g1_pre_topc(C_325,D_323) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_495])).

tff(c_512,plain,(
    ! [D_327,C_328] :
      ( u1_pre_topc('#skF_4') = D_327
      | g1_pre_topc(C_328,D_327) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_503])).

tff(c_522,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_376,c_512])).

tff(c_377,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_131])).

tff(c_622,plain,(
    ! [A_332,B_333] :
      ( k1_tsep_1(A_332,B_333,B_333) = g1_pre_topc(u1_struct_0(B_333),u1_pre_topc(B_333))
      | ~ m1_pre_topc(B_333,A_332)
      | v2_struct_0(B_333)
      | ~ l1_pre_topc(A_332)
      | ~ v2_pre_topc(A_332)
      | v2_struct_0(A_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_626,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_622])).

tff(c_634,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_243,c_522,c_377,c_626])).

tff(c_635,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_634])).

tff(c_748,plain,(
    ! [B_339,A_340,C_341] :
      ( m1_pre_topc(B_339,k1_tsep_1(A_340,B_339,C_341))
      | ~ m1_pre_topc(C_341,A_340)
      | v2_struct_0(C_341)
      | ~ m1_pre_topc(B_339,A_340)
      | v2_struct_0(B_339)
      | ~ l1_pre_topc(A_340)
      | ~ v2_pre_topc(A_340)
      | v2_struct_0(A_340) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_769,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_748])).

tff(c_784,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_64,c_769])).

tff(c_786,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_570,c_784])).

tff(c_788,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_569])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_147,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_50])).

tff(c_46,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_44,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_80,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_1331,plain,(
    ! [G_385,B_381,C_383,A_384,E_380,D_382] :
      ( r1_tmap_1(D_382,B_381,E_380,G_385)
      | ~ r1_tmap_1(C_383,B_381,k3_tmap_1(A_384,B_381,D_382,C_383,E_380),G_385)
      | ~ m1_subset_1(G_385,u1_struct_0(C_383))
      | ~ m1_subset_1(G_385,u1_struct_0(D_382))
      | ~ m1_pre_topc(C_383,D_382)
      | ~ v1_tsep_1(C_383,D_382)
      | ~ m1_subset_1(E_380,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_382),u1_struct_0(B_381))))
      | ~ v1_funct_2(E_380,u1_struct_0(D_382),u1_struct_0(B_381))
      | ~ v1_funct_1(E_380)
      | ~ m1_pre_topc(D_382,A_384)
      | v2_struct_0(D_382)
      | ~ m1_pre_topc(C_383,A_384)
      | v2_struct_0(C_383)
      | ~ l1_pre_topc(B_381)
      | ~ v2_pre_topc(B_381)
      | v2_struct_0(B_381)
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384)
      | v2_struct_0(A_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_1333,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_80,c_1331])).

tff(c_1336,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_146,c_103,c_135,c_152,c_103,c_135,c_788,c_147,c_135,c_147,c_377,c_1333])).

tff(c_1337,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_42,c_1336])).

tff(c_180,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_174])).

tff(c_186,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_180])).

tff(c_22,plain,(
    ! [A_18] :
      ( v3_pre_topc(k2_struct_0(A_18),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    ! [B_28,A_26] :
      ( m1_subset_1(u1_struct_0(B_28),k1_zfmisc_1(u1_struct_0(A_26)))
      | ~ m1_pre_topc(B_28,A_26)
      | ~ l1_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_808,plain,(
    ! [B_342,A_343] :
      ( v1_tsep_1(B_342,A_343)
      | ~ v3_pre_topc(u1_struct_0(B_342),A_343)
      | ~ m1_subset_1(u1_struct_0(B_342),k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ m1_pre_topc(B_342,A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1230,plain,(
    ! [B_364,A_365] :
      ( v1_tsep_1(B_364,A_365)
      | ~ v3_pre_topc(u1_struct_0(B_364),A_365)
      | ~ v2_pre_topc(A_365)
      | ~ m1_pre_topc(B_364,A_365)
      | ~ l1_pre_topc(A_365) ) ),
    inference(resolution,[status(thm)],[c_30,c_808])).

tff(c_1338,plain,(
    ! [A_386] :
      ( v1_tsep_1('#skF_3',A_386)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_386)
      | ~ v2_pre_topc(A_386)
      | ~ m1_pre_topc('#skF_3',A_386)
      | ~ l1_pre_topc(A_386) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_1230])).

tff(c_1348,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1338])).

tff(c_1355,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_126,c_788,c_1348])).

tff(c_1357,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1337,c_1355])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:28:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.74  
% 4.06/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.74  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.06/1.74  
% 4.06/1.74  %Foreground sorts:
% 4.06/1.74  
% 4.06/1.74  
% 4.06/1.74  %Background operators:
% 4.06/1.74  
% 4.06/1.74  
% 4.06/1.74  %Foreground operators:
% 4.06/1.74  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.06/1.74  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.06/1.74  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.06/1.74  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.06/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.06/1.74  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.06/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.74  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.06/1.74  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.06/1.74  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.06/1.74  tff('#skF_7', type, '#skF_7': $i).
% 4.06/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.06/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.06/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.06/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.06/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.06/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.06/1.74  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.06/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.74  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.06/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.06/1.74  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.06/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.06/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.74  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.06/1.74  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.06/1.74  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.06/1.74  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.06/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.74  
% 4.06/1.76  tff(f_254, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.06/1.76  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.06/1.76  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.06/1.76  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.06/1.76  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.06/1.76  tff(f_67, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 4.06/1.76  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.06/1.76  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.06/1.76  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 4.06/1.76  tff(f_107, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.06/1.76  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 4.06/1.76  tff(f_128, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 4.06/1.76  tff(f_205, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.06/1.76  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.06/1.76  tff(f_100, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.06/1.76  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_42, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_64, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_114, plain, (![B_296, A_297]: (l1_pre_topc(B_296) | ~m1_pre_topc(B_296, A_297) | ~l1_pre_topc(A_297))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.06/1.76  tff(c_120, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_114])).
% 4.06/1.76  tff(c_126, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_120])).
% 4.06/1.76  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.06/1.76  tff(c_90, plain, (![A_294]: (u1_struct_0(A_294)=k2_struct_0(A_294) | ~l1_struct_0(A_294))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.06/1.76  tff(c_94, plain, (![A_6]: (u1_struct_0(A_6)=k2_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_8, c_90])).
% 4.06/1.76  tff(c_135, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_126, c_94])).
% 4.06/1.76  tff(c_95, plain, (![A_295]: (u1_struct_0(A_295)=k2_struct_0(A_295) | ~l1_pre_topc(A_295))), inference(resolution, [status(thm)], [c_8, c_90])).
% 4.06/1.76  tff(c_103, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_68, c_95])).
% 4.06/1.76  tff(c_56, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_109, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_56])).
% 4.06/1.76  tff(c_146, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_109])).
% 4.06/1.76  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_108, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_54])).
% 4.06/1.76  tff(c_152, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_108])).
% 4.06/1.76  tff(c_174, plain, (![B_300, A_301]: (v2_pre_topc(B_300) | ~m1_pre_topc(B_300, A_301) | ~l1_pre_topc(A_301) | ~v2_pre_topc(A_301))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.06/1.76  tff(c_177, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_174])).
% 4.06/1.76  tff(c_183, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_177])).
% 4.06/1.76  tff(c_117, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_64, c_114])).
% 4.06/1.76  tff(c_123, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_117])).
% 4.06/1.76  tff(c_131, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_123, c_94])).
% 4.06/1.76  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_136, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_52])).
% 4.06/1.76  tff(c_187, plain, (![A_302]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_302), u1_pre_topc(A_302))) | ~l1_pre_topc(A_302) | ~v2_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.06/1.76  tff(c_193, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_131, c_187])).
% 4.06/1.76  tff(c_203, plain, (v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_123, c_136, c_193])).
% 4.06/1.76  tff(c_208, plain, (![A_303]: (g1_pre_topc(u1_struct_0(A_303), u1_pre_topc(A_303))=A_303 | ~v1_pre_topc(A_303) | ~l1_pre_topc(A_303))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.06/1.76  tff(c_220, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_208])).
% 4.06/1.76  tff(c_233, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_220])).
% 4.06/1.76  tff(c_243, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_233])).
% 4.06/1.76  tff(c_153, plain, (![A_299]: (m1_subset_1(u1_pre_topc(A_299), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_299)))) | ~l1_pre_topc(A_299))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.06/1.76  tff(c_159, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_131, c_153])).
% 4.06/1.76  tff(c_169, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_159])).
% 4.06/1.76  tff(c_342, plain, (![C_309, A_310, D_311, B_312]: (C_309=A_310 | g1_pre_topc(C_309, D_311)!=g1_pre_topc(A_310, B_312) | ~m1_subset_1(B_312, k1_zfmisc_1(k1_zfmisc_1(A_310))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.06/1.76  tff(c_354, plain, (![C_309, D_311]: (k2_struct_0('#skF_3')=C_309 | g1_pre_topc(C_309, D_311)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_136, c_342])).
% 4.06/1.76  tff(c_359, plain, (![C_313, D_314]: (k2_struct_0('#skF_3')=C_313 | g1_pre_topc(C_313, D_314)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_354])).
% 4.06/1.76  tff(c_369, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_243, c_359])).
% 4.06/1.76  tff(c_275, plain, (![B_305, A_306]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(u1_struct_0(A_306))) | ~m1_pre_topc(B_305, A_306) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.06/1.76  tff(c_281, plain, (![B_305]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_305, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_275])).
% 4.06/1.76  tff(c_308, plain, (![B_307]: (m1_subset_1(u1_struct_0(B_307), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_307, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_281])).
% 4.06/1.76  tff(c_314, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_131, c_308])).
% 4.06/1.76  tff(c_569, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_314])).
% 4.06/1.76  tff(c_570, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_569])).
% 4.06/1.76  tff(c_376, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_369, c_136])).
% 4.06/1.76  tff(c_156, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_153])).
% 4.06/1.76  tff(c_167, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_156])).
% 4.06/1.76  tff(c_495, plain, (![D_323, B_324, C_325, A_326]: (D_323=B_324 | g1_pre_topc(C_325, D_323)!=g1_pre_topc(A_326, B_324) | ~m1_subset_1(B_324, k1_zfmisc_1(k1_zfmisc_1(A_326))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.06/1.76  tff(c_503, plain, (![D_323, C_325]: (u1_pre_topc('#skF_4')=D_323 | g1_pre_topc(C_325, D_323)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_243, c_495])).
% 4.06/1.76  tff(c_512, plain, (![D_327, C_328]: (u1_pre_topc('#skF_4')=D_327 | g1_pre_topc(C_328, D_327)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_503])).
% 4.06/1.76  tff(c_522, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_376, c_512])).
% 4.06/1.76  tff(c_377, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_369, c_131])).
% 4.06/1.76  tff(c_622, plain, (![A_332, B_333]: (k1_tsep_1(A_332, B_333, B_333)=g1_pre_topc(u1_struct_0(B_333), u1_pre_topc(B_333)) | ~m1_pre_topc(B_333, A_332) | v2_struct_0(B_333) | ~l1_pre_topc(A_332) | ~v2_pre_topc(A_332) | v2_struct_0(A_332))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.06/1.76  tff(c_626, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_622])).
% 4.06/1.76  tff(c_634, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4' | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_243, c_522, c_377, c_626])).
% 4.06/1.76  tff(c_635, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_634])).
% 4.06/1.76  tff(c_748, plain, (![B_339, A_340, C_341]: (m1_pre_topc(B_339, k1_tsep_1(A_340, B_339, C_341)) | ~m1_pre_topc(C_341, A_340) | v2_struct_0(C_341) | ~m1_pre_topc(B_339, A_340) | v2_struct_0(B_339) | ~l1_pre_topc(A_340) | ~v2_pre_topc(A_340) | v2_struct_0(A_340))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.06/1.76  tff(c_769, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_635, c_748])).
% 4.06/1.76  tff(c_784, plain, (m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_64, c_769])).
% 4.06/1.76  tff(c_786, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_570, c_784])).
% 4.06/1.76  tff(c_788, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_569])).
% 4.06/1.76  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_147, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_50])).
% 4.06/1.76  tff(c_46, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_44, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_254])).
% 4.06/1.76  tff(c_80, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 4.06/1.76  tff(c_1331, plain, (![G_385, B_381, C_383, A_384, E_380, D_382]: (r1_tmap_1(D_382, B_381, E_380, G_385) | ~r1_tmap_1(C_383, B_381, k3_tmap_1(A_384, B_381, D_382, C_383, E_380), G_385) | ~m1_subset_1(G_385, u1_struct_0(C_383)) | ~m1_subset_1(G_385, u1_struct_0(D_382)) | ~m1_pre_topc(C_383, D_382) | ~v1_tsep_1(C_383, D_382) | ~m1_subset_1(E_380, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_382), u1_struct_0(B_381)))) | ~v1_funct_2(E_380, u1_struct_0(D_382), u1_struct_0(B_381)) | ~v1_funct_1(E_380) | ~m1_pre_topc(D_382, A_384) | v2_struct_0(D_382) | ~m1_pre_topc(C_383, A_384) | v2_struct_0(C_383) | ~l1_pre_topc(B_381) | ~v2_pre_topc(B_381) | v2_struct_0(B_381) | ~l1_pre_topc(A_384) | ~v2_pre_topc(A_384) | v2_struct_0(A_384))), inference(cnfTransformation, [status(thm)], [f_205])).
% 4.06/1.76  tff(c_1333, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_80, c_1331])).
% 4.06/1.76  tff(c_1336, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_146, c_103, c_135, c_152, c_103, c_135, c_788, c_147, c_135, c_147, c_377, c_1333])).
% 4.06/1.76  tff(c_1337, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_42, c_1336])).
% 4.06/1.76  tff(c_180, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_174])).
% 4.06/1.76  tff(c_186, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_180])).
% 4.06/1.76  tff(c_22, plain, (![A_18]: (v3_pre_topc(k2_struct_0(A_18), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.06/1.76  tff(c_30, plain, (![B_28, A_26]: (m1_subset_1(u1_struct_0(B_28), k1_zfmisc_1(u1_struct_0(A_26))) | ~m1_pre_topc(B_28, A_26) | ~l1_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.06/1.76  tff(c_808, plain, (![B_342, A_343]: (v1_tsep_1(B_342, A_343) | ~v3_pre_topc(u1_struct_0(B_342), A_343) | ~m1_subset_1(u1_struct_0(B_342), k1_zfmisc_1(u1_struct_0(A_343))) | ~m1_pre_topc(B_342, A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.06/1.76  tff(c_1230, plain, (![B_364, A_365]: (v1_tsep_1(B_364, A_365) | ~v3_pre_topc(u1_struct_0(B_364), A_365) | ~v2_pre_topc(A_365) | ~m1_pre_topc(B_364, A_365) | ~l1_pre_topc(A_365))), inference(resolution, [status(thm)], [c_30, c_808])).
% 4.06/1.76  tff(c_1338, plain, (![A_386]: (v1_tsep_1('#skF_3', A_386) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_386) | ~v2_pre_topc(A_386) | ~m1_pre_topc('#skF_3', A_386) | ~l1_pre_topc(A_386))), inference(superposition, [status(thm), theory('equality')], [c_377, c_1230])).
% 4.06/1.76  tff(c_1348, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1338])).
% 4.06/1.76  tff(c_1355, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_186, c_126, c_788, c_1348])).
% 4.06/1.76  tff(c_1357, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1337, c_1355])).
% 4.06/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.06/1.76  
% 4.06/1.76  Inference rules
% 4.06/1.76  ----------------------
% 4.06/1.76  #Ref     : 2
% 4.06/1.76  #Sup     : 275
% 4.06/1.76  #Fact    : 0
% 4.06/1.76  #Define  : 0
% 4.06/1.76  #Split   : 23
% 4.06/1.76  #Chain   : 0
% 4.06/1.76  #Close   : 0
% 4.06/1.76  
% 4.06/1.76  Ordering : KBO
% 4.06/1.76  
% 4.06/1.76  Simplification rules
% 4.06/1.76  ----------------------
% 4.06/1.76  #Subsume      : 38
% 4.06/1.76  #Demod        : 339
% 4.06/1.76  #Tautology    : 95
% 4.06/1.76  #SimpNegUnit  : 32
% 4.06/1.76  #BackRed      : 15
% 4.06/1.76  
% 4.06/1.76  #Partial instantiations: 0
% 4.06/1.76  #Strategies tried      : 1
% 4.06/1.76  
% 4.06/1.76  Timing (in seconds)
% 4.06/1.76  ----------------------
% 4.06/1.77  Preprocessing        : 0.43
% 4.06/1.77  Parsing              : 0.22
% 4.06/1.77  CNF conversion       : 0.05
% 4.06/1.77  Main loop            : 0.54
% 4.06/1.77  Inferencing          : 0.17
% 4.06/1.77  Reduction            : 0.20
% 4.06/1.77  Demodulation         : 0.14
% 4.06/1.77  BG Simplification    : 0.03
% 4.06/1.77  Subsumption          : 0.11
% 4.06/1.77  Abstraction          : 0.02
% 4.06/1.77  MUC search           : 0.00
% 4.06/1.77  Cooper               : 0.00
% 4.06/1.77  Total                : 1.01
% 4.06/1.77  Index Insertion      : 0.00
% 4.06/1.77  Index Deletion       : 0.00
% 4.06/1.77  Index Matching       : 0.00
% 4.06/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
