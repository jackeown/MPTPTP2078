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
% DateTime   : Thu Dec  3 10:27:34 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.30s
% Verified   : 
% Statistics : Number of formulae       :  140 (2833 expanded)
%              Number of leaves         :   44 ( 977 expanded)
%              Depth                    :   17
%              Number of atoms          :  307 (12934 expanded)
%              Number of equality atoms :   39 (1819 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_242,negated_conjecture,(
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

tff(f_131,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_31,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_69,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_102,axiom,(
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

tff(f_193,axiom,(
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

tff(f_84,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_120,axiom,(
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

tff(c_76,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_117,plain,(
    ! [B_295,A_296] :
      ( l1_pre_topc(B_295)
      | ~ m1_pre_topc(B_295,A_296)
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_117])).

tff(c_130,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_123])).

tff(c_36,plain,(
    ! [A_36] :
      ( m1_pre_topc(A_36,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_93,plain,(
    ! [A_293] :
      ( u1_struct_0(A_293) = k2_struct_0(A_293)
      | ~ l1_struct_0(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [A_6] :
      ( u1_struct_0(A_6) = k2_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_137,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_130,c_97])).

tff(c_316,plain,(
    ! [B_305,A_306] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(u1_struct_0(A_306)))
      | ~ m1_pre_topc(B_305,A_306)
      | ~ l1_pre_topc(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_328,plain,(
    ! [B_305] :
      ( m1_subset_1(u1_struct_0(B_305),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_305,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_316])).

tff(c_375,plain,(
    ! [B_309] :
      ( m1_subset_1(u1_struct_0(B_309),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_309,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_328])).

tff(c_381,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_375])).

tff(c_606,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_609,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_606])).

tff(c_613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_609])).

tff(c_615,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_78,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_181,plain,(
    ! [B_299,A_300] :
      ( v2_pre_topc(B_299)
      | ~ m1_pre_topc(B_299,A_300)
      | ~ l1_pre_topc(A_300)
      | ~ v2_pre_topc(A_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_187,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_181])).

tff(c_194,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_187])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_223,plain,(
    ! [A_302] :
      ( g1_pre_topc(u1_struct_0(A_302),u1_pre_topc(A_302)) = A_302
      | ~ v1_pre_topc(A_302)
      | ~ l1_pre_topc(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_238,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_223])).

tff(c_250,plain,
    ( g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4'
    | ~ v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_238])).

tff(c_256,plain,(
    ~ v1_pre_topc('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_66,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_126,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_117])).

tff(c_133,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_126])).

tff(c_141,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_133,c_97])).

tff(c_54,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_148,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_54])).

tff(c_259,plain,(
    ! [A_303] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_303),u1_pre_topc(A_303)))
      | ~ l1_pre_topc(A_303)
      | v2_struct_0(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_265,plain,
    ( v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_259])).

tff(c_276,plain,
    ( v1_pre_topc('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_148,c_265])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_256,c_276])).

tff(c_279,plain,(
    g1_pre_topc(k2_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_159,plain,(
    ! [A_298] :
      ( m1_subset_1(u1_pre_topc(A_298),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_298))))
      | ~ l1_pre_topc(A_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_162,plain,
    ( m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_159])).

tff(c_173,plain,(
    m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_162])).

tff(c_409,plain,(
    ! [D_311,B_312,C_313,A_314] :
      ( D_311 = B_312
      | g1_pre_topc(C_313,D_311) != g1_pre_topc(A_314,B_312)
      | ~ m1_subset_1(B_312,k1_zfmisc_1(k1_zfmisc_1(A_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_421,plain,(
    ! [D_311,C_313] :
      ( u1_pre_topc('#skF_3') = D_311
      | g1_pre_topc(C_313,D_311) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_3'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_409])).

tff(c_426,plain,(
    ! [D_315,C_316] :
      ( u1_pre_topc('#skF_3') = D_315
      | g1_pre_topc(C_316,D_315) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_421])).

tff(c_436,plain,(
    u1_pre_topc('#skF_3') = u1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_426])).

tff(c_441,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_148])).

tff(c_165,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_159])).

tff(c_175,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_165])).

tff(c_497,plain,(
    ! [C_319,A_320,D_321,B_322] :
      ( C_319 = A_320
      | g1_pre_topc(C_319,D_321) != g1_pre_topc(A_320,B_322)
      | ~ m1_subset_1(B_322,k1_zfmisc_1(k1_zfmisc_1(A_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_505,plain,(
    ! [C_319,D_321] :
      ( k2_struct_0('#skF_4') = C_319
      | g1_pre_topc(C_319,D_321) != '#skF_4'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_497])).

tff(c_514,plain,(
    ! [C_323,D_324] :
      ( k2_struct_0('#skF_4') = C_323
      | g1_pre_topc(C_323,D_324) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_505])).

tff(c_524,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_514])).

tff(c_532,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_141])).

tff(c_190,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_181])).

tff(c_197,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_190])).

tff(c_1065,plain,(
    ! [C_346,A_347] :
      ( m1_pre_topc(C_346,A_347)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_346),u1_pre_topc(C_346)),A_347)
      | ~ l1_pre_topc(C_346)
      | ~ v2_pre_topc(C_346)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_346),u1_pre_topc(C_346)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_346),u1_pre_topc(C_346)))
      | ~ l1_pre_topc(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1074,plain,(
    ! [A_347] :
      ( m1_pre_topc('#skF_3',A_347)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_4')),A_347)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc(A_347) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_1065])).

tff(c_1095,plain,(
    ! [A_347] :
      ( m1_pre_topc('#skF_3',A_347)
      | ~ m1_pre_topc('#skF_4',A_347)
      | ~ l1_pre_topc(A_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_279,c_436,c_532,c_130,c_279,c_436,c_532,c_197,c_133,c_279,c_532,c_1074])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_44,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_98,plain,(
    ! [A_294] :
      ( u1_struct_0(A_294) = k2_struct_0(A_294)
      | ~ l1_pre_topc(A_294) ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_105,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_98])).

tff(c_58,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_108,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58])).

tff(c_142,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_108])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_107,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_56])).

tff(c_180,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_107])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_143,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_52])).

tff(c_48,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_46,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_82,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46])).

tff(c_1142,plain,(
    ! [A_353,G_354,E_352,D_356,C_355,B_351] :
      ( r1_tmap_1(D_356,B_351,E_352,G_354)
      | ~ r1_tmap_1(C_355,B_351,k3_tmap_1(A_353,B_351,D_356,C_355,E_352),G_354)
      | ~ m1_subset_1(G_354,u1_struct_0(C_355))
      | ~ m1_subset_1(G_354,u1_struct_0(D_356))
      | ~ m1_pre_topc(C_355,D_356)
      | ~ v1_tsep_1(C_355,D_356)
      | ~ m1_subset_1(E_352,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_356),u1_struct_0(B_351))))
      | ~ v1_funct_2(E_352,u1_struct_0(D_356),u1_struct_0(B_351))
      | ~ v1_funct_1(E_352)
      | ~ m1_pre_topc(D_356,A_353)
      | v2_struct_0(D_356)
      | ~ m1_pre_topc(C_355,A_353)
      | v2_struct_0(C_355)
      | ~ l1_pre_topc(B_351)
      | ~ v2_pre_topc(B_351)
      | v2_struct_0(B_351)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_1144,plain,
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
    inference(resolution,[status(thm)],[c_82,c_1142])).

tff(c_1147,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_70,c_66,c_62,c_60,c_142,c_105,c_137,c_180,c_105,c_137,c_143,c_137,c_143,c_532,c_1144])).

tff(c_1148,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_74,c_68,c_64,c_44,c_1147])).

tff(c_1149,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1148])).

tff(c_22,plain,(
    ! [A_18] :
      ( v3_pre_topc(k2_struct_0(A_18),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_34,plain,(
    ! [B_35,A_33] :
      ( m1_subset_1(u1_struct_0(B_35),k1_zfmisc_1(u1_struct_0(A_33)))
      | ~ m1_pre_topc(B_35,A_33)
      | ~ l1_pre_topc(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_724,plain,(
    ! [B_332,A_333] :
      ( v1_tsep_1(B_332,A_333)
      | ~ v3_pre_topc(u1_struct_0(B_332),A_333)
      | ~ m1_subset_1(u1_struct_0(B_332),k1_zfmisc_1(u1_struct_0(A_333)))
      | ~ m1_pre_topc(B_332,A_333)
      | ~ l1_pre_topc(A_333)
      | ~ v2_pre_topc(A_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1150,plain,(
    ! [B_357,A_358] :
      ( v1_tsep_1(B_357,A_358)
      | ~ v3_pre_topc(u1_struct_0(B_357),A_358)
      | ~ v2_pre_topc(A_358)
      | ~ m1_pre_topc(B_357,A_358)
      | ~ l1_pre_topc(A_358) ) ),
    inference(resolution,[status(thm)],[c_34,c_724])).

tff(c_1268,plain,(
    ! [A_376] :
      ( v1_tsep_1('#skF_3',A_376)
      | ~ v3_pre_topc(k2_struct_0('#skF_4'),A_376)
      | ~ v2_pre_topc(A_376)
      | ~ m1_pre_topc('#skF_3',A_376)
      | ~ l1_pre_topc(A_376) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_1150])).

tff(c_1278,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1268])).

tff(c_1285,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_130,c_1278])).

tff(c_1286,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1149,c_1285])).

tff(c_1289,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1095,c_1286])).

tff(c_1296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_615,c_1289])).

tff(c_1297,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1148])).

tff(c_1301,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_1095,c_1297])).

tff(c_1308,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_615,c_1301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.76  
% 4.08/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.29/1.76  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.29/1.76  
% 4.29/1.76  %Foreground sorts:
% 4.29/1.76  
% 4.29/1.76  
% 4.29/1.76  %Background operators:
% 4.29/1.76  
% 4.29/1.76  
% 4.29/1.76  %Foreground operators:
% 4.29/1.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.29/1.76  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.29/1.76  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.29/1.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.29/1.76  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.29/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.29/1.76  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.29/1.76  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.29/1.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.29/1.76  tff('#skF_7', type, '#skF_7': $i).
% 4.29/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.29/1.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.29/1.76  tff('#skF_6', type, '#skF_6': $i).
% 4.29/1.76  tff('#skF_2', type, '#skF_2': $i).
% 4.29/1.76  tff('#skF_3', type, '#skF_3': $i).
% 4.29/1.76  tff('#skF_1', type, '#skF_1': $i).
% 4.29/1.76  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.29/1.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.29/1.76  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 4.29/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.29/1.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.29/1.76  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.29/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.29/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.29/1.76  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.29/1.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.29/1.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.29/1.76  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 4.29/1.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.29/1.76  
% 4.30/1.78  tff(f_242, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.30/1.78  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.30/1.78  tff(f_131, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.30/1.78  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.30/1.78  tff(f_44, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 4.30/1.78  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.30/1.78  tff(f_40, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.30/1.78  tff(f_31, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.30/1.78  tff(f_69, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 4.30/1.78  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.30/1.78  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 4.30/1.78  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 4.30/1.78  tff(f_193, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 4.30/1.78  tff(f_84, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.30/1.78  tff(f_120, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.30/1.78  tff(c_76, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_117, plain, (![B_295, A_296]: (l1_pre_topc(B_295) | ~m1_pre_topc(B_295, A_296) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.30/1.78  tff(c_123, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_117])).
% 4.30/1.78  tff(c_130, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_123])).
% 4.30/1.78  tff(c_36, plain, (![A_36]: (m1_pre_topc(A_36, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.30/1.78  tff(c_8, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.30/1.78  tff(c_93, plain, (![A_293]: (u1_struct_0(A_293)=k2_struct_0(A_293) | ~l1_struct_0(A_293))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.30/1.78  tff(c_97, plain, (![A_6]: (u1_struct_0(A_6)=k2_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(resolution, [status(thm)], [c_8, c_93])).
% 4.30/1.78  tff(c_137, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_130, c_97])).
% 4.30/1.78  tff(c_316, plain, (![B_305, A_306]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(u1_struct_0(A_306))) | ~m1_pre_topc(B_305, A_306) | ~l1_pre_topc(A_306))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.30/1.78  tff(c_328, plain, (![B_305]: (m1_subset_1(u1_struct_0(B_305), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_305, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_316])).
% 4.30/1.78  tff(c_375, plain, (![B_309]: (m1_subset_1(u1_struct_0(B_309), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_309, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_328])).
% 4.30/1.78  tff(c_381, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_375])).
% 4.30/1.78  tff(c_606, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_381])).
% 4.30/1.78  tff(c_609, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_36, c_606])).
% 4.30/1.78  tff(c_613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_609])).
% 4.30/1.78  tff(c_615, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_381])).
% 4.30/1.78  tff(c_78, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_181, plain, (![B_299, A_300]: (v2_pre_topc(B_299) | ~m1_pre_topc(B_299, A_300) | ~l1_pre_topc(A_300) | ~v2_pre_topc(A_300))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.30/1.78  tff(c_187, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_181])).
% 4.30/1.78  tff(c_194, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_187])).
% 4.30/1.78  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_223, plain, (![A_302]: (g1_pre_topc(u1_struct_0(A_302), u1_pre_topc(A_302))=A_302 | ~v1_pre_topc(A_302) | ~l1_pre_topc(A_302))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.30/1.78  tff(c_238, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_223])).
% 4.30/1.78  tff(c_250, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4' | ~v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_238])).
% 4.30/1.78  tff(c_256, plain, (~v1_pre_topc('#skF_4')), inference(splitLeft, [status(thm)], [c_250])).
% 4.30/1.78  tff(c_66, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_126, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_117])).
% 4.30/1.78  tff(c_133, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_126])).
% 4.30/1.78  tff(c_141, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_133, c_97])).
% 4.30/1.78  tff(c_54, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_148, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_54])).
% 4.30/1.78  tff(c_259, plain, (![A_303]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_303), u1_pre_topc(A_303))) | ~l1_pre_topc(A_303) | v2_struct_0(A_303))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.30/1.78  tff(c_265, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_259])).
% 4.30/1.78  tff(c_276, plain, (v1_pre_topc('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_133, c_148, c_265])).
% 4.30/1.78  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_256, c_276])).
% 4.30/1.78  tff(c_279, plain, (g1_pre_topc(k2_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_4'), inference(splitRight, [status(thm)], [c_250])).
% 4.30/1.78  tff(c_159, plain, (![A_298]: (m1_subset_1(u1_pre_topc(A_298), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_298)))) | ~l1_pre_topc(A_298))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.30/1.78  tff(c_162, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))) | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_159])).
% 4.30/1.78  tff(c_173, plain, (m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_162])).
% 4.30/1.78  tff(c_409, plain, (![D_311, B_312, C_313, A_314]: (D_311=B_312 | g1_pre_topc(C_313, D_311)!=g1_pre_topc(A_314, B_312) | ~m1_subset_1(B_312, k1_zfmisc_1(k1_zfmisc_1(A_314))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.30/1.78  tff(c_421, plain, (![D_311, C_313]: (u1_pre_topc('#skF_3')=D_311 | g1_pre_topc(C_313, D_311)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_3'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_3')))))), inference(superposition, [status(thm), theory('equality')], [c_148, c_409])).
% 4.30/1.78  tff(c_426, plain, (![D_315, C_316]: (u1_pre_topc('#skF_3')=D_315 | g1_pre_topc(C_316, D_315)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_173, c_421])).
% 4.30/1.78  tff(c_436, plain, (u1_pre_topc('#skF_3')=u1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_279, c_426])).
% 4.30/1.78  tff(c_441, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_436, c_148])).
% 4.30/1.78  tff(c_165, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))) | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_137, c_159])).
% 4.30/1.78  tff(c_175, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_165])).
% 4.30/1.78  tff(c_497, plain, (![C_319, A_320, D_321, B_322]: (C_319=A_320 | g1_pre_topc(C_319, D_321)!=g1_pre_topc(A_320, B_322) | ~m1_subset_1(B_322, k1_zfmisc_1(k1_zfmisc_1(A_320))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.30/1.78  tff(c_505, plain, (![C_319, D_321]: (k2_struct_0('#skF_4')=C_319 | g1_pre_topc(C_319, D_321)!='#skF_4' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(k2_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_279, c_497])).
% 4.30/1.78  tff(c_514, plain, (![C_323, D_324]: (k2_struct_0('#skF_4')=C_323 | g1_pre_topc(C_323, D_324)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_175, c_505])).
% 4.30/1.78  tff(c_524, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_441, c_514])).
% 4.30/1.78  tff(c_532, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_141])).
% 4.30/1.78  tff(c_190, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_181])).
% 4.30/1.78  tff(c_197, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_190])).
% 4.30/1.78  tff(c_1065, plain, (![C_346, A_347]: (m1_pre_topc(C_346, A_347) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_346), u1_pre_topc(C_346)), A_347) | ~l1_pre_topc(C_346) | ~v2_pre_topc(C_346) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_346), u1_pre_topc(C_346))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_346), u1_pre_topc(C_346))) | ~l1_pre_topc(A_347))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.30/1.78  tff(c_1074, plain, (![A_347]: (m1_pre_topc('#skF_3', A_347) | ~m1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_4')), A_347) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc(A_347))), inference(superposition, [status(thm), theory('equality')], [c_436, c_1065])).
% 4.30/1.78  tff(c_1095, plain, (![A_347]: (m1_pre_topc('#skF_3', A_347) | ~m1_pre_topc('#skF_4', A_347) | ~l1_pre_topc(A_347))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_279, c_436, c_532, c_130, c_279, c_436, c_532, c_197, c_133, c_279, c_532, c_1074])).
% 4.30/1.78  tff(c_80, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_44, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_98, plain, (![A_294]: (u1_struct_0(A_294)=k2_struct_0(A_294) | ~l1_pre_topc(A_294))), inference(resolution, [status(thm)], [c_8, c_93])).
% 4.30/1.78  tff(c_105, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_98])).
% 4.30/1.78  tff(c_58, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_108, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58])).
% 4.30/1.78  tff(c_142, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_108])).
% 4.30/1.78  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_107, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_56])).
% 4.30/1.78  tff(c_180, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_107])).
% 4.30/1.78  tff(c_52, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_143, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_52])).
% 4.30/1.78  tff(c_48, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_46, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_242])).
% 4.30/1.78  tff(c_82, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46])).
% 4.30/1.78  tff(c_1142, plain, (![A_353, G_354, E_352, D_356, C_355, B_351]: (r1_tmap_1(D_356, B_351, E_352, G_354) | ~r1_tmap_1(C_355, B_351, k3_tmap_1(A_353, B_351, D_356, C_355, E_352), G_354) | ~m1_subset_1(G_354, u1_struct_0(C_355)) | ~m1_subset_1(G_354, u1_struct_0(D_356)) | ~m1_pre_topc(C_355, D_356) | ~v1_tsep_1(C_355, D_356) | ~m1_subset_1(E_352, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_356), u1_struct_0(B_351)))) | ~v1_funct_2(E_352, u1_struct_0(D_356), u1_struct_0(B_351)) | ~v1_funct_1(E_352) | ~m1_pre_topc(D_356, A_353) | v2_struct_0(D_356) | ~m1_pre_topc(C_355, A_353) | v2_struct_0(C_355) | ~l1_pre_topc(B_351) | ~v2_pre_topc(B_351) | v2_struct_0(B_351) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353))), inference(cnfTransformation, [status(thm)], [f_193])).
% 4.30/1.78  tff(c_1144, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_82, c_1142])).
% 4.30/1.78  tff(c_1147, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_70, c_66, c_62, c_60, c_142, c_105, c_137, c_180, c_105, c_137, c_143, c_137, c_143, c_532, c_1144])).
% 4.30/1.78  tff(c_1148, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_80, c_74, c_68, c_64, c_44, c_1147])).
% 4.30/1.78  tff(c_1149, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1148])).
% 4.30/1.78  tff(c_22, plain, (![A_18]: (v3_pre_topc(k2_struct_0(A_18), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.30/1.78  tff(c_34, plain, (![B_35, A_33]: (m1_subset_1(u1_struct_0(B_35), k1_zfmisc_1(u1_struct_0(A_33))) | ~m1_pre_topc(B_35, A_33) | ~l1_pre_topc(A_33))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.30/1.78  tff(c_724, plain, (![B_332, A_333]: (v1_tsep_1(B_332, A_333) | ~v3_pre_topc(u1_struct_0(B_332), A_333) | ~m1_subset_1(u1_struct_0(B_332), k1_zfmisc_1(u1_struct_0(A_333))) | ~m1_pre_topc(B_332, A_333) | ~l1_pre_topc(A_333) | ~v2_pre_topc(A_333))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.30/1.78  tff(c_1150, plain, (![B_357, A_358]: (v1_tsep_1(B_357, A_358) | ~v3_pre_topc(u1_struct_0(B_357), A_358) | ~v2_pre_topc(A_358) | ~m1_pre_topc(B_357, A_358) | ~l1_pre_topc(A_358))), inference(resolution, [status(thm)], [c_34, c_724])).
% 4.30/1.78  tff(c_1268, plain, (![A_376]: (v1_tsep_1('#skF_3', A_376) | ~v3_pre_topc(k2_struct_0('#skF_4'), A_376) | ~v2_pre_topc(A_376) | ~m1_pre_topc('#skF_3', A_376) | ~l1_pre_topc(A_376))), inference(superposition, [status(thm), theory('equality')], [c_532, c_1150])).
% 4.30/1.78  tff(c_1278, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1268])).
% 4.30/1.78  tff(c_1285, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_130, c_1278])).
% 4.30/1.78  tff(c_1286, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1149, c_1285])).
% 4.30/1.78  tff(c_1289, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1095, c_1286])).
% 4.30/1.78  tff(c_1296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_615, c_1289])).
% 4.30/1.78  tff(c_1297, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1148])).
% 4.30/1.78  tff(c_1301, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_1095, c_1297])).
% 4.30/1.78  tff(c_1308, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_130, c_615, c_1301])).
% 4.30/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.30/1.78  
% 4.30/1.78  Inference rules
% 4.30/1.78  ----------------------
% 4.30/1.78  #Ref     : 2
% 4.30/1.78  #Sup     : 261
% 4.30/1.78  #Fact    : 0
% 4.30/1.78  #Define  : 0
% 4.30/1.78  #Split   : 18
% 4.30/1.78  #Chain   : 0
% 4.30/1.78  #Close   : 0
% 4.30/1.78  
% 4.30/1.78  Ordering : KBO
% 4.30/1.78  
% 4.30/1.78  Simplification rules
% 4.30/1.78  ----------------------
% 4.30/1.78  #Subsume      : 36
% 4.30/1.78  #Demod        : 369
% 4.30/1.78  #Tautology    : 96
% 4.30/1.78  #SimpNegUnit  : 27
% 4.30/1.78  #BackRed      : 17
% 4.30/1.78  
% 4.30/1.78  #Partial instantiations: 0
% 4.30/1.78  #Strategies tried      : 1
% 4.30/1.78  
% 4.30/1.78  Timing (in seconds)
% 4.30/1.78  ----------------------
% 4.30/1.78  Preprocessing        : 0.38
% 4.30/1.78  Parsing              : 0.18
% 4.30/1.78  CNF conversion       : 0.05
% 4.30/1.79  Main loop            : 0.54
% 4.30/1.79  Inferencing          : 0.16
% 4.30/1.79  Reduction            : 0.20
% 4.30/1.79  Demodulation         : 0.14
% 4.30/1.79  BG Simplification    : 0.03
% 4.30/1.79  Subsumption          : 0.11
% 4.30/1.79  Abstraction          : 0.02
% 4.30/1.79  MUC search           : 0.00
% 4.30/1.79  Cooper               : 0.00
% 4.30/1.79  Total                : 0.96
% 4.30/1.79  Index Insertion      : 0.00
% 4.30/1.79  Index Deletion       : 0.00
% 4.30/1.79  Index Matching       : 0.00
% 4.30/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
