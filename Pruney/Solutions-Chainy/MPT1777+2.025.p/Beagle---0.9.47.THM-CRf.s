%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:35 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  118 (2078 expanded)
%              Number of leaves         :   41 ( 731 expanded)
%              Depth                    :   20
%              Number of atoms          :  284 (11273 expanded)
%              Number of equality atoms :   29 (1559 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_229,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_97,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_113,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_180,axiom,(
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
                     => ( m1_pre_topc(C,D)
                       => ! [F] :
                            ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(D))
                               => ! [H] :
                                    ( m1_subset_1(H,u1_struct_0(C))
                                   => ( ( r1_tarski(F,u1_struct_0(C))
                                        & m1_connsp_2(F,D,G)
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_119,plain,(
    ! [B_420,A_421] :
      ( v2_pre_topc(B_420)
      | ~ m1_pre_topc(B_420,A_421)
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_119])).

tff(c_135,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_128])).

tff(c_91,plain,(
    ! [B_414,A_415] :
      ( l1_pre_topc(B_414)
      | ~ m1_pre_topc(B_414,A_415)
      | ~ l1_pre_topc(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_91])).

tff(c_107,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_100])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_104,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_136,plain,(
    ! [A_422] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_422),u1_pre_topc(A_422)))
      | ~ l1_pre_topc(A_422)
      | v2_struct_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_139,plain,
    ( v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_136])).

tff(c_141,plain,
    ( v1_pre_topc('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_139])).

tff(c_142,plain,(
    v1_pre_topc('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_141])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10] :
      ( m1_subset_1(u1_pre_topc(A_10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_179,plain,(
    ! [D_425,B_426,C_427,A_428] :
      ( D_425 = B_426
      | g1_pre_topc(C_427,D_425) != g1_pre_topc(A_428,B_426)
      | ~ m1_subset_1(B_426,k1_zfmisc_1(k1_zfmisc_1(A_428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_189,plain,(
    ! [B_429,A_430] :
      ( u1_pre_topc('#skF_4') = B_429
      | g1_pre_topc(A_430,B_429) != '#skF_5'
      | ~ m1_subset_1(B_429,k1_zfmisc_1(k1_zfmisc_1(A_430))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_179])).

tff(c_204,plain,(
    ! [A_433] :
      ( u1_pre_topc(A_433) = u1_pre_topc('#skF_4')
      | g1_pre_topc(u1_struct_0(A_433),u1_pre_topc(A_433)) != '#skF_5'
      | ~ l1_pre_topc(A_433) ) ),
    inference(resolution,[status(thm)],[c_12,c_189])).

tff(c_216,plain,(
    ! [A_434] :
      ( u1_pre_topc(A_434) = u1_pre_topc('#skF_4')
      | A_434 != '#skF_5'
      | ~ l1_pre_topc(A_434)
      | ~ v1_pre_topc(A_434)
      | ~ l1_pre_topc(A_434) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_204])).

tff(c_219,plain,
    ( u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_142,c_216])).

tff(c_225,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_219])).

tff(c_233,plain,
    ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) = '#skF_5'
    | ~ v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_6])).

tff(c_251,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_142,c_233])).

tff(c_245,plain,
    ( m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_12])).

tff(c_261,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_245])).

tff(c_267,plain,(
    ! [C_435,A_436,D_437,B_438] :
      ( C_435 = A_436
      | g1_pre_topc(C_435,D_437) != g1_pre_topc(A_436,B_438)
      | ~ m1_subset_1(B_438,k1_zfmisc_1(k1_zfmisc_1(A_436))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_309,plain,(
    ! [A_439,B_440] :
      ( u1_struct_0('#skF_4') = A_439
      | g1_pre_topc(A_439,B_440) != '#skF_5'
      | ~ m1_subset_1(B_440,k1_zfmisc_1(k1_zfmisc_1(A_439))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_267])).

tff(c_312,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_261,c_309])).

tff(c_322,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_312])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( m1_connsp_2('#skF_1'(A_25,B_26),A_25,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_934,plain,(
    ! [C_479,A_480,B_481] :
      ( m1_subset_1(C_479,k1_zfmisc_1(u1_struct_0(A_480)))
      | ~ m1_connsp_2(C_479,A_480,B_481)
      | ~ m1_subset_1(B_481,u1_struct_0(A_480))
      | ~ l1_pre_topc(A_480)
      | ~ v2_pre_topc(A_480)
      | v2_struct_0(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_938,plain,(
    ! [A_482,B_483] :
      ( m1_subset_1('#skF_1'(A_482,B_483),k1_zfmisc_1(u1_struct_0(A_482)))
      | ~ m1_subset_1(B_483,u1_struct_0(A_482))
      | ~ l1_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(resolution,[status(thm)],[c_28,c_934])).

tff(c_944,plain,(
    ! [B_483] :
      ( m1_subset_1('#skF_1'('#skF_5',B_483),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_483,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_938])).

tff(c_947,plain,(
    ! [B_483] :
      ( m1_subset_1('#skF_1'('#skF_5',B_483),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_483,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_107,c_322,c_944])).

tff(c_949,plain,(
    ! [B_484] :
      ( m1_subset_1('#skF_1'('#skF_5',B_484),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_484,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_947])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_953,plain,(
    ! [B_484] :
      ( r1_tarski('#skF_1'('#skF_5',B_484),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_484,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_949,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_28] :
      ( m1_pre_topc(A_28,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_594,plain,(
    ! [A_457,B_458] :
      ( m1_pre_topc(A_457,g1_pre_topc(u1_struct_0(B_458),u1_pre_topc(B_458)))
      | ~ m1_pre_topc(A_457,B_458)
      | ~ l1_pre_topc(B_458)
      | ~ l1_pre_topc(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_621,plain,(
    ! [A_457] :
      ( m1_pre_topc(A_457,'#skF_5')
      | ~ m1_pre_topc(A_457,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_457) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_594])).

tff(c_634,plain,(
    ! [A_457] :
      ( m1_pre_topc(A_457,'#skF_5')
      | ~ m1_pre_topc(A_457,'#skF_4')
      | ~ l1_pre_topc(A_457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_621])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_42,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_38,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_76,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_330,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_329,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_50])).

tff(c_40,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1100,plain,(
    ! [H_501,B_504,D_502,C_505,F_500,A_503,E_506] :
      ( r1_tmap_1(D_502,B_504,E_506,H_501)
      | ~ r1_tmap_1(C_505,B_504,k3_tmap_1(A_503,B_504,D_502,C_505,E_506),H_501)
      | ~ m1_connsp_2(F_500,D_502,H_501)
      | ~ r1_tarski(F_500,u1_struct_0(C_505))
      | ~ m1_subset_1(H_501,u1_struct_0(C_505))
      | ~ m1_subset_1(H_501,u1_struct_0(D_502))
      | ~ m1_subset_1(F_500,k1_zfmisc_1(u1_struct_0(D_502)))
      | ~ m1_pre_topc(C_505,D_502)
      | ~ m1_subset_1(E_506,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_502),u1_struct_0(B_504))))
      | ~ v1_funct_2(E_506,u1_struct_0(D_502),u1_struct_0(B_504))
      | ~ v1_funct_1(E_506)
      | ~ m1_pre_topc(D_502,A_503)
      | v2_struct_0(D_502)
      | ~ m1_pre_topc(C_505,A_503)
      | v2_struct_0(C_505)
      | ~ l1_pre_topc(B_504)
      | ~ v2_pre_topc(B_504)
      | v2_struct_0(B_504)
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_1102,plain,(
    ! [F_500] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_500,'#skF_5','#skF_8')
      | ~ r1_tarski(F_500,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_500,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_1100])).

tff(c_1105,plain,(
    ! [F_500] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_500,'#skF_5','#skF_8')
      | ~ r1_tarski(F_500,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_500,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_330,c_322,c_329,c_322,c_322,c_44,c_322,c_44,c_1102])).

tff(c_1106,plain,(
    ! [F_500] :
      ( ~ m1_connsp_2(F_500,'#skF_5','#skF_8')
      | ~ r1_tarski(F_500,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_500,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_76,c_1105])).

tff(c_1107,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1106])).

tff(c_1110,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_634,c_1107])).

tff(c_1113,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1110])).

tff(c_1116,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1113])).

tff(c_1120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1116])).

tff(c_1245,plain,(
    ! [F_508] :
      ( ~ m1_connsp_2(F_508,'#skF_5','#skF_8')
      | ~ r1_tarski(F_508,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_508,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1106])).

tff(c_1263,plain,(
    ! [A_509] :
      ( ~ m1_connsp_2(A_509,'#skF_5','#skF_8')
      | ~ r1_tarski(A_509,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_1245])).

tff(c_1281,plain,(
    ! [B_518] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_518),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_518,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_953,c_1263])).

tff(c_1285,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1281])).

tff(c_1288,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_107,c_44,c_322,c_44,c_1285])).

tff(c_1290,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:00:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.58  
% 3.70/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.59  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.70/1.59  
% 3.70/1.59  %Foreground sorts:
% 3.70/1.59  
% 3.70/1.59  
% 3.70/1.59  %Background operators:
% 3.70/1.59  
% 3.70/1.59  
% 3.70/1.59  %Foreground operators:
% 3.70/1.59  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.70/1.59  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.70/1.59  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.70/1.59  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.70/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.59  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.70/1.59  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.70/1.59  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.70/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.70/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.70/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.70/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.59  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.70/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.59  tff('#skF_8', type, '#skF_8': $i).
% 3.70/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.59  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.70/1.59  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.70/1.59  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.70/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.70/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.59  
% 3.70/1.61  tff(f_229, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.70/1.61  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.70/1.61  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.70/1.61  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 3.70/1.61  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.70/1.61  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.70/1.61  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.70/1.61  tff(f_109, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.70/1.61  tff(f_97, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.70/1.61  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.70/1.61  tff(f_113, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.70/1.61  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.70/1.61  tff(f_180, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.70/1.61  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_119, plain, (![B_420, A_421]: (v2_pre_topc(B_420) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.70/1.61  tff(c_128, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_119])).
% 3.70/1.61  tff(c_135, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_128])).
% 3.70/1.61  tff(c_91, plain, (![B_414, A_415]: (l1_pre_topc(B_414) | ~m1_pre_topc(B_414, A_415) | ~l1_pre_topc(A_415))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.70/1.61  tff(c_100, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_91])).
% 3.70/1.61  tff(c_107, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_100])).
% 3.70/1.61  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_97, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_91])).
% 3.70/1.61  tff(c_104, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97])).
% 3.70/1.61  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_136, plain, (![A_422]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_422), u1_pre_topc(A_422))) | ~l1_pre_topc(A_422) | v2_struct_0(A_422))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.70/1.61  tff(c_139, plain, (v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_136])).
% 3.70/1.61  tff(c_141, plain, (v1_pre_topc('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_139])).
% 3.70/1.61  tff(c_142, plain, (v1_pre_topc('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_141])).
% 3.70/1.61  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.70/1.61  tff(c_12, plain, (![A_10]: (m1_subset_1(u1_pre_topc(A_10), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.70/1.61  tff(c_179, plain, (![D_425, B_426, C_427, A_428]: (D_425=B_426 | g1_pre_topc(C_427, D_425)!=g1_pre_topc(A_428, B_426) | ~m1_subset_1(B_426, k1_zfmisc_1(k1_zfmisc_1(A_428))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.70/1.61  tff(c_189, plain, (![B_429, A_430]: (u1_pre_topc('#skF_4')=B_429 | g1_pre_topc(A_430, B_429)!='#skF_5' | ~m1_subset_1(B_429, k1_zfmisc_1(k1_zfmisc_1(A_430))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_179])).
% 3.70/1.61  tff(c_204, plain, (![A_433]: (u1_pre_topc(A_433)=u1_pre_topc('#skF_4') | g1_pre_topc(u1_struct_0(A_433), u1_pre_topc(A_433))!='#skF_5' | ~l1_pre_topc(A_433))), inference(resolution, [status(thm)], [c_12, c_189])).
% 3.70/1.61  tff(c_216, plain, (![A_434]: (u1_pre_topc(A_434)=u1_pre_topc('#skF_4') | A_434!='#skF_5' | ~l1_pre_topc(A_434) | ~v1_pre_topc(A_434) | ~l1_pre_topc(A_434))), inference(superposition, [status(thm), theory('equality')], [c_6, c_204])).
% 3.70/1.61  tff(c_219, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_142, c_216])).
% 3.70/1.61  tff(c_225, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_219])).
% 3.70/1.61  tff(c_233, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))='#skF_5' | ~v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_225, c_6])).
% 3.70/1.61  tff(c_251, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_142, c_233])).
% 3.70/1.61  tff(c_245, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_225, c_12])).
% 3.70/1.61  tff(c_261, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_107, c_245])).
% 3.70/1.61  tff(c_267, plain, (![C_435, A_436, D_437, B_438]: (C_435=A_436 | g1_pre_topc(C_435, D_437)!=g1_pre_topc(A_436, B_438) | ~m1_subset_1(B_438, k1_zfmisc_1(k1_zfmisc_1(A_436))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.70/1.61  tff(c_309, plain, (![A_439, B_440]: (u1_struct_0('#skF_4')=A_439 | g1_pre_topc(A_439, B_440)!='#skF_5' | ~m1_subset_1(B_440, k1_zfmisc_1(k1_zfmisc_1(A_439))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_267])).
% 3.70/1.61  tff(c_312, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))!='#skF_5'), inference(resolution, [status(thm)], [c_261, c_309])).
% 3.70/1.61  tff(c_322, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_251, c_312])).
% 3.70/1.61  tff(c_28, plain, (![A_25, B_26]: (m1_connsp_2('#skF_1'(A_25, B_26), A_25, B_26) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.70/1.61  tff(c_934, plain, (![C_479, A_480, B_481]: (m1_subset_1(C_479, k1_zfmisc_1(u1_struct_0(A_480))) | ~m1_connsp_2(C_479, A_480, B_481) | ~m1_subset_1(B_481, u1_struct_0(A_480)) | ~l1_pre_topc(A_480) | ~v2_pre_topc(A_480) | v2_struct_0(A_480))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.70/1.61  tff(c_938, plain, (![A_482, B_483]: (m1_subset_1('#skF_1'(A_482, B_483), k1_zfmisc_1(u1_struct_0(A_482))) | ~m1_subset_1(B_483, u1_struct_0(A_482)) | ~l1_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(resolution, [status(thm)], [c_28, c_934])).
% 3.70/1.61  tff(c_944, plain, (![B_483]: (m1_subset_1('#skF_1'('#skF_5', B_483), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_483, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_938])).
% 3.70/1.61  tff(c_947, plain, (![B_483]: (m1_subset_1('#skF_1'('#skF_5', B_483), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_483, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_107, c_322, c_944])).
% 3.70/1.61  tff(c_949, plain, (![B_484]: (m1_subset_1('#skF_1'('#skF_5', B_484), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_484, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_947])).
% 3.70/1.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.70/1.61  tff(c_953, plain, (![B_484]: (r1_tarski('#skF_1'('#skF_5', B_484), u1_struct_0('#skF_4')) | ~m1_subset_1(B_484, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_949, c_2])).
% 3.70/1.61  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.70/1.61  tff(c_30, plain, (![A_28]: (m1_pre_topc(A_28, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.70/1.61  tff(c_594, plain, (![A_457, B_458]: (m1_pre_topc(A_457, g1_pre_topc(u1_struct_0(B_458), u1_pre_topc(B_458))) | ~m1_pre_topc(A_457, B_458) | ~l1_pre_topc(B_458) | ~l1_pre_topc(A_457))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.70/1.61  tff(c_621, plain, (![A_457]: (m1_pre_topc(A_457, '#skF_5') | ~m1_pre_topc(A_457, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_457))), inference(superposition, [status(thm), theory('equality')], [c_48, c_594])).
% 3.70/1.61  tff(c_634, plain, (![A_457]: (m1_pre_topc(A_457, '#skF_5') | ~m1_pre_topc(A_457, '#skF_4') | ~l1_pre_topc(A_457))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_621])).
% 3.70/1.61  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_38, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 3.70/1.61  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_330, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_52])).
% 3.70/1.61  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_329, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_322, c_50])).
% 3.70/1.61  tff(c_40, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_229])).
% 3.70/1.61  tff(c_1100, plain, (![H_501, B_504, D_502, C_505, F_500, A_503, E_506]: (r1_tmap_1(D_502, B_504, E_506, H_501) | ~r1_tmap_1(C_505, B_504, k3_tmap_1(A_503, B_504, D_502, C_505, E_506), H_501) | ~m1_connsp_2(F_500, D_502, H_501) | ~r1_tarski(F_500, u1_struct_0(C_505)) | ~m1_subset_1(H_501, u1_struct_0(C_505)) | ~m1_subset_1(H_501, u1_struct_0(D_502)) | ~m1_subset_1(F_500, k1_zfmisc_1(u1_struct_0(D_502))) | ~m1_pre_topc(C_505, D_502) | ~m1_subset_1(E_506, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_502), u1_struct_0(B_504)))) | ~v1_funct_2(E_506, u1_struct_0(D_502), u1_struct_0(B_504)) | ~v1_funct_1(E_506) | ~m1_pre_topc(D_502, A_503) | v2_struct_0(D_502) | ~m1_pre_topc(C_505, A_503) | v2_struct_0(C_505) | ~l1_pre_topc(B_504) | ~v2_pre_topc(B_504) | v2_struct_0(B_504) | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503))), inference(cnfTransformation, [status(thm)], [f_180])).
% 3.70/1.61  tff(c_1102, plain, (![F_500]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_500, '#skF_5', '#skF_8') | ~r1_tarski(F_500, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_500, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1100])).
% 3.70/1.61  tff(c_1105, plain, (![F_500]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_500, '#skF_5', '#skF_8') | ~r1_tarski(F_500, u1_struct_0('#skF_4')) | ~m1_subset_1(F_500, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_330, c_322, c_329, c_322, c_322, c_44, c_322, c_44, c_1102])).
% 3.70/1.61  tff(c_1106, plain, (![F_500]: (~m1_connsp_2(F_500, '#skF_5', '#skF_8') | ~r1_tarski(F_500, u1_struct_0('#skF_4')) | ~m1_subset_1(F_500, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_76, c_1105])).
% 3.70/1.61  tff(c_1107, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1106])).
% 3.70/1.61  tff(c_1110, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_634, c_1107])).
% 3.70/1.61  tff(c_1113, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1110])).
% 3.70/1.61  tff(c_1116, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_1113])).
% 3.70/1.61  tff(c_1120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1116])).
% 3.70/1.61  tff(c_1245, plain, (![F_508]: (~m1_connsp_2(F_508, '#skF_5', '#skF_8') | ~r1_tarski(F_508, u1_struct_0('#skF_4')) | ~m1_subset_1(F_508, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1106])).
% 3.70/1.61  tff(c_1263, plain, (![A_509]: (~m1_connsp_2(A_509, '#skF_5', '#skF_8') | ~r1_tarski(A_509, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_1245])).
% 3.70/1.61  tff(c_1281, plain, (![B_518]: (~m1_connsp_2('#skF_1'('#skF_5', B_518), '#skF_5', '#skF_8') | ~m1_subset_1(B_518, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_953, c_1263])).
% 3.70/1.61  tff(c_1285, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_1281])).
% 3.70/1.61  tff(c_1288, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_107, c_44, c_322, c_44, c_1285])).
% 3.70/1.61  tff(c_1290, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1288])).
% 3.70/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.61  
% 3.70/1.61  Inference rules
% 3.70/1.61  ----------------------
% 3.70/1.61  #Ref     : 6
% 3.70/1.61  #Sup     : 232
% 3.70/1.61  #Fact    : 0
% 3.70/1.61  #Define  : 0
% 3.70/1.61  #Split   : 3
% 3.70/1.61  #Chain   : 0
% 3.70/1.61  #Close   : 0
% 3.70/1.61  
% 3.70/1.61  Ordering : KBO
% 3.70/1.61  
% 3.70/1.61  Simplification rules
% 3.70/1.61  ----------------------
% 3.70/1.61  #Subsume      : 51
% 3.70/1.61  #Demod        : 388
% 3.70/1.61  #Tautology    : 114
% 3.70/1.61  #SimpNegUnit  : 12
% 3.70/1.61  #BackRed      : 7
% 3.70/1.61  
% 3.70/1.61  #Partial instantiations: 0
% 3.70/1.61  #Strategies tried      : 1
% 3.70/1.61  
% 3.70/1.61  Timing (in seconds)
% 3.70/1.61  ----------------------
% 3.70/1.61  Preprocessing        : 0.38
% 3.70/1.61  Parsing              : 0.19
% 3.70/1.61  CNF conversion       : 0.06
% 3.70/1.61  Main loop            : 0.44
% 3.70/1.61  Inferencing          : 0.14
% 3.70/1.61  Reduction            : 0.15
% 3.70/1.61  Demodulation         : 0.11
% 3.70/1.61  BG Simplification    : 0.02
% 3.70/1.61  Subsumption          : 0.09
% 3.70/1.61  Abstraction          : 0.02
% 3.70/1.61  MUC search           : 0.00
% 3.70/1.61  Cooper               : 0.00
% 3.70/1.61  Total                : 0.87
% 3.70/1.61  Index Insertion      : 0.00
% 3.70/1.61  Index Deletion       : 0.00
% 3.70/1.61  Index Matching       : 0.00
% 3.70/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
