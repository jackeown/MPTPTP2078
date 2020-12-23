%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:35 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  121 (1616 expanded)
%              Number of leaves         :   41 ( 587 expanded)
%              Depth                    :   18
%              Number of atoms          :  285 (9364 expanded)
%              Number of equality atoms :   29 (1318 expanded)
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

tff(f_227,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_107,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_111,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_178,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

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
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_125,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_119])).

tff(c_132,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_125])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_104,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_142,plain,(
    ! [A_423] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_423),u1_pre_topc(A_423)))
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_145,plain,
    ( v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_142])).

tff(c_147,plain,(
    v1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_104,c_145])).

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

tff(c_249,plain,(
    ! [D_439,B_440,C_441,A_442] :
      ( D_439 = B_440
      | g1_pre_topc(C_441,D_439) != g1_pre_topc(A_442,B_440)
      | ~ m1_subset_1(B_440,k1_zfmisc_1(k1_zfmisc_1(A_442))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_257,plain,(
    ! [D_439,C_441] :
      ( u1_pre_topc('#skF_4') = D_439
      | g1_pre_topc(C_441,D_439) != '#skF_5'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_249])).

tff(c_284,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_287,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_284])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_287])).

tff(c_297,plain,(
    ! [D_448,C_449] :
      ( u1_pre_topc('#skF_4') = D_448
      | g1_pre_topc(C_449,D_448) != '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_325,plain,(
    ! [A_450] :
      ( u1_pre_topc(A_450) = u1_pre_topc('#skF_4')
      | A_450 != '#skF_5'
      | ~ v1_pre_topc(A_450)
      | ~ l1_pre_topc(A_450) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_297])).

tff(c_328,plain,
    ( u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_147,c_325])).

tff(c_334,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_328])).

tff(c_366,plain,
    ( g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) = '#skF_5'
    | ~ v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_6])).

tff(c_386,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_147,c_366])).

tff(c_296,plain,(
    m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_210,plain,(
    ! [C_430,A_431,D_432,B_433] :
      ( C_430 = A_431
      | g1_pre_topc(C_430,D_432) != g1_pre_topc(A_431,B_433)
      | ~ m1_subset_1(B_433,k1_zfmisc_1(k1_zfmisc_1(A_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_218,plain,(
    ! [C_430,D_432] :
      ( u1_struct_0('#skF_4') = C_430
      | g1_pre_topc(C_430,D_432) != '#skF_5'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_210])).

tff(c_416,plain,(
    ! [C_453,D_454] :
      ( u1_struct_0('#skF_4') = C_453
      | g1_pre_topc(C_453,D_454) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_218])).

tff(c_426,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_416])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( m1_connsp_2('#skF_1'(A_25,B_26),A_25,B_26)
      | ~ m1_subset_1(B_26,u1_struct_0(A_25))
      | ~ l1_pre_topc(A_25)
      | ~ v2_pre_topc(A_25)
      | v2_struct_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_687,plain,(
    ! [C_466,A_467,B_468] :
      ( m1_subset_1(C_466,k1_zfmisc_1(u1_struct_0(A_467)))
      | ~ m1_connsp_2(C_466,A_467,B_468)
      | ~ m1_subset_1(B_468,u1_struct_0(A_467))
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467)
      | v2_struct_0(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_983,plain,(
    ! [A_490,B_491] :
      ( m1_subset_1('#skF_1'(A_490,B_491),k1_zfmisc_1(u1_struct_0(A_490)))
      | ~ m1_subset_1(B_491,u1_struct_0(A_490))
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(resolution,[status(thm)],[c_28,c_687])).

tff(c_989,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_1'('#skF_5',B_491),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_491,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_983])).

tff(c_992,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_1'('#skF_5',B_491),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_491,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_107,c_426,c_989])).

tff(c_1001,plain,(
    ! [B_499] :
      ( m1_subset_1('#skF_1'('#skF_5',B_499),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_499,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_992])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1005,plain,(
    ! [B_499] :
      ( r1_tarski('#skF_1'('#skF_5',B_499),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_499,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1001,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_28] :
      ( m1_pre_topc(A_28,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_473,plain,(
    ! [A_455,B_456] :
      ( m1_pre_topc(A_455,g1_pre_topc(u1_struct_0(B_456),u1_pre_topc(B_456)))
      | ~ m1_pre_topc(A_455,B_456)
      | ~ l1_pre_topc(B_456)
      | ~ l1_pre_topc(A_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_500,plain,(
    ! [A_455] :
      ( m1_pre_topc(A_455,'#skF_5')
      | ~ m1_pre_topc(A_455,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_455) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_473])).

tff(c_513,plain,(
    ! [A_455] :
      ( m1_pre_topc(A_455,'#skF_5')
      | ~ m1_pre_topc(A_455,'#skF_4')
      | ~ l1_pre_topc(A_455) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_500])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_42,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_38,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_76,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_432,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_431,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_50])).

tff(c_40,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_227])).

tff(c_994,plain,(
    ! [F_492,C_497,H_493,E_498,B_496,D_494,A_495] :
      ( r1_tmap_1(D_494,B_496,E_498,H_493)
      | ~ r1_tmap_1(C_497,B_496,k3_tmap_1(A_495,B_496,D_494,C_497,E_498),H_493)
      | ~ m1_connsp_2(F_492,D_494,H_493)
      | ~ r1_tarski(F_492,u1_struct_0(C_497))
      | ~ m1_subset_1(H_493,u1_struct_0(C_497))
      | ~ m1_subset_1(H_493,u1_struct_0(D_494))
      | ~ m1_subset_1(F_492,k1_zfmisc_1(u1_struct_0(D_494)))
      | ~ m1_pre_topc(C_497,D_494)
      | ~ m1_subset_1(E_498,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_494),u1_struct_0(B_496))))
      | ~ v1_funct_2(E_498,u1_struct_0(D_494),u1_struct_0(B_496))
      | ~ v1_funct_1(E_498)
      | ~ m1_pre_topc(D_494,A_495)
      | v2_struct_0(D_494)
      | ~ m1_pre_topc(C_497,A_495)
      | v2_struct_0(C_497)
      | ~ l1_pre_topc(B_496)
      | ~ v2_pre_topc(B_496)
      | v2_struct_0(B_496)
      | ~ l1_pre_topc(A_495)
      | ~ v2_pre_topc(A_495)
      | v2_struct_0(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_996,plain,(
    ! [F_492] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_492,'#skF_5','#skF_8')
      | ~ r1_tarski(F_492,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_492,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_40,c_994])).

tff(c_999,plain,(
    ! [F_492] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_492,'#skF_5','#skF_8')
      | ~ r1_tarski(F_492,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_492,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_432,c_426,c_431,c_426,c_426,c_44,c_426,c_44,c_996])).

tff(c_1000,plain,(
    ! [F_492] :
      ( ~ m1_connsp_2(F_492,'#skF_5','#skF_8')
      | ~ r1_tarski(F_492,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_492,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_76,c_999])).

tff(c_1014,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1000])).

tff(c_1017,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_513,c_1014])).

tff(c_1020,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1017])).

tff(c_1023,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1020])).

tff(c_1027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1023])).

tff(c_1153,plain,(
    ! [F_507] :
      ( ~ m1_connsp_2(F_507,'#skF_5','#skF_8')
      | ~ r1_tarski(F_507,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_507,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1000])).

tff(c_1171,plain,(
    ! [A_508] :
      ( ~ m1_connsp_2(A_508,'#skF_5','#skF_8')
      | ~ r1_tarski(A_508,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_1153])).

tff(c_1185,plain,(
    ! [B_510] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_510),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_510,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1005,c_1171])).

tff(c_1189,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1185])).

tff(c_1192,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_107,c_44,c_426,c_44,c_1189])).

tff(c_1194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:05:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.60  
% 3.37/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.61  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.71/1.61  
% 3.71/1.61  %Foreground sorts:
% 3.71/1.61  
% 3.71/1.61  
% 3.71/1.61  %Background operators:
% 3.71/1.61  
% 3.71/1.61  
% 3.71/1.61  %Foreground operators:
% 3.71/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.71/1.61  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.71/1.61  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.71/1.61  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.71/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.71/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.71/1.61  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.71/1.61  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.71/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.71/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.71/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.71/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.71/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.71/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.71/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.71/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.71/1.61  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.71/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.71/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.71/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.71/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.71/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.71/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.71/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.71/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.71/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.71/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.71/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.71/1.61  
% 3.71/1.63  tff(f_227, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.71/1.63  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.71/1.63  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.71/1.63  tff(f_63, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_pre_topc)).
% 3.71/1.63  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.71/1.63  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.71/1.63  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.71/1.63  tff(f_107, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.71/1.63  tff(f_95, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.71/1.63  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.71/1.63  tff(f_111, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.71/1.63  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.71/1.63  tff(f_178, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.71/1.63  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_119, plain, (![B_420, A_421]: (v2_pre_topc(B_420) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.71/1.63  tff(c_128, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_119])).
% 3.71/1.63  tff(c_135, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_128])).
% 3.71/1.63  tff(c_91, plain, (![B_414, A_415]: (l1_pre_topc(B_414) | ~m1_pre_topc(B_414, A_415) | ~l1_pre_topc(A_415))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.71/1.63  tff(c_100, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_91])).
% 3.71/1.63  tff(c_107, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_100])).
% 3.71/1.63  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_125, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_119])).
% 3.71/1.63  tff(c_132, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_125])).
% 3.71/1.63  tff(c_97, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_91])).
% 3.71/1.63  tff(c_104, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97])).
% 3.71/1.63  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_142, plain, (![A_423]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_423), u1_pre_topc(A_423))) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.71/1.63  tff(c_145, plain, (v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_142])).
% 3.71/1.63  tff(c_147, plain, (v1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_104, c_145])).
% 3.71/1.63  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.71/1.63  tff(c_12, plain, (![A_10]: (m1_subset_1(u1_pre_topc(A_10), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.71/1.63  tff(c_249, plain, (![D_439, B_440, C_441, A_442]: (D_439=B_440 | g1_pre_topc(C_441, D_439)!=g1_pre_topc(A_442, B_440) | ~m1_subset_1(B_440, k1_zfmisc_1(k1_zfmisc_1(A_442))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.71/1.63  tff(c_257, plain, (![D_439, C_441]: (u1_pre_topc('#skF_4')=D_439 | g1_pre_topc(C_441, D_439)!='#skF_5' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_249])).
% 3.71/1.63  tff(c_284, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_257])).
% 3.71/1.63  tff(c_287, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_284])).
% 3.71/1.63  tff(c_294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_287])).
% 3.71/1.63  tff(c_297, plain, (![D_448, C_449]: (u1_pre_topc('#skF_4')=D_448 | g1_pre_topc(C_449, D_448)!='#skF_5')), inference(splitRight, [status(thm)], [c_257])).
% 3.71/1.63  tff(c_325, plain, (![A_450]: (u1_pre_topc(A_450)=u1_pre_topc('#skF_4') | A_450!='#skF_5' | ~v1_pre_topc(A_450) | ~l1_pre_topc(A_450))), inference(superposition, [status(thm), theory('equality')], [c_6, c_297])).
% 3.71/1.63  tff(c_328, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_147, c_325])).
% 3.71/1.63  tff(c_334, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_328])).
% 3.71/1.63  tff(c_366, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))='#skF_5' | ~v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_334, c_6])).
% 3.71/1.63  tff(c_386, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_4'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_147, c_366])).
% 3.71/1.63  tff(c_296, plain, (m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_257])).
% 3.71/1.63  tff(c_210, plain, (![C_430, A_431, D_432, B_433]: (C_430=A_431 | g1_pre_topc(C_430, D_432)!=g1_pre_topc(A_431, B_433) | ~m1_subset_1(B_433, k1_zfmisc_1(k1_zfmisc_1(A_431))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.71/1.63  tff(c_218, plain, (![C_430, D_432]: (u1_struct_0('#skF_4')=C_430 | g1_pre_topc(C_430, D_432)!='#skF_5' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_210])).
% 3.71/1.63  tff(c_416, plain, (![C_453, D_454]: (u1_struct_0('#skF_4')=C_453 | g1_pre_topc(C_453, D_454)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_296, c_218])).
% 3.71/1.63  tff(c_426, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_386, c_416])).
% 3.71/1.63  tff(c_28, plain, (![A_25, B_26]: (m1_connsp_2('#skF_1'(A_25, B_26), A_25, B_26) | ~m1_subset_1(B_26, u1_struct_0(A_25)) | ~l1_pre_topc(A_25) | ~v2_pre_topc(A_25) | v2_struct_0(A_25))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.71/1.63  tff(c_687, plain, (![C_466, A_467, B_468]: (m1_subset_1(C_466, k1_zfmisc_1(u1_struct_0(A_467))) | ~m1_connsp_2(C_466, A_467, B_468) | ~m1_subset_1(B_468, u1_struct_0(A_467)) | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467) | v2_struct_0(A_467))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.71/1.63  tff(c_983, plain, (![A_490, B_491]: (m1_subset_1('#skF_1'(A_490, B_491), k1_zfmisc_1(u1_struct_0(A_490))) | ~m1_subset_1(B_491, u1_struct_0(A_490)) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(resolution, [status(thm)], [c_28, c_687])).
% 3.71/1.63  tff(c_989, plain, (![B_491]: (m1_subset_1('#skF_1'('#skF_5', B_491), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_491, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_426, c_983])).
% 3.71/1.63  tff(c_992, plain, (![B_491]: (m1_subset_1('#skF_1'('#skF_5', B_491), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_491, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_107, c_426, c_989])).
% 3.71/1.63  tff(c_1001, plain, (![B_499]: (m1_subset_1('#skF_1'('#skF_5', B_499), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_499, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_992])).
% 3.71/1.63  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.71/1.63  tff(c_1005, plain, (![B_499]: (r1_tarski('#skF_1'('#skF_5', B_499), u1_struct_0('#skF_4')) | ~m1_subset_1(B_499, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1001, c_2])).
% 3.71/1.63  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.71/1.63  tff(c_30, plain, (![A_28]: (m1_pre_topc(A_28, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.71/1.63  tff(c_473, plain, (![A_455, B_456]: (m1_pre_topc(A_455, g1_pre_topc(u1_struct_0(B_456), u1_pre_topc(B_456))) | ~m1_pre_topc(A_455, B_456) | ~l1_pre_topc(B_456) | ~l1_pre_topc(A_455))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.71/1.63  tff(c_500, plain, (![A_455]: (m1_pre_topc(A_455, '#skF_5') | ~m1_pre_topc(A_455, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_455))), inference(superposition, [status(thm), theory('equality')], [c_48, c_473])).
% 3.71/1.63  tff(c_513, plain, (![A_455]: (m1_pre_topc(A_455, '#skF_5') | ~m1_pre_topc(A_455, '#skF_4') | ~l1_pre_topc(A_455))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_500])).
% 3.71/1.63  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_38, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 3.71/1.63  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_432, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_52])).
% 3.71/1.63  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_431, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_426, c_50])).
% 3.71/1.63  tff(c_40, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_227])).
% 3.71/1.63  tff(c_994, plain, (![F_492, C_497, H_493, E_498, B_496, D_494, A_495]: (r1_tmap_1(D_494, B_496, E_498, H_493) | ~r1_tmap_1(C_497, B_496, k3_tmap_1(A_495, B_496, D_494, C_497, E_498), H_493) | ~m1_connsp_2(F_492, D_494, H_493) | ~r1_tarski(F_492, u1_struct_0(C_497)) | ~m1_subset_1(H_493, u1_struct_0(C_497)) | ~m1_subset_1(H_493, u1_struct_0(D_494)) | ~m1_subset_1(F_492, k1_zfmisc_1(u1_struct_0(D_494))) | ~m1_pre_topc(C_497, D_494) | ~m1_subset_1(E_498, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_494), u1_struct_0(B_496)))) | ~v1_funct_2(E_498, u1_struct_0(D_494), u1_struct_0(B_496)) | ~v1_funct_1(E_498) | ~m1_pre_topc(D_494, A_495) | v2_struct_0(D_494) | ~m1_pre_topc(C_497, A_495) | v2_struct_0(C_497) | ~l1_pre_topc(B_496) | ~v2_pre_topc(B_496) | v2_struct_0(B_496) | ~l1_pre_topc(A_495) | ~v2_pre_topc(A_495) | v2_struct_0(A_495))), inference(cnfTransformation, [status(thm)], [f_178])).
% 3.71/1.63  tff(c_996, plain, (![F_492]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_492, '#skF_5', '#skF_8') | ~r1_tarski(F_492, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_492, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_994])).
% 3.71/1.63  tff(c_999, plain, (![F_492]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_492, '#skF_5', '#skF_8') | ~r1_tarski(F_492, u1_struct_0('#skF_4')) | ~m1_subset_1(F_492, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_432, c_426, c_431, c_426, c_426, c_44, c_426, c_44, c_996])).
% 3.71/1.63  tff(c_1000, plain, (![F_492]: (~m1_connsp_2(F_492, '#skF_5', '#skF_8') | ~r1_tarski(F_492, u1_struct_0('#skF_4')) | ~m1_subset_1(F_492, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_76, c_999])).
% 3.71/1.63  tff(c_1014, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1000])).
% 3.71/1.63  tff(c_1017, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_513, c_1014])).
% 3.71/1.63  tff(c_1020, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1017])).
% 3.71/1.63  tff(c_1023, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_1020])).
% 3.71/1.63  tff(c_1027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1023])).
% 3.71/1.63  tff(c_1153, plain, (![F_507]: (~m1_connsp_2(F_507, '#skF_5', '#skF_8') | ~r1_tarski(F_507, u1_struct_0('#skF_4')) | ~m1_subset_1(F_507, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1000])).
% 3.71/1.63  tff(c_1171, plain, (![A_508]: (~m1_connsp_2(A_508, '#skF_5', '#skF_8') | ~r1_tarski(A_508, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_1153])).
% 3.71/1.63  tff(c_1185, plain, (![B_510]: (~m1_connsp_2('#skF_1'('#skF_5', B_510), '#skF_5', '#skF_8') | ~m1_subset_1(B_510, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1005, c_1171])).
% 3.71/1.63  tff(c_1189, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_1185])).
% 3.71/1.63  tff(c_1192, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_107, c_44, c_426, c_44, c_1189])).
% 3.71/1.63  tff(c_1194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1192])).
% 3.71/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.63  
% 3.71/1.63  Inference rules
% 3.71/1.63  ----------------------
% 3.71/1.63  #Ref     : 5
% 3.71/1.63  #Sup     : 215
% 3.71/1.63  #Fact    : 0
% 3.71/1.63  #Define  : 0
% 3.71/1.63  #Split   : 6
% 3.71/1.63  #Chain   : 0
% 3.71/1.63  #Close   : 0
% 3.71/1.63  
% 3.71/1.63  Ordering : KBO
% 3.71/1.63  
% 3.71/1.63  Simplification rules
% 3.71/1.63  ----------------------
% 3.71/1.63  #Subsume      : 54
% 3.71/1.63  #Demod        : 352
% 3.71/1.63  #Tautology    : 95
% 3.71/1.63  #SimpNegUnit  : 6
% 3.71/1.63  #BackRed      : 5
% 3.71/1.63  
% 3.71/1.63  #Partial instantiations: 0
% 3.71/1.63  #Strategies tried      : 1
% 3.71/1.63  
% 3.71/1.63  Timing (in seconds)
% 3.71/1.63  ----------------------
% 3.71/1.63  Preprocessing        : 0.40
% 3.71/1.63  Parsing              : 0.21
% 3.71/1.63  CNF conversion       : 0.06
% 3.71/1.63  Main loop            : 0.42
% 3.71/1.63  Inferencing          : 0.14
% 3.71/1.63  Reduction            : 0.14
% 3.71/1.63  Demodulation         : 0.11
% 3.71/1.63  BG Simplification    : 0.02
% 3.71/1.63  Subsumption          : 0.09
% 3.71/1.63  Abstraction          : 0.02
% 3.71/1.63  MUC search           : 0.00
% 3.71/1.63  Cooper               : 0.00
% 3.71/1.63  Total                : 0.87
% 3.71/1.63  Index Insertion      : 0.00
% 3.71/1.63  Index Deletion       : 0.00
% 3.71/1.63  Index Matching       : 0.00
% 3.71/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
