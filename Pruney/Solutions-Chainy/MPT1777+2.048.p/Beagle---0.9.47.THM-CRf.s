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
% DateTime   : Thu Dec  3 10:27:39 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 778 expanded)
%              Number of leaves         :   40 ( 290 expanded)
%              Depth                    :   17
%              Number of atoms          :  278 (4159 expanded)
%              Number of equality atoms :   13 ( 384 expanded)
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

tff(f_237,negated_conjecture,(
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

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_110,axiom,(
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

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_188,axiom,(
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

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_127,plain,(
    ! [B_425,A_426] :
      ( v2_pre_topc(B_425)
      | ~ m1_pre_topc(B_425,A_426)
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_127])).

tff(c_143,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_136])).

tff(c_100,plain,(
    ! [B_421,A_422] :
      ( l1_pre_topc(B_421)
      | ~ m1_pre_topc(B_421,A_422)
      | ~ l1_pre_topc(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_109,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_100])).

tff(c_116,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_109])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_106,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_100])).

tff(c_113,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_106])).

tff(c_30,plain,(
    ! [A_29] :
      ( m1_pre_topc(A_29,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_160,plain,(
    ! [B_431,A_432] :
      ( m1_pre_topc(B_431,A_432)
      | ~ m1_pre_topc(B_431,g1_pre_topc(u1_struct_0(A_432),u1_pre_topc(A_432)))
      | ~ l1_pre_topc(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_163,plain,(
    ! [B_431] :
      ( m1_pre_topc(B_431,'#skF_4')
      | ~ m1_pre_topc(B_431,'#skF_5')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_160])).

tff(c_171,plain,(
    ! [B_433] :
      ( m1_pre_topc(B_433,'#skF_4')
      | ~ m1_pre_topc(B_433,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_163])).

tff(c_175,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_171])).

tff(c_178,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_175])).

tff(c_32,plain,(
    ! [B_32,A_30] :
      ( r1_tarski(u1_struct_0(B_32),u1_struct_0(A_30))
      | ~ m1_pre_topc(B_32,A_30)
      | ~ l1_pre_topc(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_150,plain,(
    ! [B_428,A_429] :
      ( r1_tarski(u1_struct_0(B_428),u1_struct_0(A_429))
      | ~ m1_pre_topc(B_428,A_429)
      | ~ l1_pre_topc(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_265,plain,(
    ! [B_440,A_441] :
      ( u1_struct_0(B_440) = u1_struct_0(A_441)
      | ~ r1_tarski(u1_struct_0(A_441),u1_struct_0(B_440))
      | ~ m1_pre_topc(B_440,A_441)
      | ~ l1_pre_topc(A_441) ) ),
    inference(resolution,[status(thm)],[c_150,c_2])).

tff(c_277,plain,(
    ! [B_444,A_445] :
      ( u1_struct_0(B_444) = u1_struct_0(A_445)
      | ~ m1_pre_topc(A_445,B_444)
      | ~ l1_pre_topc(B_444)
      | ~ m1_pre_topc(B_444,A_445)
      | ~ l1_pre_topc(A_445) ) ),
    inference(resolution,[status(thm)],[c_32,c_265])).

tff(c_283,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_178,c_277])).

tff(c_298,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_113,c_283])).

tff(c_307,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_298])).

tff(c_133,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_127])).

tff(c_140,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_133])).

tff(c_796,plain,(
    ! [C_476,A_477] :
      ( m1_pre_topc(C_476,A_477)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(C_476),u1_pre_topc(C_476)),A_477)
      | ~ l1_pre_topc(C_476)
      | ~ v2_pre_topc(C_476)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(C_476),u1_pre_topc(C_476)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(C_476),u1_pre_topc(C_476)))
      | ~ l1_pre_topc(A_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_811,plain,(
    ! [A_477] :
      ( m1_pre_topc('#skF_4',A_477)
      | ~ m1_pre_topc('#skF_5',A_477)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')))
      | ~ l1_pre_topc(A_477) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_796])).

tff(c_825,plain,(
    ! [A_478] :
      ( m1_pre_topc('#skF_4',A_478)
      | ~ m1_pre_topc('#skF_5',A_478)
      | ~ l1_pre_topc(A_478) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_50,c_116,c_50,c_140,c_113,c_811])).

tff(c_838,plain,
    ( m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_825])).

tff(c_849,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_838])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_307,c_849])).

tff(c_852,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( m1_connsp_2('#skF_1'(A_19,B_20),A_19,B_20)
      | ~ m1_subset_1(B_20,u1_struct_0(A_19))
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19)
      | v2_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_943,plain,(
    ! [C_479,A_480,B_481] :
      ( m1_subset_1(C_479,k1_zfmisc_1(u1_struct_0(A_480)))
      | ~ m1_connsp_2(C_479,A_480,B_481)
      | ~ m1_subset_1(B_481,u1_struct_0(A_480))
      | ~ l1_pre_topc(A_480)
      | ~ v2_pre_topc(A_480)
      | v2_struct_0(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1636,plain,(
    ! [A_522,B_523] :
      ( m1_subset_1('#skF_1'(A_522,B_523),k1_zfmisc_1(u1_struct_0(A_522)))
      | ~ m1_subset_1(B_523,u1_struct_0(A_522))
      | ~ l1_pre_topc(A_522)
      | ~ v2_pre_topc(A_522)
      | v2_struct_0(A_522) ) ),
    inference(resolution,[status(thm)],[c_24,c_943])).

tff(c_1642,plain,(
    ! [B_523] :
      ( m1_subset_1('#skF_1'('#skF_5',B_523),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_523,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_1636])).

tff(c_1645,plain,(
    ! [B_523] :
      ( m1_subset_1('#skF_1'('#skF_5',B_523),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_523,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_116,c_852,c_1642])).

tff(c_1647,plain,(
    ! [B_524] :
      ( m1_subset_1('#skF_1'('#skF_5',B_524),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_524,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1645])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1652,plain,(
    ! [B_525] :
      ( r1_tarski('#skF_1'('#skF_5',B_525),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_525,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1647,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_44,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_78,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_54,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_903,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_902,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_52])).

tff(c_853,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_298])).

tff(c_42,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_1407,plain,(
    ! [A_502,D_505,B_504,F_503,H_506,C_501,E_507] :
      ( r1_tmap_1(D_505,B_504,E_507,H_506)
      | ~ r1_tmap_1(C_501,B_504,k3_tmap_1(A_502,B_504,D_505,C_501,E_507),H_506)
      | ~ m1_connsp_2(F_503,D_505,H_506)
      | ~ r1_tarski(F_503,u1_struct_0(C_501))
      | ~ m1_subset_1(H_506,u1_struct_0(C_501))
      | ~ m1_subset_1(H_506,u1_struct_0(D_505))
      | ~ m1_subset_1(F_503,k1_zfmisc_1(u1_struct_0(D_505)))
      | ~ m1_pre_topc(C_501,D_505)
      | ~ m1_subset_1(E_507,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_505),u1_struct_0(B_504))))
      | ~ v1_funct_2(E_507,u1_struct_0(D_505),u1_struct_0(B_504))
      | ~ v1_funct_1(E_507)
      | ~ m1_pre_topc(D_505,A_502)
      | v2_struct_0(D_505)
      | ~ m1_pre_topc(C_501,A_502)
      | v2_struct_0(C_501)
      | ~ l1_pre_topc(B_504)
      | ~ v2_pre_topc(B_504)
      | v2_struct_0(B_504)
      | ~ l1_pre_topc(A_502)
      | ~ v2_pre_topc(A_502)
      | v2_struct_0(A_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1409,plain,(
    ! [F_503] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_503,'#skF_5','#skF_8')
      | ~ r1_tarski(F_503,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_503,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_42,c_1407])).

tff(c_1412,plain,(
    ! [F_503] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_503,'#skF_5','#skF_8')
      | ~ r1_tarski(F_503,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_503,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_903,c_852,c_902,c_852,c_853,c_852,c_46,c_852,c_46,c_1409])).

tff(c_1414,plain,(
    ! [F_508] :
      ( ~ m1_connsp_2(F_508,'#skF_5','#skF_8')
      | ~ r1_tarski(F_508,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_508,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_78,c_1412])).

tff(c_1419,plain,(
    ! [A_3] :
      ( ~ m1_connsp_2(A_3,'#skF_5','#skF_8')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1414])).

tff(c_1660,plain,(
    ! [B_526] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_526),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_526,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1652,c_1419])).

tff(c_1664,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1660])).

tff(c_1667,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_116,c_46,c_852,c_46,c_1664])).

tff(c_1669,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1667])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.73  
% 4.11/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.73  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.11/1.73  
% 4.11/1.73  %Foreground sorts:
% 4.11/1.73  
% 4.11/1.73  
% 4.11/1.73  %Background operators:
% 4.11/1.73  
% 4.11/1.73  
% 4.11/1.73  %Foreground operators:
% 4.11/1.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.11/1.73  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.11/1.73  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.11/1.73  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.11/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.11/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.73  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.11/1.73  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.11/1.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.11/1.73  tff('#skF_7', type, '#skF_7': $i).
% 4.11/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.11/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.11/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.11/1.73  tff('#skF_2', type, '#skF_2': $i).
% 4.11/1.73  tff('#skF_3', type, '#skF_3': $i).
% 4.11/1.73  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.11/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.11/1.73  tff('#skF_8', type, '#skF_8': $i).
% 4.11/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.11/1.73  tff('#skF_4', type, '#skF_4': $i).
% 4.11/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.73  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.11/1.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.11/1.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.11/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.11/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.11/1.73  
% 4.43/1.77  tff(f_237, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.43/1.77  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.43/1.77  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.43/1.77  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.43/1.77  tff(f_66, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.43/1.77  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.43/1.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.43/1.77  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: ((v2_pre_topc(B) & l1_pre_topc(B)) => (![C]: ((v2_pre_topc(C) & l1_pre_topc(C)) => ((B = g1_pre_topc(u1_struct_0(C), u1_pre_topc(C))) => (m1_pre_topc(B, A) <=> m1_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_tmap_1)).
% 4.43/1.77  tff(f_92, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.43/1.77  tff(f_80, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.43/1.77  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.43/1.77  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.43/1.77  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_127, plain, (![B_425, A_426]: (v2_pre_topc(B_425) | ~m1_pre_topc(B_425, A_426) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.43/1.77  tff(c_136, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_127])).
% 4.43/1.77  tff(c_143, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_136])).
% 4.43/1.77  tff(c_100, plain, (![B_421, A_422]: (l1_pre_topc(B_421) | ~m1_pre_topc(B_421, A_422) | ~l1_pre_topc(A_422))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.43/1.77  tff(c_109, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_100])).
% 4.43/1.77  tff(c_116, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_109])).
% 4.43/1.77  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_106, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_100])).
% 4.43/1.77  tff(c_113, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_106])).
% 4.43/1.77  tff(c_30, plain, (![A_29]: (m1_pre_topc(A_29, A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.43/1.77  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_160, plain, (![B_431, A_432]: (m1_pre_topc(B_431, A_432) | ~m1_pre_topc(B_431, g1_pre_topc(u1_struct_0(A_432), u1_pre_topc(A_432))) | ~l1_pre_topc(A_432))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.43/1.77  tff(c_163, plain, (![B_431]: (m1_pre_topc(B_431, '#skF_4') | ~m1_pre_topc(B_431, '#skF_5') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_160])).
% 4.43/1.77  tff(c_171, plain, (![B_433]: (m1_pre_topc(B_433, '#skF_4') | ~m1_pre_topc(B_433, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_163])).
% 4.43/1.77  tff(c_175, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_30, c_171])).
% 4.43/1.77  tff(c_178, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_175])).
% 4.43/1.77  tff(c_32, plain, (![B_32, A_30]: (r1_tarski(u1_struct_0(B_32), u1_struct_0(A_30)) | ~m1_pre_topc(B_32, A_30) | ~l1_pre_topc(A_30))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.43/1.77  tff(c_150, plain, (![B_428, A_429]: (r1_tarski(u1_struct_0(B_428), u1_struct_0(A_429)) | ~m1_pre_topc(B_428, A_429) | ~l1_pre_topc(A_429))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.43/1.77  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.43/1.77  tff(c_265, plain, (![B_440, A_441]: (u1_struct_0(B_440)=u1_struct_0(A_441) | ~r1_tarski(u1_struct_0(A_441), u1_struct_0(B_440)) | ~m1_pre_topc(B_440, A_441) | ~l1_pre_topc(A_441))), inference(resolution, [status(thm)], [c_150, c_2])).
% 4.43/1.77  tff(c_277, plain, (![B_444, A_445]: (u1_struct_0(B_444)=u1_struct_0(A_445) | ~m1_pre_topc(A_445, B_444) | ~l1_pre_topc(B_444) | ~m1_pre_topc(B_444, A_445) | ~l1_pre_topc(A_445))), inference(resolution, [status(thm)], [c_32, c_265])).
% 4.43/1.77  tff(c_283, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_178, c_277])).
% 4.43/1.77  tff(c_298, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_113, c_283])).
% 4.43/1.77  tff(c_307, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_298])).
% 4.43/1.77  tff(c_133, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_127])).
% 4.43/1.77  tff(c_140, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_133])).
% 4.43/1.77  tff(c_796, plain, (![C_476, A_477]: (m1_pre_topc(C_476, A_477) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(C_476), u1_pre_topc(C_476)), A_477) | ~l1_pre_topc(C_476) | ~v2_pre_topc(C_476) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(C_476), u1_pre_topc(C_476))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(C_476), u1_pre_topc(C_476))) | ~l1_pre_topc(A_477))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.43/1.77  tff(c_811, plain, (![A_477]: (m1_pre_topc('#skF_4', A_477) | ~m1_pre_topc('#skF_5', A_477) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))) | ~l1_pre_topc(A_477))), inference(superposition, [status(thm), theory('equality')], [c_50, c_796])).
% 4.43/1.77  tff(c_825, plain, (![A_478]: (m1_pre_topc('#skF_4', A_478) | ~m1_pre_topc('#skF_5', A_478) | ~l1_pre_topc(A_478))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_50, c_116, c_50, c_140, c_113, c_811])).
% 4.43/1.77  tff(c_838, plain, (m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_30, c_825])).
% 4.43/1.77  tff(c_849, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_838])).
% 4.43/1.77  tff(c_851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_307, c_849])).
% 4.43/1.77  tff(c_852, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_298])).
% 4.43/1.77  tff(c_24, plain, (![A_19, B_20]: (m1_connsp_2('#skF_1'(A_19, B_20), A_19, B_20) | ~m1_subset_1(B_20, u1_struct_0(A_19)) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19) | v2_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.43/1.77  tff(c_943, plain, (![C_479, A_480, B_481]: (m1_subset_1(C_479, k1_zfmisc_1(u1_struct_0(A_480))) | ~m1_connsp_2(C_479, A_480, B_481) | ~m1_subset_1(B_481, u1_struct_0(A_480)) | ~l1_pre_topc(A_480) | ~v2_pre_topc(A_480) | v2_struct_0(A_480))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.43/1.77  tff(c_1636, plain, (![A_522, B_523]: (m1_subset_1('#skF_1'(A_522, B_523), k1_zfmisc_1(u1_struct_0(A_522))) | ~m1_subset_1(B_523, u1_struct_0(A_522)) | ~l1_pre_topc(A_522) | ~v2_pre_topc(A_522) | v2_struct_0(A_522))), inference(resolution, [status(thm)], [c_24, c_943])).
% 4.43/1.77  tff(c_1642, plain, (![B_523]: (m1_subset_1('#skF_1'('#skF_5', B_523), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_523, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_852, c_1636])).
% 4.43/1.77  tff(c_1645, plain, (![B_523]: (m1_subset_1('#skF_1'('#skF_5', B_523), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_523, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_116, c_852, c_1642])).
% 4.43/1.77  tff(c_1647, plain, (![B_524]: (m1_subset_1('#skF_1'('#skF_5', B_524), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_524, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1645])).
% 4.43/1.77  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.43/1.77  tff(c_1652, plain, (![B_525]: (r1_tarski('#skF_1'('#skF_5', B_525), u1_struct_0('#skF_4')) | ~m1_subset_1(B_525, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1647, c_8])).
% 4.43/1.77  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.43/1.77  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_44, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_40, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_78, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40])).
% 4.43/1.77  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_54, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_903, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_852, c_54])).
% 4.43/1.77  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_902, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_852, c_52])).
% 4.43/1.77  tff(c_853, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_298])).
% 4.43/1.77  tff(c_42, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_237])).
% 4.43/1.77  tff(c_1407, plain, (![A_502, D_505, B_504, F_503, H_506, C_501, E_507]: (r1_tmap_1(D_505, B_504, E_507, H_506) | ~r1_tmap_1(C_501, B_504, k3_tmap_1(A_502, B_504, D_505, C_501, E_507), H_506) | ~m1_connsp_2(F_503, D_505, H_506) | ~r1_tarski(F_503, u1_struct_0(C_501)) | ~m1_subset_1(H_506, u1_struct_0(C_501)) | ~m1_subset_1(H_506, u1_struct_0(D_505)) | ~m1_subset_1(F_503, k1_zfmisc_1(u1_struct_0(D_505))) | ~m1_pre_topc(C_501, D_505) | ~m1_subset_1(E_507, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_505), u1_struct_0(B_504)))) | ~v1_funct_2(E_507, u1_struct_0(D_505), u1_struct_0(B_504)) | ~v1_funct_1(E_507) | ~m1_pre_topc(D_505, A_502) | v2_struct_0(D_505) | ~m1_pre_topc(C_501, A_502) | v2_struct_0(C_501) | ~l1_pre_topc(B_504) | ~v2_pre_topc(B_504) | v2_struct_0(B_504) | ~l1_pre_topc(A_502) | ~v2_pre_topc(A_502) | v2_struct_0(A_502))), inference(cnfTransformation, [status(thm)], [f_188])).
% 4.43/1.77  tff(c_1409, plain, (![F_503]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_503, '#skF_5', '#skF_8') | ~r1_tarski(F_503, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_503, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_1407])).
% 4.43/1.77  tff(c_1412, plain, (![F_503]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_503, '#skF_5', '#skF_8') | ~r1_tarski(F_503, u1_struct_0('#skF_4')) | ~m1_subset_1(F_503, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_903, c_852, c_902, c_852, c_853, c_852, c_46, c_852, c_46, c_1409])).
% 4.43/1.77  tff(c_1414, plain, (![F_508]: (~m1_connsp_2(F_508, '#skF_5', '#skF_8') | ~r1_tarski(F_508, u1_struct_0('#skF_4')) | ~m1_subset_1(F_508, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_78, c_1412])).
% 4.43/1.77  tff(c_1419, plain, (![A_3]: (~m1_connsp_2(A_3, '#skF_5', '#skF_8') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_1414])).
% 4.43/1.77  tff(c_1660, plain, (![B_526]: (~m1_connsp_2('#skF_1'('#skF_5', B_526), '#skF_5', '#skF_8') | ~m1_subset_1(B_526, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1652, c_1419])).
% 4.43/1.77  tff(c_1664, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1660])).
% 4.43/1.77  tff(c_1667, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_116, c_46, c_852, c_46, c_1664])).
% 4.43/1.77  tff(c_1669, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1667])).
% 4.43/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.43/1.77  
% 4.43/1.77  Inference rules
% 4.43/1.77  ----------------------
% 4.43/1.77  #Ref     : 0
% 4.43/1.77  #Sup     : 308
% 4.43/1.77  #Fact    : 0
% 4.43/1.77  #Define  : 0
% 4.43/1.77  #Split   : 8
% 4.43/1.77  #Chain   : 0
% 4.43/1.77  #Close   : 0
% 4.43/1.77  
% 4.43/1.77  Ordering : KBO
% 4.43/1.77  
% 4.43/1.77  Simplification rules
% 4.43/1.77  ----------------------
% 4.43/1.77  #Subsume      : 102
% 4.43/1.77  #Demod        : 509
% 4.43/1.77  #Tautology    : 95
% 4.43/1.77  #SimpNegUnit  : 4
% 4.43/1.77  #BackRed      : 5
% 4.43/1.77  
% 4.43/1.77  #Partial instantiations: 0
% 4.43/1.77  #Strategies tried      : 1
% 4.43/1.77  
% 4.43/1.77  Timing (in seconds)
% 4.43/1.77  ----------------------
% 4.43/1.77  Preprocessing        : 0.40
% 4.43/1.77  Parsing              : 0.21
% 4.43/1.77  CNF conversion       : 0.06
% 4.43/1.77  Main loop            : 0.54
% 4.43/1.78  Inferencing          : 0.18
% 4.43/1.78  Reduction            : 0.18
% 4.43/1.78  Demodulation         : 0.14
% 4.43/1.78  BG Simplification    : 0.03
% 4.48/1.78  Subsumption          : 0.13
% 4.48/1.78  Abstraction          : 0.02
% 4.48/1.78  MUC search           : 0.00
% 4.48/1.78  Cooper               : 0.00
% 4.48/1.78  Total                : 1.02
% 4.48/1.78  Index Insertion      : 0.00
% 4.48/1.78  Index Deletion       : 0.00
% 4.48/1.78  Index Matching       : 0.00
% 4.48/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
