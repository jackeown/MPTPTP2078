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
% DateTime   : Thu Dec  3 10:27:33 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 794 expanded)
%              Number of leaves         :   42 ( 301 expanded)
%              Depth                    :   17
%              Number of atoms          :  391 (5344 expanded)
%              Number of equality atoms :   32 ( 473 expanded)
%              Maximal formula depth    :   29 (   5 average)
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

tff(f_246,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_130,axiom,(
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

tff(f_142,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_197,axiom,(
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

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_127,plain,(
    ! [B_435,A_436] :
      ( v2_pre_topc(B_435)
      | ~ m1_pre_topc(B_435,A_436)
      | ~ l1_pre_topc(A_436)
      | ~ v2_pre_topc(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_136,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_127])).

tff(c_143,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_136])).

tff(c_100,plain,(
    ! [B_431,A_432] :
      ( l1_pre_topc(B_431)
      | ~ m1_pre_topc(B_431,A_432)
      | ~ l1_pre_topc(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_109,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_100])).

tff(c_116,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_109])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_106,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_100])).

tff(c_113,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_106])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_144,plain,(
    ! [A_437] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_437),u1_pre_topc(A_437)))
      | ~ l1_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_147,plain,
    ( v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_144])).

tff(c_149,plain,
    ( v1_pre_topc('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_147])).

tff(c_150,plain,(
    v1_pre_topc('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_149])).

tff(c_12,plain,(
    ! [A_5] :
      ( g1_pre_topc(u1_struct_0(A_5),u1_pre_topc(A_5)) = A_5
      | ~ v1_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1419,plain,(
    ! [D_532,B_533,C_534,A_535] :
      ( m1_pre_topc(D_532,B_533)
      | ~ m1_pre_topc(C_534,A_535)
      | g1_pre_topc(u1_struct_0(D_532),u1_pre_topc(D_532)) != g1_pre_topc(u1_struct_0(C_534),u1_pre_topc(C_534))
      | g1_pre_topc(u1_struct_0(B_533),u1_pre_topc(B_533)) != g1_pre_topc(u1_struct_0(A_535),u1_pre_topc(A_535))
      | ~ l1_pre_topc(D_532)
      | ~ l1_pre_topc(C_534)
      | ~ l1_pre_topc(B_533)
      | ~ l1_pre_topc(A_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1451,plain,(
    ! [D_532,B_533,A_35] :
      ( m1_pre_topc(D_532,B_533)
      | g1_pre_topc(u1_struct_0(D_532),u1_pre_topc(D_532)) != g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35))
      | g1_pre_topc(u1_struct_0(B_533),u1_pre_topc(B_533)) != g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35))
      | ~ l1_pre_topc(D_532)
      | ~ l1_pre_topc(B_533)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_28,c_1419])).

tff(c_2307,plain,(
    ! [A_607,B_608] :
      ( m1_pre_topc(A_607,B_608)
      | g1_pre_topc(u1_struct_0(B_608),u1_pre_topc(B_608)) != g1_pre_topc(u1_struct_0(A_607),u1_pre_topc(A_607))
      | ~ l1_pre_topc(A_607)
      | ~ l1_pre_topc(B_608)
      | ~ l1_pre_topc(A_607) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1451])).

tff(c_2313,plain,(
    ! [A_607] :
      ( m1_pre_topc(A_607,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_607),u1_pre_topc(A_607)) != '#skF_5'
      | ~ l1_pre_topc(A_607)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_607) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2307])).

tff(c_2320,plain,(
    ! [A_609] :
      ( m1_pre_topc(A_609,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_609),u1_pre_topc(A_609)) != '#skF_5'
      | ~ l1_pre_topc(A_609) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2313])).

tff(c_2331,plain,(
    ! [A_610] :
      ( m1_pre_topc(A_610,'#skF_4')
      | A_610 != '#skF_5'
      | ~ l1_pre_topc(A_610)
      | ~ v1_pre_topc(A_610)
      | ~ l1_pre_topc(A_610) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2320])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_331,plain,(
    ! [B_458,C_459,A_460] :
      ( m1_pre_topc(B_458,C_459)
      | ~ r1_tarski(u1_struct_0(B_458),u1_struct_0(C_459))
      | ~ m1_pre_topc(C_459,A_460)
      | ~ m1_pre_topc(B_458,A_460)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_389,plain,(
    ! [B_463,A_464] :
      ( m1_pre_topc(B_463,B_463)
      | ~ m1_pre_topc(B_463,A_464)
      | ~ l1_pre_topc(A_464)
      | ~ v2_pre_topc(A_464) ) ),
    inference(resolution,[status(thm)],[c_6,c_331])).

tff(c_397,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_389])).

tff(c_407,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_397])).

tff(c_696,plain,(
    ! [D_476,B_477,C_478,A_479] :
      ( m1_pre_topc(D_476,B_477)
      | ~ m1_pre_topc(C_478,A_479)
      | g1_pre_topc(u1_struct_0(D_476),u1_pre_topc(D_476)) != g1_pre_topc(u1_struct_0(C_478),u1_pre_topc(C_478))
      | g1_pre_topc(u1_struct_0(B_477),u1_pre_topc(B_477)) != g1_pre_topc(u1_struct_0(A_479),u1_pre_topc(A_479))
      | ~ l1_pre_topc(D_476)
      | ~ l1_pre_topc(C_478)
      | ~ l1_pre_topc(B_477)
      | ~ l1_pre_topc(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_700,plain,(
    ! [D_476,B_477] :
      ( m1_pre_topc(D_476,B_477)
      | g1_pre_topc(u1_struct_0(D_476),u1_pre_topc(D_476)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | g1_pre_topc(u1_struct_0(B_477),u1_pre_topc(B_477)) != g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4'))
      | ~ l1_pre_topc(D_476)
      | ~ l1_pre_topc(B_477)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_407,c_696])).

tff(c_922,plain,(
    ! [D_505,B_506] :
      ( m1_pre_topc(D_505,B_506)
      | g1_pre_topc(u1_struct_0(D_505),u1_pre_topc(D_505)) != '#skF_5'
      | g1_pre_topc(u1_struct_0(B_506),u1_pre_topc(B_506)) != '#skF_5'
      | ~ l1_pre_topc(D_505)
      | ~ l1_pre_topc(B_506) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_50,c_50,c_700])).

tff(c_926,plain,(
    ! [B_506] :
      ( m1_pre_topc('#skF_4',B_506)
      | g1_pre_topc(u1_struct_0(B_506),u1_pre_topc(B_506)) != '#skF_5'
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(B_506) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_922])).

tff(c_937,plain,(
    ! [B_514] :
      ( m1_pre_topc('#skF_4',B_514)
      | g1_pre_topc(u1_struct_0(B_514),u1_pre_topc(B_514)) != '#skF_5'
      | ~ l1_pre_topc(B_514) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_926])).

tff(c_948,plain,(
    ! [A_515] :
      ( m1_pre_topc('#skF_4',A_515)
      | A_515 != '#skF_5'
      | ~ l1_pre_topc(A_515)
      | ~ v1_pre_topc(A_515)
      | ~ l1_pre_topc(A_515) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_937])).

tff(c_184,plain,(
    ! [C_440,A_441,B_442] :
      ( m1_pre_topc(C_440,A_441)
      | ~ m1_pre_topc(C_440,B_442)
      | ~ m1_pre_topc(B_442,A_441)
      | ~ l1_pre_topc(A_441)
      | ~ v2_pre_topc(A_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_193,plain,(
    ! [A_441] :
      ( m1_pre_topc('#skF_5',A_441)
      | ~ m1_pre_topc('#skF_2',A_441)
      | ~ l1_pre_topc(A_441)
      | ~ v2_pre_topc(A_441) ) ),
    inference(resolution,[status(thm)],[c_58,c_184])).

tff(c_237,plain,(
    ! [B_449,C_450,A_451] :
      ( r1_tarski(u1_struct_0(B_449),u1_struct_0(C_450))
      | ~ m1_pre_topc(B_449,C_450)
      | ~ m1_pre_topc(C_450,A_451)
      | ~ m1_pre_topc(B_449,A_451)
      | ~ l1_pre_topc(A_451)
      | ~ v2_pre_topc(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_266,plain,(
    ! [B_456,A_457] :
      ( r1_tarski(u1_struct_0(B_456),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_456,'#skF_5')
      | ~ m1_pre_topc(B_456,A_457)
      | ~ m1_pre_topc('#skF_2',A_457)
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457) ) ),
    inference(resolution,[status(thm)],[c_193,c_237])).

tff(c_272,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_266])).

tff(c_280,plain,
    ( r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_272])).

tff(c_284,plain,(
    ~ m1_pre_topc('#skF_2','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_280])).

tff(c_287,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_284])).

tff(c_291,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_287])).

tff(c_292,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_5')
    | r1_tarski(u1_struct_0('#skF_4'),u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_280])).

tff(c_330,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_292])).

tff(c_969,plain,
    ( ~ v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_948,c_330])).

tff(c_1005,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_150,c_969])).

tff(c_1007,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_292])).

tff(c_243,plain,(
    ! [B_449] :
      ( r1_tarski(u1_struct_0(B_449),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_449,'#skF_4')
      | ~ m1_pre_topc(B_449,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_62,c_237])).

tff(c_250,plain,(
    ! [B_449] :
      ( r1_tarski(u1_struct_0(B_449),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_449,'#skF_4')
      | ~ m1_pre_topc(B_449,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_243])).

tff(c_245,plain,(
    ! [B_449] :
      ( r1_tarski(u1_struct_0(B_449),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_449,'#skF_5')
      | ~ m1_pre_topc(B_449,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_237])).

tff(c_258,plain,(
    ! [B_453] :
      ( r1_tarski(u1_struct_0(B_453),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_453,'#skF_5')
      | ~ m1_pre_topc(B_453,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_245])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1038,plain,(
    ! [B_516] :
      ( u1_struct_0(B_516) = u1_struct_0('#skF_5')
      | ~ r1_tarski(u1_struct_0('#skF_5'),u1_struct_0(B_516))
      | ~ m1_pre_topc(B_516,'#skF_5')
      | ~ m1_pre_topc(B_516,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_258,c_2])).

tff(c_1050,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_250,c_1038])).

tff(c_1062,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_62,c_1007,c_1050])).

tff(c_1071,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1062])).

tff(c_2360,plain,
    ( ~ v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_2331,c_1071])).

tff(c_2407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_150,c_2360])).

tff(c_2408,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1062])).

tff(c_26,plain,(
    ! [A_32,B_33] :
      ( m1_connsp_2('#skF_1'(A_32,B_33),A_32,B_33)
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2579,plain,(
    ! [C_616,A_617,B_618] :
      ( m1_subset_1(C_616,k1_zfmisc_1(u1_struct_0(A_617)))
      | ~ m1_connsp_2(C_616,A_617,B_618)
      | ~ m1_subset_1(B_618,u1_struct_0(A_617))
      | ~ l1_pre_topc(A_617)
      | ~ v2_pre_topc(A_617)
      | v2_struct_0(A_617) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_3232,plain,(
    ! [A_658,B_659] :
      ( m1_subset_1('#skF_1'(A_658,B_659),k1_zfmisc_1(u1_struct_0(A_658)))
      | ~ m1_subset_1(B_659,u1_struct_0(A_658))
      | ~ l1_pre_topc(A_658)
      | ~ v2_pre_topc(A_658)
      | v2_struct_0(A_658) ) ),
    inference(resolution,[status(thm)],[c_26,c_2579])).

tff(c_3238,plain,(
    ! [B_659] :
      ( m1_subset_1('#skF_1'('#skF_5',B_659),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_659,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2408,c_3232])).

tff(c_3241,plain,(
    ! [B_659] :
      ( m1_subset_1('#skF_1'('#skF_5',B_659),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_659,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_116,c_2408,c_3238])).

tff(c_3243,plain,(
    ! [B_660] :
      ( m1_subset_1('#skF_1'('#skF_5',B_660),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_660,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3241])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3248,plain,(
    ! [B_661] :
      ( r1_tarski('#skF_1'('#skF_5',B_661),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_661,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3243,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_44,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_78,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_54,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_2482,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_2481,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2408,c_52])).

tff(c_42,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_3159,plain,(
    ! [D_652,F_648,B_651,C_650,E_649,H_647,A_646] :
      ( r1_tmap_1(D_652,B_651,E_649,H_647)
      | ~ r1_tmap_1(C_650,B_651,k3_tmap_1(A_646,B_651,D_652,C_650,E_649),H_647)
      | ~ m1_connsp_2(F_648,D_652,H_647)
      | ~ r1_tarski(F_648,u1_struct_0(C_650))
      | ~ m1_subset_1(H_647,u1_struct_0(C_650))
      | ~ m1_subset_1(H_647,u1_struct_0(D_652))
      | ~ m1_subset_1(F_648,k1_zfmisc_1(u1_struct_0(D_652)))
      | ~ m1_pre_topc(C_650,D_652)
      | ~ m1_subset_1(E_649,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_652),u1_struct_0(B_651))))
      | ~ v1_funct_2(E_649,u1_struct_0(D_652),u1_struct_0(B_651))
      | ~ v1_funct_1(E_649)
      | ~ m1_pre_topc(D_652,A_646)
      | v2_struct_0(D_652)
      | ~ m1_pre_topc(C_650,A_646)
      | v2_struct_0(C_650)
      | ~ l1_pre_topc(B_651)
      | ~ v2_pre_topc(B_651)
      | v2_struct_0(B_651)
      | ~ l1_pre_topc(A_646)
      | ~ v2_pre_topc(A_646)
      | v2_struct_0(A_646) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_3161,plain,(
    ! [F_648] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_648,'#skF_5','#skF_8')
      | ~ r1_tarski(F_648,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_648,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_42,c_3159])).

tff(c_3164,plain,(
    ! [F_648] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_648,'#skF_5','#skF_8')
      | ~ r1_tarski(F_648,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_648,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_2482,c_2408,c_2481,c_2408,c_1007,c_2408,c_46,c_2408,c_46,c_3161])).

tff(c_3166,plain,(
    ! [F_653] :
      ( ~ m1_connsp_2(F_653,'#skF_5','#skF_8')
      | ~ r1_tarski(F_653,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_653,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_78,c_3164])).

tff(c_3171,plain,(
    ! [A_3] :
      ( ~ m1_connsp_2(A_3,'#skF_5','#skF_8')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_3166])).

tff(c_3256,plain,(
    ! [B_662] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_662),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_662,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_3248,c_3171])).

tff(c_3260,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_3256])).

tff(c_3263,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_116,c_46,c_2408,c_46,c_3260])).

tff(c_3265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:09:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.89  
% 4.85/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.89  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.85/1.89  
% 4.85/1.89  %Foreground sorts:
% 4.85/1.89  
% 4.85/1.89  
% 4.85/1.89  %Background operators:
% 4.85/1.89  
% 4.85/1.89  
% 4.85/1.89  %Foreground operators:
% 4.85/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.85/1.89  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.85/1.89  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.85/1.89  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.85/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.85/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.89  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.85/1.89  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.85/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.85/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.85/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.85/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.85/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.85/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.85/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.85/1.89  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.85/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.85/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.85/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.85/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.85/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.85/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.85/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.85/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.85/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/1.89  
% 5.26/1.92  tff(f_246, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.26/1.92  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.26/1.92  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.26/1.92  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 5.26/1.92  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 5.26/1.92  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.26/1.92  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 5.26/1.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.26/1.92  tff(f_130, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 5.26/1.92  tff(f_142, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 5.26/1.92  tff(f_112, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 5.26/1.92  tff(f_100, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 5.26/1.92  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.26/1.92  tff(f_197, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 5.26/1.92  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_127, plain, (![B_435, A_436]: (v2_pre_topc(B_435) | ~m1_pre_topc(B_435, A_436) | ~l1_pre_topc(A_436) | ~v2_pre_topc(A_436))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.26/1.92  tff(c_136, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_127])).
% 5.26/1.92  tff(c_143, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_136])).
% 5.26/1.92  tff(c_100, plain, (![B_431, A_432]: (l1_pre_topc(B_431) | ~m1_pre_topc(B_431, A_432) | ~l1_pre_topc(A_432))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.26/1.92  tff(c_109, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_100])).
% 5.26/1.92  tff(c_116, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_109])).
% 5.26/1.92  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_106, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_100])).
% 5.26/1.92  tff(c_113, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_106])).
% 5.26/1.92  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_144, plain, (![A_437]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_437), u1_pre_topc(A_437))) | ~l1_pre_topc(A_437) | v2_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.26/1.92  tff(c_147, plain, (v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_50, c_144])).
% 5.26/1.92  tff(c_149, plain, (v1_pre_topc('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_147])).
% 5.26/1.92  tff(c_150, plain, (v1_pre_topc('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_149])).
% 5.26/1.92  tff(c_12, plain, (![A_5]: (g1_pre_topc(u1_struct_0(A_5), u1_pre_topc(A_5))=A_5 | ~v1_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.26/1.92  tff(c_28, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_116])).
% 5.26/1.92  tff(c_1419, plain, (![D_532, B_533, C_534, A_535]: (m1_pre_topc(D_532, B_533) | ~m1_pre_topc(C_534, A_535) | g1_pre_topc(u1_struct_0(D_532), u1_pre_topc(D_532))!=g1_pre_topc(u1_struct_0(C_534), u1_pre_topc(C_534)) | g1_pre_topc(u1_struct_0(B_533), u1_pre_topc(B_533))!=g1_pre_topc(u1_struct_0(A_535), u1_pre_topc(A_535)) | ~l1_pre_topc(D_532) | ~l1_pre_topc(C_534) | ~l1_pre_topc(B_533) | ~l1_pre_topc(A_535))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.26/1.92  tff(c_1451, plain, (![D_532, B_533, A_35]: (m1_pre_topc(D_532, B_533) | g1_pre_topc(u1_struct_0(D_532), u1_pre_topc(D_532))!=g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35)) | g1_pre_topc(u1_struct_0(B_533), u1_pre_topc(B_533))!=g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35)) | ~l1_pre_topc(D_532) | ~l1_pre_topc(B_533) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_28, c_1419])).
% 5.26/1.92  tff(c_2307, plain, (![A_607, B_608]: (m1_pre_topc(A_607, B_608) | g1_pre_topc(u1_struct_0(B_608), u1_pre_topc(B_608))!=g1_pre_topc(u1_struct_0(A_607), u1_pre_topc(A_607)) | ~l1_pre_topc(A_607) | ~l1_pre_topc(B_608) | ~l1_pre_topc(A_607))), inference(reflexivity, [status(thm), theory('equality')], [c_1451])).
% 5.26/1.92  tff(c_2313, plain, (![A_607]: (m1_pre_topc(A_607, '#skF_4') | g1_pre_topc(u1_struct_0(A_607), u1_pre_topc(A_607))!='#skF_5' | ~l1_pre_topc(A_607) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_607))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2307])).
% 5.26/1.92  tff(c_2320, plain, (![A_609]: (m1_pre_topc(A_609, '#skF_4') | g1_pre_topc(u1_struct_0(A_609), u1_pre_topc(A_609))!='#skF_5' | ~l1_pre_topc(A_609))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_2313])).
% 5.26/1.92  tff(c_2331, plain, (![A_610]: (m1_pre_topc(A_610, '#skF_4') | A_610!='#skF_5' | ~l1_pre_topc(A_610) | ~v1_pre_topc(A_610) | ~l1_pre_topc(A_610))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2320])).
% 5.26/1.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.26/1.92  tff(c_331, plain, (![B_458, C_459, A_460]: (m1_pre_topc(B_458, C_459) | ~r1_tarski(u1_struct_0(B_458), u1_struct_0(C_459)) | ~m1_pre_topc(C_459, A_460) | ~m1_pre_topc(B_458, A_460) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.26/1.92  tff(c_389, plain, (![B_463, A_464]: (m1_pre_topc(B_463, B_463) | ~m1_pre_topc(B_463, A_464) | ~l1_pre_topc(A_464) | ~v2_pre_topc(A_464))), inference(resolution, [status(thm)], [c_6, c_331])).
% 5.26/1.92  tff(c_397, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_389])).
% 5.26/1.92  tff(c_407, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_397])).
% 5.26/1.92  tff(c_696, plain, (![D_476, B_477, C_478, A_479]: (m1_pre_topc(D_476, B_477) | ~m1_pre_topc(C_478, A_479) | g1_pre_topc(u1_struct_0(D_476), u1_pre_topc(D_476))!=g1_pre_topc(u1_struct_0(C_478), u1_pre_topc(C_478)) | g1_pre_topc(u1_struct_0(B_477), u1_pre_topc(B_477))!=g1_pre_topc(u1_struct_0(A_479), u1_pre_topc(A_479)) | ~l1_pre_topc(D_476) | ~l1_pre_topc(C_478) | ~l1_pre_topc(B_477) | ~l1_pre_topc(A_479))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.26/1.92  tff(c_700, plain, (![D_476, B_477]: (m1_pre_topc(D_476, B_477) | g1_pre_topc(u1_struct_0(D_476), u1_pre_topc(D_476))!=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | g1_pre_topc(u1_struct_0(B_477), u1_pre_topc(B_477))!=g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4')) | ~l1_pre_topc(D_476) | ~l1_pre_topc(B_477) | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_407, c_696])).
% 5.26/1.92  tff(c_922, plain, (![D_505, B_506]: (m1_pre_topc(D_505, B_506) | g1_pre_topc(u1_struct_0(D_505), u1_pre_topc(D_505))!='#skF_5' | g1_pre_topc(u1_struct_0(B_506), u1_pre_topc(B_506))!='#skF_5' | ~l1_pre_topc(D_505) | ~l1_pre_topc(B_506))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_50, c_50, c_700])).
% 5.26/1.92  tff(c_926, plain, (![B_506]: (m1_pre_topc('#skF_4', B_506) | g1_pre_topc(u1_struct_0(B_506), u1_pre_topc(B_506))!='#skF_5' | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(B_506))), inference(superposition, [status(thm), theory('equality')], [c_50, c_922])).
% 5.26/1.92  tff(c_937, plain, (![B_514]: (m1_pre_topc('#skF_4', B_514) | g1_pre_topc(u1_struct_0(B_514), u1_pre_topc(B_514))!='#skF_5' | ~l1_pre_topc(B_514))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_926])).
% 5.26/1.92  tff(c_948, plain, (![A_515]: (m1_pre_topc('#skF_4', A_515) | A_515!='#skF_5' | ~l1_pre_topc(A_515) | ~v1_pre_topc(A_515) | ~l1_pre_topc(A_515))), inference(superposition, [status(thm), theory('equality')], [c_12, c_937])).
% 5.26/1.92  tff(c_184, plain, (![C_440, A_441, B_442]: (m1_pre_topc(C_440, A_441) | ~m1_pre_topc(C_440, B_442) | ~m1_pre_topc(B_442, A_441) | ~l1_pre_topc(A_441) | ~v2_pre_topc(A_441))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.26/1.92  tff(c_193, plain, (![A_441]: (m1_pre_topc('#skF_5', A_441) | ~m1_pre_topc('#skF_2', A_441) | ~l1_pre_topc(A_441) | ~v2_pre_topc(A_441))), inference(resolution, [status(thm)], [c_58, c_184])).
% 5.26/1.92  tff(c_237, plain, (![B_449, C_450, A_451]: (r1_tarski(u1_struct_0(B_449), u1_struct_0(C_450)) | ~m1_pre_topc(B_449, C_450) | ~m1_pre_topc(C_450, A_451) | ~m1_pre_topc(B_449, A_451) | ~l1_pre_topc(A_451) | ~v2_pre_topc(A_451))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.26/1.92  tff(c_266, plain, (![B_456, A_457]: (r1_tarski(u1_struct_0(B_456), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_456, '#skF_5') | ~m1_pre_topc(B_456, A_457) | ~m1_pre_topc('#skF_2', A_457) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457))), inference(resolution, [status(thm)], [c_193, c_237])).
% 5.26/1.92  tff(c_272, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_266])).
% 5.26/1.92  tff(c_280, plain, (r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_272])).
% 5.26/1.92  tff(c_284, plain, (~m1_pre_topc('#skF_2', '#skF_2')), inference(splitLeft, [status(thm)], [c_280])).
% 5.26/1.92  tff(c_287, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_28, c_284])).
% 5.26/1.92  tff(c_291, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_287])).
% 5.26/1.92  tff(c_292, plain, (~m1_pre_topc('#skF_4', '#skF_5') | r1_tarski(u1_struct_0('#skF_4'), u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_280])).
% 5.26/1.92  tff(c_330, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_292])).
% 5.26/1.92  tff(c_969, plain, (~v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_948, c_330])).
% 5.26/1.92  tff(c_1005, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_150, c_969])).
% 5.26/1.92  tff(c_1007, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_292])).
% 5.26/1.92  tff(c_243, plain, (![B_449]: (r1_tarski(u1_struct_0(B_449), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_449, '#skF_4') | ~m1_pre_topc(B_449, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_62, c_237])).
% 5.26/1.92  tff(c_250, plain, (![B_449]: (r1_tarski(u1_struct_0(B_449), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_449, '#skF_4') | ~m1_pre_topc(B_449, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_243])).
% 5.26/1.92  tff(c_245, plain, (![B_449]: (r1_tarski(u1_struct_0(B_449), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_449, '#skF_5') | ~m1_pre_topc(B_449, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_58, c_237])).
% 5.26/1.92  tff(c_258, plain, (![B_453]: (r1_tarski(u1_struct_0(B_453), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_453, '#skF_5') | ~m1_pre_topc(B_453, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_245])).
% 5.26/1.92  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.26/1.92  tff(c_1038, plain, (![B_516]: (u1_struct_0(B_516)=u1_struct_0('#skF_5') | ~r1_tarski(u1_struct_0('#skF_5'), u1_struct_0(B_516)) | ~m1_pre_topc(B_516, '#skF_5') | ~m1_pre_topc(B_516, '#skF_2'))), inference(resolution, [status(thm)], [c_258, c_2])).
% 5.26/1.92  tff(c_1050, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_250, c_1038])).
% 5.26/1.92  tff(c_1062, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_62, c_1007, c_1050])).
% 5.26/1.92  tff(c_1071, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1062])).
% 5.26/1.92  tff(c_2360, plain, (~v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_2331, c_1071])).
% 5.26/1.92  tff(c_2407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_150, c_2360])).
% 5.26/1.92  tff(c_2408, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_1062])).
% 5.26/1.92  tff(c_26, plain, (![A_32, B_33]: (m1_connsp_2('#skF_1'(A_32, B_33), A_32, B_33) | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.26/1.92  tff(c_2579, plain, (![C_616, A_617, B_618]: (m1_subset_1(C_616, k1_zfmisc_1(u1_struct_0(A_617))) | ~m1_connsp_2(C_616, A_617, B_618) | ~m1_subset_1(B_618, u1_struct_0(A_617)) | ~l1_pre_topc(A_617) | ~v2_pre_topc(A_617) | v2_struct_0(A_617))), inference(cnfTransformation, [status(thm)], [f_100])).
% 5.26/1.92  tff(c_3232, plain, (![A_658, B_659]: (m1_subset_1('#skF_1'(A_658, B_659), k1_zfmisc_1(u1_struct_0(A_658))) | ~m1_subset_1(B_659, u1_struct_0(A_658)) | ~l1_pre_topc(A_658) | ~v2_pre_topc(A_658) | v2_struct_0(A_658))), inference(resolution, [status(thm)], [c_26, c_2579])).
% 5.26/1.92  tff(c_3238, plain, (![B_659]: (m1_subset_1('#skF_1'('#skF_5', B_659), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_659, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2408, c_3232])).
% 5.26/1.92  tff(c_3241, plain, (![B_659]: (m1_subset_1('#skF_1'('#skF_5', B_659), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_659, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_116, c_2408, c_3238])).
% 5.26/1.92  tff(c_3243, plain, (![B_660]: (m1_subset_1('#skF_1'('#skF_5', B_660), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_660, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_3241])).
% 5.26/1.92  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.26/1.92  tff(c_3248, plain, (![B_661]: (r1_tarski('#skF_1'('#skF_5', B_661), u1_struct_0('#skF_4')) | ~m1_subset_1(B_661, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3243, c_8])).
% 5.26/1.92  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.26/1.92  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_44, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_40, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_78, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40])).
% 5.26/1.92  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_54, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_2482, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_54])).
% 5.26/1.92  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_2481, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2408, c_52])).
% 5.26/1.92  tff(c_42, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_246])).
% 5.26/1.92  tff(c_3159, plain, (![D_652, F_648, B_651, C_650, E_649, H_647, A_646]: (r1_tmap_1(D_652, B_651, E_649, H_647) | ~r1_tmap_1(C_650, B_651, k3_tmap_1(A_646, B_651, D_652, C_650, E_649), H_647) | ~m1_connsp_2(F_648, D_652, H_647) | ~r1_tarski(F_648, u1_struct_0(C_650)) | ~m1_subset_1(H_647, u1_struct_0(C_650)) | ~m1_subset_1(H_647, u1_struct_0(D_652)) | ~m1_subset_1(F_648, k1_zfmisc_1(u1_struct_0(D_652))) | ~m1_pre_topc(C_650, D_652) | ~m1_subset_1(E_649, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_652), u1_struct_0(B_651)))) | ~v1_funct_2(E_649, u1_struct_0(D_652), u1_struct_0(B_651)) | ~v1_funct_1(E_649) | ~m1_pre_topc(D_652, A_646) | v2_struct_0(D_652) | ~m1_pre_topc(C_650, A_646) | v2_struct_0(C_650) | ~l1_pre_topc(B_651) | ~v2_pre_topc(B_651) | v2_struct_0(B_651) | ~l1_pre_topc(A_646) | ~v2_pre_topc(A_646) | v2_struct_0(A_646))), inference(cnfTransformation, [status(thm)], [f_197])).
% 5.26/1.92  tff(c_3161, plain, (![F_648]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_648, '#skF_5', '#skF_8') | ~r1_tarski(F_648, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_648, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_3159])).
% 5.26/1.92  tff(c_3164, plain, (![F_648]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_648, '#skF_5', '#skF_8') | ~r1_tarski(F_648, u1_struct_0('#skF_4')) | ~m1_subset_1(F_648, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_2482, c_2408, c_2481, c_2408, c_1007, c_2408, c_46, c_2408, c_46, c_3161])).
% 5.26/1.92  tff(c_3166, plain, (![F_653]: (~m1_connsp_2(F_653, '#skF_5', '#skF_8') | ~r1_tarski(F_653, u1_struct_0('#skF_4')) | ~m1_subset_1(F_653, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_78, c_3164])).
% 5.26/1.92  tff(c_3171, plain, (![A_3]: (~m1_connsp_2(A_3, '#skF_5', '#skF_8') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_3166])).
% 5.26/1.92  tff(c_3256, plain, (![B_662]: (~m1_connsp_2('#skF_1'('#skF_5', B_662), '#skF_5', '#skF_8') | ~m1_subset_1(B_662, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_3248, c_3171])).
% 5.26/1.92  tff(c_3260, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_26, c_3256])).
% 5.26/1.92  tff(c_3263, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_116, c_46, c_2408, c_46, c_3260])).
% 5.26/1.92  tff(c_3265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_3263])).
% 5.26/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/1.92  
% 5.26/1.92  Inference rules
% 5.26/1.92  ----------------------
% 5.26/1.92  #Ref     : 15
% 5.26/1.92  #Sup     : 581
% 5.26/1.92  #Fact    : 0
% 5.26/1.92  #Define  : 0
% 5.26/1.92  #Split   : 15
% 5.26/1.92  #Chain   : 0
% 5.26/1.92  #Close   : 0
% 5.26/1.92  
% 5.26/1.92  Ordering : KBO
% 5.26/1.92  
% 5.26/1.92  Simplification rules
% 5.26/1.92  ----------------------
% 5.26/1.92  #Subsume      : 201
% 5.26/1.92  #Demod        : 970
% 5.26/1.92  #Tautology    : 210
% 5.26/1.92  #SimpNegUnit  : 12
% 5.26/1.92  #BackRed      : 11
% 5.26/1.92  
% 5.26/1.92  #Partial instantiations: 0
% 5.26/1.92  #Strategies tried      : 1
% 5.26/1.92  
% 5.26/1.92  Timing (in seconds)
% 5.26/1.92  ----------------------
% 5.26/1.92  Preprocessing        : 0.39
% 5.26/1.92  Parsing              : 0.20
% 5.26/1.92  CNF conversion       : 0.06
% 5.26/1.92  Main loop            : 0.75
% 5.26/1.92  Inferencing          : 0.26
% 5.26/1.92  Reduction            : 0.25
% 5.26/1.92  Demodulation         : 0.18
% 5.26/1.92  BG Simplification    : 0.03
% 5.26/1.92  Subsumption          : 0.16
% 5.26/1.92  Abstraction          : 0.03
% 5.26/1.92  MUC search           : 0.00
% 5.26/1.92  Cooper               : 0.00
% 5.26/1.92  Total                : 1.18
% 5.26/1.92  Index Insertion      : 0.00
% 5.26/1.92  Index Deletion       : 0.00
% 5.26/1.92  Index Matching       : 0.00
% 5.26/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
