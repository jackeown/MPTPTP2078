%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:35 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 513 expanded)
%              Number of leaves         :   42 ( 199 expanded)
%              Depth                    :   15
%              Number of atoms          :  288 (2966 expanded)
%              Number of equality atoms :   25 ( 389 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(f_252,negated_conjecture,(
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

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_88,axiom,(
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

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_121,axiom,(
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

tff(f_203,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_111,plain,(
    ! [B_424,A_425] :
      ( v2_pre_topc(B_424)
      | ~ m1_pre_topc(B_424,A_425)
      | ~ l1_pre_topc(A_425)
      | ~ v2_pre_topc(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_117,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_111])).

tff(c_123,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_117])).

tff(c_84,plain,(
    ! [B_419,A_420] :
      ( l1_pre_topc(B_419)
      | ~ m1_pre_topc(B_419,A_420)
      | ~ l1_pre_topc(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_90,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_84])).

tff(c_96,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_90])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_87,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_84])).

tff(c_93,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_87])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_125,plain,(
    ! [A_427] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_427),u1_pre_topc(A_427)))
      | ~ l1_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_128,plain,
    ( v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_125])).

tff(c_130,plain,
    ( v1_pre_topc('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_128])).

tff(c_131,plain,(
    v1_pre_topc('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_130])).

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

tff(c_169,plain,(
    ! [C_430,A_431,D_432,B_433] :
      ( C_430 = A_431
      | g1_pre_topc(C_430,D_432) != g1_pre_topc(A_431,B_433)
      | ~ m1_subset_1(B_433,k1_zfmisc_1(k1_zfmisc_1(A_431))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_177,plain,(
    ! [C_430,D_432] :
      ( u1_struct_0('#skF_4') = C_430
      | g1_pre_topc(C_430,D_432) != '#skF_5'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_169])).

tff(c_188,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_191,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_198,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_191])).

tff(c_201,plain,(
    ! [C_436,D_437] :
      ( u1_struct_0('#skF_4') = C_436
      | g1_pre_topc(C_436,D_437) != '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_215,plain,(
    ! [A_438] :
      ( u1_struct_0(A_438) = u1_struct_0('#skF_4')
      | A_438 != '#skF_5'
      | ~ v1_pre_topc(A_438)
      | ~ l1_pre_topc(A_438) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_201])).

tff(c_218,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_215])).

tff(c_224,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_218])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( m1_connsp_2('#skF_1'(A_22,B_23),A_22,B_23)
      | ~ m1_subset_1(B_23,u1_struct_0(A_22))
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_500,plain,(
    ! [C_473,A_474,B_475] :
      ( m1_subset_1(C_473,k1_zfmisc_1(u1_struct_0(A_474)))
      | ~ m1_connsp_2(C_473,A_474,B_475)
      | ~ m1_subset_1(B_475,u1_struct_0(A_474))
      | ~ l1_pre_topc(A_474)
      | ~ v2_pre_topc(A_474)
      | v2_struct_0(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_504,plain,(
    ! [A_476,B_477] :
      ( m1_subset_1('#skF_1'(A_476,B_477),k1_zfmisc_1(u1_struct_0(A_476)))
      | ~ m1_subset_1(B_477,u1_struct_0(A_476))
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(resolution,[status(thm)],[c_24,c_500])).

tff(c_510,plain,(
    ! [B_477] :
      ( m1_subset_1('#skF_1'('#skF_5',B_477),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_477,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_504])).

tff(c_513,plain,(
    ! [B_477] :
      ( m1_subset_1('#skF_1'('#skF_5',B_477),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_477,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_96,c_224,c_510])).

tff(c_515,plain,(
    ! [B_478] :
      ( m1_subset_1('#skF_1'('#skF_5',B_478),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_478,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_513])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_519,plain,(
    ! [B_478] :
      ( r1_tarski('#skF_1'('#skF_5',B_478),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_478,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_515,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_40,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_36,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_74,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_50,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_243,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_242,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_48])).

tff(c_541,plain,(
    ! [A_484,B_485] :
      ( k1_tsep_1(A_484,B_485,B_485) = g1_pre_topc(u1_struct_0(B_485),u1_pre_topc(B_485))
      | ~ m1_pre_topc(B_485,A_484)
      | v2_struct_0(B_485)
      | ~ l1_pre_topc(A_484)
      | ~ v2_pre_topc(A_484)
      | v2_struct_0(A_484) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_545,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k1_tsep_1('#skF_2','#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_541])).

tff(c_553,plain,
    ( k1_tsep_1('#skF_2','#skF_4','#skF_4') = '#skF_5'
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_46,c_545])).

tff(c_554,plain,(
    k1_tsep_1('#skF_2','#skF_4','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60,c_553])).

tff(c_567,plain,(
    ! [B_486,A_487,C_488] :
      ( m1_pre_topc(B_486,k1_tsep_1(A_487,B_486,C_488))
      | ~ m1_pre_topc(C_488,A_487)
      | v2_struct_0(C_488)
      | ~ m1_pre_topc(B_486,A_487)
      | v2_struct_0(B_486)
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_589,plain,
    ( m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_567])).

tff(c_602,plain,
    ( m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_58,c_58,c_589])).

tff(c_603,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60,c_602])).

tff(c_38,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_754,plain,(
    ! [C_497,E_498,F_493,B_496,D_494,A_495,H_499] :
      ( r1_tmap_1(D_494,B_496,E_498,H_499)
      | ~ r1_tmap_1(C_497,B_496,k3_tmap_1(A_495,B_496,D_494,C_497,E_498),H_499)
      | ~ m1_connsp_2(F_493,D_494,H_499)
      | ~ r1_tarski(F_493,u1_struct_0(C_497))
      | ~ m1_subset_1(H_499,u1_struct_0(C_497))
      | ~ m1_subset_1(H_499,u1_struct_0(D_494))
      | ~ m1_subset_1(F_493,k1_zfmisc_1(u1_struct_0(D_494)))
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
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_756,plain,(
    ! [F_493] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_493,'#skF_5','#skF_8')
      | ~ r1_tarski(F_493,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_493,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_38,c_754])).

tff(c_759,plain,(
    ! [F_493] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_493,'#skF_5','#skF_8')
      | ~ r1_tarski(F_493,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_493,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_243,c_224,c_242,c_224,c_603,c_224,c_42,c_224,c_42,c_756])).

tff(c_761,plain,(
    ! [F_500] :
      ( ~ m1_connsp_2(F_500,'#skF_5','#skF_8')
      | ~ r1_tarski(F_500,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_500,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_74,c_759])).

tff(c_779,plain,(
    ! [A_501] :
      ( ~ m1_connsp_2(A_501,'#skF_5','#skF_8')
      | ~ r1_tarski(A_501,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_761])).

tff(c_793,plain,(
    ! [B_503] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_503),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_503,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_519,c_779])).

tff(c_797,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_793])).

tff(c_800,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_96,c_42,c_224,c_42,c_797])).

tff(c_802,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_800])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.37/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.55  
% 3.47/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.55  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.47/1.55  
% 3.47/1.55  %Foreground sorts:
% 3.47/1.55  
% 3.47/1.55  
% 3.47/1.55  %Background operators:
% 3.47/1.55  
% 3.47/1.55  
% 3.47/1.55  %Foreground operators:
% 3.47/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.47/1.55  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.47/1.55  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.47/1.55  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.47/1.55  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.47/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.55  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.47/1.55  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.47/1.55  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.47/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.47/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.47/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.55  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.47/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.47/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.55  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.47/1.55  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.47/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.47/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.55  
% 3.47/1.57  tff(f_252, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.47/1.57  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.47/1.57  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.47/1.57  tff(f_65, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 3.47/1.57  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 3.47/1.57  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 3.47/1.57  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 3.47/1.57  tff(f_100, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.47/1.57  tff(f_88, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.47/1.57  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.47/1.57  tff(f_136, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 3.47/1.57  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 3.47/1.57  tff(f_203, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.47/1.57  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_111, plain, (![B_424, A_425]: (v2_pre_topc(B_424) | ~m1_pre_topc(B_424, A_425) | ~l1_pre_topc(A_425) | ~v2_pre_topc(A_425))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.47/1.57  tff(c_117, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_111])).
% 3.47/1.57  tff(c_123, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_117])).
% 3.47/1.57  tff(c_84, plain, (![B_419, A_420]: (l1_pre_topc(B_419) | ~m1_pre_topc(B_419, A_420) | ~l1_pre_topc(A_420))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.47/1.57  tff(c_90, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_84])).
% 3.47/1.57  tff(c_96, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_90])).
% 3.47/1.57  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_87, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_84])).
% 3.47/1.57  tff(c_93, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_87])).
% 3.47/1.57  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_125, plain, (![A_427]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_427), u1_pre_topc(A_427))) | ~l1_pre_topc(A_427) | v2_struct_0(A_427))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.47/1.57  tff(c_128, plain, (v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_46, c_125])).
% 3.47/1.57  tff(c_130, plain, (v1_pre_topc('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_128])).
% 3.47/1.57  tff(c_131, plain, (v1_pre_topc('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_130])).
% 3.47/1.57  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.47/1.57  tff(c_12, plain, (![A_10]: (m1_subset_1(u1_pre_topc(A_10), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.47/1.57  tff(c_169, plain, (![C_430, A_431, D_432, B_433]: (C_430=A_431 | g1_pre_topc(C_430, D_432)!=g1_pre_topc(A_431, B_433) | ~m1_subset_1(B_433, k1_zfmisc_1(k1_zfmisc_1(A_431))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.47/1.57  tff(c_177, plain, (![C_430, D_432]: (u1_struct_0('#skF_4')=C_430 | g1_pre_topc(C_430, D_432)!='#skF_5' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_46, c_169])).
% 3.47/1.57  tff(c_188, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_177])).
% 3.47/1.57  tff(c_191, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_188])).
% 3.47/1.57  tff(c_198, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_191])).
% 3.47/1.57  tff(c_201, plain, (![C_436, D_437]: (u1_struct_0('#skF_4')=C_436 | g1_pre_topc(C_436, D_437)!='#skF_5')), inference(splitRight, [status(thm)], [c_177])).
% 3.47/1.57  tff(c_215, plain, (![A_438]: (u1_struct_0(A_438)=u1_struct_0('#skF_4') | A_438!='#skF_5' | ~v1_pre_topc(A_438) | ~l1_pre_topc(A_438))), inference(superposition, [status(thm), theory('equality')], [c_6, c_201])).
% 3.47/1.57  tff(c_218, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_131, c_215])).
% 3.47/1.57  tff(c_224, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_218])).
% 3.47/1.57  tff(c_24, plain, (![A_22, B_23]: (m1_connsp_2('#skF_1'(A_22, B_23), A_22, B_23) | ~m1_subset_1(B_23, u1_struct_0(A_22)) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.47/1.57  tff(c_500, plain, (![C_473, A_474, B_475]: (m1_subset_1(C_473, k1_zfmisc_1(u1_struct_0(A_474))) | ~m1_connsp_2(C_473, A_474, B_475) | ~m1_subset_1(B_475, u1_struct_0(A_474)) | ~l1_pre_topc(A_474) | ~v2_pre_topc(A_474) | v2_struct_0(A_474))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.47/1.57  tff(c_504, plain, (![A_476, B_477]: (m1_subset_1('#skF_1'(A_476, B_477), k1_zfmisc_1(u1_struct_0(A_476))) | ~m1_subset_1(B_477, u1_struct_0(A_476)) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(resolution, [status(thm)], [c_24, c_500])).
% 3.47/1.57  tff(c_510, plain, (![B_477]: (m1_subset_1('#skF_1'('#skF_5', B_477), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_477, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_224, c_504])).
% 3.47/1.57  tff(c_513, plain, (![B_477]: (m1_subset_1('#skF_1'('#skF_5', B_477), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_477, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_96, c_224, c_510])).
% 3.47/1.57  tff(c_515, plain, (![B_478]: (m1_subset_1('#skF_1'('#skF_5', B_478), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_478, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_513])).
% 3.47/1.57  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.47/1.57  tff(c_519, plain, (![B_478]: (r1_tarski('#skF_1'('#skF_5', B_478), u1_struct_0('#skF_4')) | ~m1_subset_1(B_478, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_515, c_2])).
% 3.47/1.57  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.47/1.57  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_40, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_36, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_74, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 3.47/1.57  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_50, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_243, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_50])).
% 3.47/1.57  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_242, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_224, c_48])).
% 3.47/1.57  tff(c_541, plain, (![A_484, B_485]: (k1_tsep_1(A_484, B_485, B_485)=g1_pre_topc(u1_struct_0(B_485), u1_pre_topc(B_485)) | ~m1_pre_topc(B_485, A_484) | v2_struct_0(B_485) | ~l1_pre_topc(A_484) | ~v2_pre_topc(A_484) | v2_struct_0(A_484))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.47/1.57  tff(c_545, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k1_tsep_1('#skF_2', '#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_58, c_541])).
% 3.47/1.57  tff(c_553, plain, (k1_tsep_1('#skF_2', '#skF_4', '#skF_4')='#skF_5' | v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_46, c_545])).
% 3.47/1.57  tff(c_554, plain, (k1_tsep_1('#skF_2', '#skF_4', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_72, c_60, c_553])).
% 3.47/1.57  tff(c_567, plain, (![B_486, A_487, C_488]: (m1_pre_topc(B_486, k1_tsep_1(A_487, B_486, C_488)) | ~m1_pre_topc(C_488, A_487) | v2_struct_0(C_488) | ~m1_pre_topc(B_486, A_487) | v2_struct_0(B_486) | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.47/1.57  tff(c_589, plain, (m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_554, c_567])).
% 3.47/1.57  tff(c_602, plain, (m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_58, c_58, c_589])).
% 3.47/1.57  tff(c_603, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_72, c_60, c_602])).
% 3.47/1.57  tff(c_38, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_252])).
% 3.47/1.57  tff(c_754, plain, (![C_497, E_498, F_493, B_496, D_494, A_495, H_499]: (r1_tmap_1(D_494, B_496, E_498, H_499) | ~r1_tmap_1(C_497, B_496, k3_tmap_1(A_495, B_496, D_494, C_497, E_498), H_499) | ~m1_connsp_2(F_493, D_494, H_499) | ~r1_tarski(F_493, u1_struct_0(C_497)) | ~m1_subset_1(H_499, u1_struct_0(C_497)) | ~m1_subset_1(H_499, u1_struct_0(D_494)) | ~m1_subset_1(F_493, k1_zfmisc_1(u1_struct_0(D_494))) | ~m1_pre_topc(C_497, D_494) | ~m1_subset_1(E_498, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_494), u1_struct_0(B_496)))) | ~v1_funct_2(E_498, u1_struct_0(D_494), u1_struct_0(B_496)) | ~v1_funct_1(E_498) | ~m1_pre_topc(D_494, A_495) | v2_struct_0(D_494) | ~m1_pre_topc(C_497, A_495) | v2_struct_0(C_497) | ~l1_pre_topc(B_496) | ~v2_pre_topc(B_496) | v2_struct_0(B_496) | ~l1_pre_topc(A_495) | ~v2_pre_topc(A_495) | v2_struct_0(A_495))), inference(cnfTransformation, [status(thm)], [f_203])).
% 3.47/1.57  tff(c_756, plain, (![F_493]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_493, '#skF_5', '#skF_8') | ~r1_tarski(F_493, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_493, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_754])).
% 3.47/1.57  tff(c_759, plain, (![F_493]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_493, '#skF_5', '#skF_8') | ~r1_tarski(F_493, u1_struct_0('#skF_4')) | ~m1_subset_1(F_493, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_243, c_224, c_242, c_224, c_603, c_224, c_42, c_224, c_42, c_756])).
% 3.47/1.57  tff(c_761, plain, (![F_500]: (~m1_connsp_2(F_500, '#skF_5', '#skF_8') | ~r1_tarski(F_500, u1_struct_0('#skF_4')) | ~m1_subset_1(F_500, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_74, c_759])).
% 3.47/1.57  tff(c_779, plain, (![A_501]: (~m1_connsp_2(A_501, '#skF_5', '#skF_8') | ~r1_tarski(A_501, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_761])).
% 3.47/1.57  tff(c_793, plain, (![B_503]: (~m1_connsp_2('#skF_1'('#skF_5', B_503), '#skF_5', '#skF_8') | ~m1_subset_1(B_503, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_519, c_779])).
% 3.47/1.57  tff(c_797, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_793])).
% 3.47/1.57  tff(c_800, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_96, c_42, c_224, c_42, c_797])).
% 3.47/1.57  tff(c_802, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_800])).
% 3.47/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.57  
% 3.47/1.57  Inference rules
% 3.47/1.57  ----------------------
% 3.47/1.57  #Ref     : 6
% 3.47/1.57  #Sup     : 147
% 3.47/1.57  #Fact    : 0
% 3.47/1.57  #Define  : 0
% 3.47/1.57  #Split   : 2
% 3.47/1.57  #Chain   : 0
% 3.47/1.58  #Close   : 0
% 3.47/1.58  
% 3.47/1.58  Ordering : KBO
% 3.47/1.58  
% 3.47/1.58  Simplification rules
% 3.47/1.58  ----------------------
% 3.47/1.58  #Subsume      : 23
% 3.47/1.58  #Demod        : 245
% 3.47/1.58  #Tautology    : 69
% 3.47/1.58  #SimpNegUnit  : 27
% 3.47/1.58  #BackRed      : 8
% 3.47/1.58  
% 3.47/1.58  #Partial instantiations: 0
% 3.47/1.58  #Strategies tried      : 1
% 3.47/1.58  
% 3.47/1.58  Timing (in seconds)
% 3.47/1.58  ----------------------
% 3.47/1.58  Preprocessing        : 0.39
% 3.47/1.58  Parsing              : 0.19
% 3.47/1.58  CNF conversion       : 0.06
% 3.47/1.58  Main loop            : 0.36
% 3.47/1.58  Inferencing          : 0.12
% 3.47/1.58  Reduction            : 0.12
% 3.47/1.58  Demodulation         : 0.09
% 3.47/1.58  BG Simplification    : 0.02
% 3.47/1.58  Subsumption          : 0.07
% 3.47/1.58  Abstraction          : 0.02
% 3.47/1.58  MUC search           : 0.00
% 3.47/1.58  Cooper               : 0.00
% 3.47/1.58  Total                : 0.79
% 3.47/1.58  Index Insertion      : 0.00
% 3.47/1.58  Index Deletion       : 0.00
% 3.47/1.58  Index Matching       : 0.00
% 3.47/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
