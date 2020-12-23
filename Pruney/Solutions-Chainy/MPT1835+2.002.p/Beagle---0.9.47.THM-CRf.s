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
% DateTime   : Thu Dec  3 10:28:12 EST 2020

% Result     : Theorem 8.83s
% Output     : CNFRefutation 9.05s
% Verified   : 
% Statistics : Number of formulae       :  169 (1021 expanded)
%              Number of leaves         :   31 ( 382 expanded)
%              Depth                    :   15
%              Number of atoms          :  761 (10640 expanded)
%              Number of equality atoms :   14 ( 473 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k10_tmap_1,type,(
    k10_tmap_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r4_tsep_1,type,(
    r4_tsep_1: ( $i * $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_239,negated_conjecture,(
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
                   => ( A = k1_tsep_1(A,C,D)
                     => ! [E] :
                          ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(E,C,B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                         => ! [F] :
                              ( ( v1_funct_1(F)
                                & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                                & v5_pre_topc(F,D,B)
                                & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                             => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,k10_tmap_1(A,B,C,D,E,F)),E)
                                  & r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,k10_tmap_1(A,B,C,D,E,F)),F)
                                  & r4_tsep_1(A,C,D) )
                               => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                  & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(A),u1_struct_0(B))
                                  & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),A,B)
                                  & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_tmap_1)).

tff(f_83,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A)
        & ~ v2_struct_0(D)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
        & v1_funct_1(F)
        & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
     => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
        & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
        & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_177,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_113,axiom,(
    ! [A,B,C,D,E] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v2_pre_topc(B)
        & l1_pre_topc(B)
        & m1_pre_topc(C,A)
        & m1_pre_topc(D,A)
        & v1_funct_1(E)
        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
     => ( v1_funct_1(k3_tmap_1(A,B,C,D,E))
        & v1_funct_2(k3_tmap_1(A,B,C,D,E),u1_struct_0(D),u1_struct_0(B))
        & m1_subset_1(k3_tmap_1(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_41,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_173,axiom,(
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
                 => ( r4_tsep_1(A,C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                       => ( ( v1_funct_1(E)
                            & v1_funct_2(E,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                            & v5_pre_topc(E,k1_tsep_1(A,C,D),B)
                            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                        <=> ( v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),u1_struct_0(C),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),C,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B))))
                            & v1_funct_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E))
                            & v1_funct_2(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),u1_struct_0(D),u1_struct_0(B))
                            & v5_pre_topc(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),D,B)
                            & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_tmap_1)).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_80,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_78,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_86,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_84,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_74,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_70,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_68,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_852,plain,(
    ! [A_296,F_293,E_297,C_295,B_294,D_292] :
      ( m1_subset_1(k10_tmap_1(A_296,B_294,C_295,D_292,E_297,F_293),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_296,C_295,D_292)),u1_struct_0(B_294))))
      | ~ m1_subset_1(F_293,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_292),u1_struct_0(B_294))))
      | ~ v1_funct_2(F_293,u1_struct_0(D_292),u1_struct_0(B_294))
      | ~ v1_funct_1(F_293)
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_295),u1_struct_0(B_294))))
      | ~ v1_funct_2(E_297,u1_struct_0(C_295),u1_struct_0(B_294))
      | ~ v1_funct_1(E_297)
      | ~ m1_pre_topc(D_292,A_296)
      | v2_struct_0(D_292)
      | ~ m1_pre_topc(C_295,A_296)
      | v2_struct_0(C_295)
      | ~ l1_pre_topc(B_294)
      | ~ v2_pre_topc(B_294)
      | v2_struct_0(B_294)
      | ~ l1_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | v2_struct_0(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_881,plain,(
    ! [B_294,E_297,F_293] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_294,'#skF_3','#skF_4',E_297,F_293),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_294))))
      | ~ m1_subset_1(F_293,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_294))))
      | ~ v1_funct_2(F_293,u1_struct_0('#skF_4'),u1_struct_0(B_294))
      | ~ v1_funct_1(F_293)
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_294))))
      | ~ v1_funct_2(E_297,u1_struct_0('#skF_3'),u1_struct_0(B_294))
      | ~ v1_funct_1(E_297)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_294)
      | ~ v2_pre_topc(B_294)
      | v2_struct_0(B_294)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_852])).

tff(c_901,plain,(
    ! [B_294,E_297,F_293] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_294,'#skF_3','#skF_4',E_297,F_293),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_294))))
      | ~ m1_subset_1(F_293,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_294))))
      | ~ v1_funct_2(F_293,u1_struct_0('#skF_4'),u1_struct_0(B_294))
      | ~ v1_funct_1(F_293)
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_294))))
      | ~ v1_funct_2(E_297,u1_struct_0('#skF_3'),u1_struct_0(B_294))
      | ~ v1_funct_1(E_297)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_294)
      | ~ v2_pre_topc(B_294)
      | v2_struct_0(B_294)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_881])).

tff(c_903,plain,(
    ! [B_298,E_299,F_300] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_298,'#skF_3','#skF_4',E_299,F_300),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_298))))
      | ~ m1_subset_1(F_300,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_298))))
      | ~ v1_funct_2(F_300,u1_struct_0('#skF_4'),u1_struct_0(B_298))
      | ~ v1_funct_1(F_300)
      | ~ m1_subset_1(E_299,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_298))))
      | ~ v1_funct_2(E_299,u1_struct_0('#skF_3'),u1_struct_0(B_298))
      | ~ v1_funct_1(E_299)
      | ~ l1_pre_topc(B_298)
      | ~ v2_pre_topc(B_298)
      | v2_struct_0(B_298) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_76,c_72,c_901])).

tff(c_171,plain,(
    ! [D_136,B_138,E_141,F_137,C_139,A_140] :
      ( v1_funct_1(k10_tmap_1(A_140,B_138,C_139,D_136,E_141,F_137))
      | ~ m1_subset_1(F_137,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_136),u1_struct_0(B_138))))
      | ~ v1_funct_2(F_137,u1_struct_0(D_136),u1_struct_0(B_138))
      | ~ v1_funct_1(F_137)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139),u1_struct_0(B_138))))
      | ~ v1_funct_2(E_141,u1_struct_0(C_139),u1_struct_0(B_138))
      | ~ v1_funct_1(E_141)
      | ~ m1_pre_topc(D_136,A_140)
      | v2_struct_0(D_136)
      | ~ m1_pre_topc(C_139,A_140)
      | v2_struct_0(C_139)
      | ~ l1_pre_topc(B_138)
      | ~ v2_pre_topc(B_138)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_175,plain,(
    ! [A_140,C_139,E_141] :
      ( v1_funct_1(k10_tmap_1(A_140,'#skF_2',C_139,'#skF_4',E_141,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_141,u1_struct_0(C_139),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_141)
      | ~ m1_pre_topc('#skF_4',A_140)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_139,A_140)
      | v2_struct_0(C_139)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(resolution,[status(thm)],[c_52,c_171])).

tff(c_181,plain,(
    ! [A_140,C_139,E_141] :
      ( v1_funct_1(k10_tmap_1(A_140,'#skF_2',C_139,'#skF_4',E_141,'#skF_6'))
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_141,u1_struct_0(C_139),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_141)
      | ~ m1_pre_topc('#skF_4',A_140)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_139,A_140)
      | v2_struct_0(C_139)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_140)
      | ~ v2_pre_topc(A_140)
      | v2_struct_0(A_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_58,c_56,c_175])).

tff(c_187,plain,(
    ! [A_142,C_143,E_144] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2',C_143,'#skF_4',E_144,'#skF_6'))
      | ~ m1_subset_1(E_144,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_144,u1_struct_0(C_143),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_144)
      | ~ m1_pre_topc('#skF_4',A_142)
      | ~ m1_pre_topc(C_143,A_142)
      | v2_struct_0(C_143)
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_72,c_181])).

tff(c_194,plain,(
    ! [A_142] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_142)
      | ~ m1_pre_topc('#skF_3',A_142)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(resolution,[status(thm)],[c_60,c_187])).

tff(c_205,plain,(
    ! [A_142] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_142)
      | ~ m1_pre_topc('#skF_3',A_142)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_194])).

tff(c_208,plain,(
    ! [A_146] :
      ( v1_funct_1(k10_tmap_1(A_146,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_146)
      | ~ m1_pre_topc('#skF_3',A_146)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_205])).

tff(c_44,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_144,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_211,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_208,c_144])).

tff(c_214,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_211])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_214])).

tff(c_217,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_220,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_942,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_903,c_220])).

tff(c_983,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_64,c_60,c_58,c_56,c_52,c_942])).

tff(c_985,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_983])).

tff(c_986,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_999,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_986])).

tff(c_1257,plain,(
    ! [A_397,C_396,B_395,D_393,E_398,F_394] :
      ( v1_funct_2(k10_tmap_1(A_397,B_395,C_396,D_393,E_398,F_394),u1_struct_0(k1_tsep_1(A_397,C_396,D_393)),u1_struct_0(B_395))
      | ~ m1_subset_1(F_394,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_393),u1_struct_0(B_395))))
      | ~ v1_funct_2(F_394,u1_struct_0(D_393),u1_struct_0(B_395))
      | ~ v1_funct_1(F_394)
      | ~ m1_subset_1(E_398,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396),u1_struct_0(B_395))))
      | ~ v1_funct_2(E_398,u1_struct_0(C_396),u1_struct_0(B_395))
      | ~ v1_funct_1(E_398)
      | ~ m1_pre_topc(D_393,A_397)
      | v2_struct_0(D_393)
      | ~ m1_pre_topc(C_396,A_397)
      | v2_struct_0(C_396)
      | ~ l1_pre_topc(B_395)
      | ~ v2_pre_topc(B_395)
      | v2_struct_0(B_395)
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1260,plain,(
    ! [B_395,E_398,F_394] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_395,'#skF_3','#skF_4',E_398,F_394),u1_struct_0('#skF_1'),u1_struct_0(B_395))
      | ~ m1_subset_1(F_394,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_395))))
      | ~ v1_funct_2(F_394,u1_struct_0('#skF_4'),u1_struct_0(B_395))
      | ~ v1_funct_1(F_394)
      | ~ m1_subset_1(E_398,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_395))))
      | ~ v1_funct_2(E_398,u1_struct_0('#skF_3'),u1_struct_0(B_395))
      | ~ v1_funct_1(E_398)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_395)
      | ~ v2_pre_topc(B_395)
      | v2_struct_0(B_395)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1257])).

tff(c_1262,plain,(
    ! [B_395,E_398,F_394] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_395,'#skF_3','#skF_4',E_398,F_394),u1_struct_0('#skF_1'),u1_struct_0(B_395))
      | ~ m1_subset_1(F_394,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_395))))
      | ~ v1_funct_2(F_394,u1_struct_0('#skF_4'),u1_struct_0(B_395))
      | ~ v1_funct_1(F_394)
      | ~ m1_subset_1(E_398,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_395))))
      | ~ v1_funct_2(E_398,u1_struct_0('#skF_3'),u1_struct_0(B_395))
      | ~ v1_funct_1(E_398)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_395)
      | ~ v2_pre_topc(B_395)
      | v2_struct_0(B_395)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_1260])).

tff(c_1275,plain,(
    ! [B_401,E_402,F_403] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_401,'#skF_3','#skF_4',E_402,F_403),u1_struct_0('#skF_1'),u1_struct_0(B_401))
      | ~ m1_subset_1(F_403,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_401))))
      | ~ v1_funct_2(F_403,u1_struct_0('#skF_4'),u1_struct_0(B_401))
      | ~ v1_funct_1(F_403)
      | ~ m1_subset_1(E_402,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_401))))
      | ~ v1_funct_2(E_402,u1_struct_0('#skF_3'),u1_struct_0(B_401))
      | ~ v1_funct_1(E_402)
      | ~ l1_pre_topc(B_401)
      | ~ v2_pre_topc(B_401)
      | v2_struct_0(B_401) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_76,c_72,c_1262])).

tff(c_1280,plain,(
    ! [E_402] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_402,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_402,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_402,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_402)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_1275])).

tff(c_1284,plain,(
    ! [E_402] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_402,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_402,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_402,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_402)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_58,c_56,c_1280])).

tff(c_1286,plain,(
    ! [E_404] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_404,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_404,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_404,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_404) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1284])).

tff(c_1293,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1286])).

tff(c_1300,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1293])).

tff(c_1302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_999,c_1300])).

tff(c_1303,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_986])).

tff(c_218,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1304,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_986])).

tff(c_987,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_42,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1310,plain,(
    ! [C_405,E_409,B_407,D_408,A_406] :
      ( v1_funct_2(k3_tmap_1(A_406,B_407,C_405,D_408,E_409),u1_struct_0(D_408),u1_struct_0(B_407))
      | ~ m1_subset_1(E_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_405),u1_struct_0(B_407))))
      | ~ v1_funct_2(E_409,u1_struct_0(C_405),u1_struct_0(B_407))
      | ~ v1_funct_1(E_409)
      | ~ m1_pre_topc(D_408,A_406)
      | ~ m1_pre_topc(C_405,A_406)
      | ~ l1_pre_topc(B_407)
      | ~ v2_pre_topc(B_407)
      | v2_struct_0(B_407)
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1312,plain,(
    ! [A_406,D_408] :
      ( v1_funct_2(k3_tmap_1(A_406,'#skF_2','#skF_1',D_408,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_408),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_408,A_406)
      | ~ m1_pre_topc('#skF_1',A_406)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(resolution,[status(thm)],[c_987,c_1310])).

tff(c_1319,plain,(
    ! [A_406,D_408] :
      ( v1_funct_2(k3_tmap_1(A_406,'#skF_2','#skF_1',D_408,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_408),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_408,A_406)
      | ~ m1_pre_topc('#skF_1',A_406)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_218,c_1304,c_1312])).

tff(c_1320,plain,(
    ! [A_406,D_408] :
      ( v1_funct_2(k3_tmap_1(A_406,'#skF_2','#skF_1',D_408,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_408),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_408,A_406)
      | ~ m1_pre_topc('#skF_1',A_406)
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1319])).

tff(c_16,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] :
      ( v1_funct_1(k3_tmap_1(A_11,B_12,C_13,D_14,E_15))
      | ~ m1_subset_1(E_15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13),u1_struct_0(B_12))))
      | ~ v1_funct_2(E_15,u1_struct_0(C_13),u1_struct_0(B_12))
      | ~ v1_funct_1(E_15)
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc(C_13,A_11)
      | ~ l1_pre_topc(B_12)
      | ~ v2_pre_topc(B_12)
      | v2_struct_0(B_12)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_989,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_1',D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_1',A_11)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_987,c_16])).

tff(c_994,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_1',D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_1',A_11)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_218,c_989])).

tff(c_995,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_1',D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_1',A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_994])).

tff(c_1305,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_995])).

tff(c_1307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1304,c_1305])).

tff(c_1308,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_1',D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_1',A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(splitRight,[status(thm)],[c_995])).

tff(c_50,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_89,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_50])).

tff(c_107,plain,(
    ! [D_109,C_110,A_111,B_112] :
      ( D_109 = C_110
      | ~ r2_funct_2(A_111,B_112,C_110,D_109)
      | ~ m1_subset_1(D_109,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_2(D_109,A_111,B_112)
      | ~ v1_funct_1(D_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_2(C_110,A_111,B_112)
      | ~ v1_funct_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_109,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_89,c_107])).

tff(c_118,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_109])).

tff(c_1507,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_1510,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1308,c_1507])).

tff(c_1513,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_1510])).

tff(c_1514,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1513])).

tff(c_1517,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1514])).

tff(c_1521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1517])).

tff(c_1523,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_12,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] :
      ( m1_subset_1(k3_tmap_1(A_11,B_12,C_13,D_14,E_15),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_14),u1_struct_0(B_12))))
      | ~ m1_subset_1(E_15,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13),u1_struct_0(B_12))))
      | ~ v1_funct_2(E_15,u1_struct_0(C_13),u1_struct_0(B_12))
      | ~ v1_funct_1(E_15)
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc(C_13,A_11)
      | ~ l1_pre_topc(B_12)
      | ~ v2_pre_topc(B_12)
      | v2_struct_0(B_12)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1522,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_1524,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1522])).

tff(c_1537,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1524])).

tff(c_1540,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_74,c_218,c_1304,c_987,c_1537])).

tff(c_1541,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_1540])).

tff(c_1544,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1541])).

tff(c_1548,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1544])).

tff(c_1550,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1522])).

tff(c_1352,plain,(
    ! [A_427,B_425,F_424,D_423,C_426,E_428] :
      ( v1_funct_1(k10_tmap_1(A_427,B_425,C_426,D_423,E_428,F_424))
      | ~ m1_subset_1(F_424,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_423),u1_struct_0(B_425))))
      | ~ v1_funct_2(F_424,u1_struct_0(D_423),u1_struct_0(B_425))
      | ~ v1_funct_1(F_424)
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426),u1_struct_0(B_425))))
      | ~ v1_funct_2(E_428,u1_struct_0(C_426),u1_struct_0(B_425))
      | ~ v1_funct_1(E_428)
      | ~ m1_pre_topc(D_423,A_427)
      | v2_struct_0(D_423)
      | ~ m1_pre_topc(C_426,A_427)
      | v2_struct_0(C_426)
      | ~ l1_pre_topc(B_425)
      | ~ v2_pre_topc(B_425)
      | v2_struct_0(B_425)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1360,plain,(
    ! [A_427,C_426,E_428] :
      ( v1_funct_1(k10_tmap_1(A_427,'#skF_2',C_426,'#skF_3',E_428,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_428,u1_struct_0(C_426),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_428)
      | ~ m1_pre_topc('#skF_3',A_427)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_426,A_427)
      | v2_struct_0(C_426)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(resolution,[status(thm)],[c_60,c_1352])).

tff(c_1372,plain,(
    ! [A_427,C_426,E_428] :
      ( v1_funct_1(k10_tmap_1(A_427,'#skF_2',C_426,'#skF_3',E_428,'#skF_5'))
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_428,u1_struct_0(C_426),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_428)
      | ~ m1_pre_topc('#skF_3',A_427)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_426,A_427)
      | v2_struct_0(C_426)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_64,c_1360])).

tff(c_1373,plain,(
    ! [A_427,C_426,E_428] :
      ( v1_funct_1(k10_tmap_1(A_427,'#skF_2',C_426,'#skF_3',E_428,'#skF_5'))
      | ~ m1_subset_1(E_428,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_428,u1_struct_0(C_426),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_428)
      | ~ m1_pre_topc('#skF_3',A_427)
      | ~ m1_pre_topc(C_426,A_427)
      | v2_struct_0(C_426)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_76,c_1372])).

tff(c_1554,plain,(
    ! [A_427] :
      ( v1_funct_1(k10_tmap_1(A_427,'#skF_2','#skF_3','#skF_3',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc('#skF_3',A_427)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(resolution,[status(thm)],[c_1550,c_1373])).

tff(c_1571,plain,(
    ! [A_427] :
      ( v1_funct_1(k10_tmap_1(A_427,'#skF_2','#skF_3','#skF_3',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_427)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1523,c_1554])).

tff(c_1572,plain,(
    ! [A_427] :
      ( v1_funct_1(k10_tmap_1(A_427,'#skF_2','#skF_3','#skF_3',k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_427)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427)
      | v2_struct_0(A_427) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1571])).

tff(c_1592,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1572])).

tff(c_1595,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1320,c_1592])).

tff(c_1598,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_1595])).

tff(c_1599,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1598])).

tff(c_1602,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1599])).

tff(c_1606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1602])).

tff(c_1608,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1572])).

tff(c_1549,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1522])).

tff(c_1611,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1608,c_1549])).

tff(c_62,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_48,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_90,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_48])).

tff(c_111,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_90,c_107])).

tff(c_121,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_111])).

tff(c_1674,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_1677,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1308,c_1674])).

tff(c_1680,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_70,c_1677])).

tff(c_1681,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1680])).

tff(c_1684,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1681])).

tff(c_1688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1684])).

tff(c_1689,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_1712,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1689])).

tff(c_1717,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1712])).

tff(c_1720,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_80,c_78,c_70,c_218,c_1304,c_987,c_1717])).

tff(c_1721,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_82,c_1720])).

tff(c_1724,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1721])).

tff(c_1728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1724])).

tff(c_1729,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1689])).

tff(c_1772,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1729])).

tff(c_1775,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1320,c_1772])).

tff(c_1778,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_70,c_1775])).

tff(c_1779,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1778])).

tff(c_1792,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1779])).

tff(c_1796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1792])).

tff(c_1797,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1729])).

tff(c_54,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_46,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_2610,plain,(
    ! [C_584,D_583,E_582,A_585,B_581] :
      ( v5_pre_topc(E_582,k1_tsep_1(A_585,C_584,D_583),B_581)
      | ~ m1_subset_1(k3_tmap_1(A_585,B_581,k1_tsep_1(A_585,C_584,D_583),D_583,E_582),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_583),u1_struct_0(B_581))))
      | ~ v5_pre_topc(k3_tmap_1(A_585,B_581,k1_tsep_1(A_585,C_584,D_583),D_583,E_582),D_583,B_581)
      | ~ v1_funct_2(k3_tmap_1(A_585,B_581,k1_tsep_1(A_585,C_584,D_583),D_583,E_582),u1_struct_0(D_583),u1_struct_0(B_581))
      | ~ v1_funct_1(k3_tmap_1(A_585,B_581,k1_tsep_1(A_585,C_584,D_583),D_583,E_582))
      | ~ m1_subset_1(k3_tmap_1(A_585,B_581,k1_tsep_1(A_585,C_584,D_583),C_584,E_582),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_584),u1_struct_0(B_581))))
      | ~ v5_pre_topc(k3_tmap_1(A_585,B_581,k1_tsep_1(A_585,C_584,D_583),C_584,E_582),C_584,B_581)
      | ~ v1_funct_2(k3_tmap_1(A_585,B_581,k1_tsep_1(A_585,C_584,D_583),C_584,E_582),u1_struct_0(C_584),u1_struct_0(B_581))
      | ~ v1_funct_1(k3_tmap_1(A_585,B_581,k1_tsep_1(A_585,C_584,D_583),C_584,E_582))
      | ~ m1_subset_1(E_582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_585,C_584,D_583)),u1_struct_0(B_581))))
      | ~ v1_funct_2(E_582,u1_struct_0(k1_tsep_1(A_585,C_584,D_583)),u1_struct_0(B_581))
      | ~ v1_funct_1(E_582)
      | ~ r4_tsep_1(A_585,C_584,D_583)
      | ~ m1_pre_topc(D_583,A_585)
      | v2_struct_0(D_583)
      | ~ m1_pre_topc(C_584,A_585)
      | v2_struct_0(C_584)
      | ~ l1_pre_topc(B_581)
      | ~ v2_pre_topc(B_581)
      | v2_struct_0(B_581)
      | ~ l1_pre_topc(A_585)
      | ~ v2_pre_topc(A_585)
      | v2_struct_0(A_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_2620,plain,(
    ! [E_582,B_581] :
      ( v5_pre_topc(E_582,k1_tsep_1('#skF_1','#skF_3','#skF_4'),B_581)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_4',E_582),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_581))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_581,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_582),'#skF_4',B_581)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_581,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_582),u1_struct_0('#skF_4'),u1_struct_0(B_581))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_581,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_582))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_581,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_582),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_581))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_581,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_582),'#skF_3',B_581)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_581,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_582),u1_struct_0('#skF_3'),u1_struct_0(B_581))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_581,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_582))
      | ~ m1_subset_1(E_582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_581))))
      | ~ v1_funct_2(E_582,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_581))
      | ~ v1_funct_1(E_582)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_581)
      | ~ v2_pre_topc(B_581)
      | v2_struct_0(B_581)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2610])).

tff(c_2625,plain,(
    ! [E_582,B_581] :
      ( v5_pre_topc(E_582,'#skF_1',B_581)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_4',E_582),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_581))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_4',E_582),'#skF_4',B_581)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_4',E_582),u1_struct_0('#skF_4'),u1_struct_0(B_581))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_4',E_582))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_3',E_582),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_581))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_3',E_582),'#skF_3',B_581)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_3',E_582),u1_struct_0('#skF_3'),u1_struct_0(B_581))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_581,'#skF_1','#skF_3',E_582))
      | ~ m1_subset_1(E_582,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_581))))
      | ~ v1_funct_2(E_582,u1_struct_0('#skF_1'),u1_struct_0(B_581))
      | ~ v1_funct_1(E_582)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_581)
      | ~ v2_pre_topc(B_581)
      | v2_struct_0(B_581)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_46,c_68,c_68,c_68,c_68,c_68,c_68,c_68,c_68,c_68,c_68,c_2620])).

tff(c_4289,plain,(
    ! [E_844,B_845] :
      ( v5_pre_topc(E_844,'#skF_1',B_845)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_845,'#skF_1','#skF_4',E_844),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_845))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_845,'#skF_1','#skF_4',E_844),'#skF_4',B_845)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_845,'#skF_1','#skF_4',E_844),u1_struct_0('#skF_4'),u1_struct_0(B_845))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_845,'#skF_1','#skF_4',E_844))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_845,'#skF_1','#skF_3',E_844),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_845))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_845,'#skF_1','#skF_3',E_844),'#skF_3',B_845)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_845,'#skF_1','#skF_3',E_844),u1_struct_0('#skF_3'),u1_struct_0(B_845))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_845,'#skF_1','#skF_3',E_844))
      | ~ m1_subset_1(E_844,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_845))))
      | ~ v1_funct_2(E_844,u1_struct_0('#skF_1'),u1_struct_0(B_845))
      | ~ v1_funct_1(E_844)
      | ~ l1_pre_topc(B_845)
      | ~ v2_pre_topc(B_845)
      | v2_struct_0(B_845) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_76,c_72,c_2625])).

tff(c_4295,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_3','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1611,c_4289])).

tff(c_4302,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_218,c_1304,c_987,c_66,c_1611,c_64,c_1611,c_62,c_1611,c_60,c_58,c_1797,c_56,c_1797,c_54,c_1797,c_52,c_1797,c_4295])).

tff(c_4304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1303,c_4302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:32:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.83/3.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.83/3.28  
% 8.83/3.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.83/3.29  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.83/3.29  
% 8.83/3.29  %Foreground sorts:
% 8.83/3.29  
% 8.83/3.29  
% 8.83/3.29  %Background operators:
% 8.83/3.29  
% 8.83/3.29  
% 8.83/3.29  %Foreground operators:
% 8.83/3.29  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.83/3.29  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.83/3.29  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.83/3.29  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.83/3.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.83/3.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.83/3.29  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.83/3.29  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 8.83/3.29  tff('#skF_5', type, '#skF_5': $i).
% 8.83/3.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.83/3.29  tff('#skF_6', type, '#skF_6': $i).
% 8.83/3.29  tff('#skF_2', type, '#skF_2': $i).
% 8.83/3.29  tff('#skF_3', type, '#skF_3': $i).
% 8.83/3.29  tff('#skF_1', type, '#skF_1': $i).
% 8.83/3.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.83/3.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.83/3.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.83/3.29  tff('#skF_4', type, '#skF_4': $i).
% 8.83/3.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.83/3.29  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 8.83/3.29  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.83/3.29  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.83/3.29  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.83/3.29  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.83/3.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.83/3.29  
% 9.05/3.33  tff(f_239, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_tmap_1)).
% 9.05/3.33  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 9.05/3.33  tff(f_177, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 9.05/3.33  tff(f_113, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 9.05/3.33  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 9.05/3.33  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_tmap_1)).
% 9.05/3.33  tff(c_82, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_80, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_78, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_64, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_56, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_88, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_76, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_86, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_84, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_74, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_70, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_68, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_852, plain, (![A_296, F_293, E_297, C_295, B_294, D_292]: (m1_subset_1(k10_tmap_1(A_296, B_294, C_295, D_292, E_297, F_293), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_296, C_295, D_292)), u1_struct_0(B_294)))) | ~m1_subset_1(F_293, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_292), u1_struct_0(B_294)))) | ~v1_funct_2(F_293, u1_struct_0(D_292), u1_struct_0(B_294)) | ~v1_funct_1(F_293) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_295), u1_struct_0(B_294)))) | ~v1_funct_2(E_297, u1_struct_0(C_295), u1_struct_0(B_294)) | ~v1_funct_1(E_297) | ~m1_pre_topc(D_292, A_296) | v2_struct_0(D_292) | ~m1_pre_topc(C_295, A_296) | v2_struct_0(C_295) | ~l1_pre_topc(B_294) | ~v2_pre_topc(B_294) | v2_struct_0(B_294) | ~l1_pre_topc(A_296) | ~v2_pre_topc(A_296) | v2_struct_0(A_296))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.05/3.33  tff(c_881, plain, (![B_294, E_297, F_293]: (m1_subset_1(k10_tmap_1('#skF_1', B_294, '#skF_3', '#skF_4', E_297, F_293), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_294)))) | ~m1_subset_1(F_293, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_294)))) | ~v1_funct_2(F_293, u1_struct_0('#skF_4'), u1_struct_0(B_294)) | ~v1_funct_1(F_293) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_294)))) | ~v1_funct_2(E_297, u1_struct_0('#skF_3'), u1_struct_0(B_294)) | ~v1_funct_1(E_297) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_294) | ~v2_pre_topc(B_294) | v2_struct_0(B_294) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_852])).
% 9.05/3.33  tff(c_901, plain, (![B_294, E_297, F_293]: (m1_subset_1(k10_tmap_1('#skF_1', B_294, '#skF_3', '#skF_4', E_297, F_293), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_294)))) | ~m1_subset_1(F_293, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_294)))) | ~v1_funct_2(F_293, u1_struct_0('#skF_4'), u1_struct_0(B_294)) | ~v1_funct_1(F_293) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_294)))) | ~v1_funct_2(E_297, u1_struct_0('#skF_3'), u1_struct_0(B_294)) | ~v1_funct_1(E_297) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_294) | ~v2_pre_topc(B_294) | v2_struct_0(B_294) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_881])).
% 9.05/3.33  tff(c_903, plain, (![B_298, E_299, F_300]: (m1_subset_1(k10_tmap_1('#skF_1', B_298, '#skF_3', '#skF_4', E_299, F_300), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_298)))) | ~m1_subset_1(F_300, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_298)))) | ~v1_funct_2(F_300, u1_struct_0('#skF_4'), u1_struct_0(B_298)) | ~v1_funct_1(F_300) | ~m1_subset_1(E_299, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_298)))) | ~v1_funct_2(E_299, u1_struct_0('#skF_3'), u1_struct_0(B_298)) | ~v1_funct_1(E_299) | ~l1_pre_topc(B_298) | ~v2_pre_topc(B_298) | v2_struct_0(B_298))), inference(negUnitSimplification, [status(thm)], [c_88, c_76, c_72, c_901])).
% 9.05/3.33  tff(c_171, plain, (![D_136, B_138, E_141, F_137, C_139, A_140]: (v1_funct_1(k10_tmap_1(A_140, B_138, C_139, D_136, E_141, F_137)) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_136), u1_struct_0(B_138)))) | ~v1_funct_2(F_137, u1_struct_0(D_136), u1_struct_0(B_138)) | ~v1_funct_1(F_137) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139), u1_struct_0(B_138)))) | ~v1_funct_2(E_141, u1_struct_0(C_139), u1_struct_0(B_138)) | ~v1_funct_1(E_141) | ~m1_pre_topc(D_136, A_140) | v2_struct_0(D_136) | ~m1_pre_topc(C_139, A_140) | v2_struct_0(C_139) | ~l1_pre_topc(B_138) | ~v2_pre_topc(B_138) | v2_struct_0(B_138) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.05/3.33  tff(c_175, plain, (![A_140, C_139, E_141]: (v1_funct_1(k10_tmap_1(A_140, '#skF_2', C_139, '#skF_4', E_141, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_141, u1_struct_0(C_139), u1_struct_0('#skF_2')) | ~v1_funct_1(E_141) | ~m1_pre_topc('#skF_4', A_140) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_139, A_140) | v2_struct_0(C_139) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_52, c_171])).
% 9.05/3.33  tff(c_181, plain, (![A_140, C_139, E_141]: (v1_funct_1(k10_tmap_1(A_140, '#skF_2', C_139, '#skF_4', E_141, '#skF_6')) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_141, u1_struct_0(C_139), u1_struct_0('#skF_2')) | ~v1_funct_1(E_141) | ~m1_pre_topc('#skF_4', A_140) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_139, A_140) | v2_struct_0(C_139) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_58, c_56, c_175])).
% 9.05/3.33  tff(c_187, plain, (![A_142, C_143, E_144]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', C_143, '#skF_4', E_144, '#skF_6')) | ~m1_subset_1(E_144, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_144, u1_struct_0(C_143), u1_struct_0('#skF_2')) | ~v1_funct_1(E_144) | ~m1_pre_topc('#skF_4', A_142) | ~m1_pre_topc(C_143, A_142) | v2_struct_0(C_143) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(negUnitSimplification, [status(thm)], [c_82, c_72, c_181])).
% 9.05/3.33  tff(c_194, plain, (![A_142]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_142) | ~m1_pre_topc('#skF_3', A_142) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_60, c_187])).
% 9.05/3.33  tff(c_205, plain, (![A_142]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_142) | ~m1_pre_topc('#skF_3', A_142) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_194])).
% 9.05/3.33  tff(c_208, plain, (![A_146]: (v1_funct_1(k10_tmap_1(A_146, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_146) | ~m1_pre_topc('#skF_3', A_146) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(negUnitSimplification, [status(thm)], [c_76, c_205])).
% 9.05/3.33  tff(c_44, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_144, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_44])).
% 9.05/3.33  tff(c_211, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_208, c_144])).
% 9.05/3.33  tff(c_214, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_211])).
% 9.05/3.33  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_214])).
% 9.05/3.33  tff(c_217, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_44])).
% 9.05/3.33  tff(c_220, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_217])).
% 9.05/3.33  tff(c_942, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_903, c_220])).
% 9.05/3.33  tff(c_983, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_64, c_60, c_58, c_56, c_52, c_942])).
% 9.05/3.33  tff(c_985, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_983])).
% 9.05/3.33  tff(c_986, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_217])).
% 9.05/3.33  tff(c_999, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_986])).
% 9.05/3.33  tff(c_1257, plain, (![A_397, C_396, B_395, D_393, E_398, F_394]: (v1_funct_2(k10_tmap_1(A_397, B_395, C_396, D_393, E_398, F_394), u1_struct_0(k1_tsep_1(A_397, C_396, D_393)), u1_struct_0(B_395)) | ~m1_subset_1(F_394, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_393), u1_struct_0(B_395)))) | ~v1_funct_2(F_394, u1_struct_0(D_393), u1_struct_0(B_395)) | ~v1_funct_1(F_394) | ~m1_subset_1(E_398, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396), u1_struct_0(B_395)))) | ~v1_funct_2(E_398, u1_struct_0(C_396), u1_struct_0(B_395)) | ~v1_funct_1(E_398) | ~m1_pre_topc(D_393, A_397) | v2_struct_0(D_393) | ~m1_pre_topc(C_396, A_397) | v2_struct_0(C_396) | ~l1_pre_topc(B_395) | ~v2_pre_topc(B_395) | v2_struct_0(B_395) | ~l1_pre_topc(A_397) | ~v2_pre_topc(A_397) | v2_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.05/3.33  tff(c_1260, plain, (![B_395, E_398, F_394]: (v1_funct_2(k10_tmap_1('#skF_1', B_395, '#skF_3', '#skF_4', E_398, F_394), u1_struct_0('#skF_1'), u1_struct_0(B_395)) | ~m1_subset_1(F_394, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_395)))) | ~v1_funct_2(F_394, u1_struct_0('#skF_4'), u1_struct_0(B_395)) | ~v1_funct_1(F_394) | ~m1_subset_1(E_398, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_395)))) | ~v1_funct_2(E_398, u1_struct_0('#skF_3'), u1_struct_0(B_395)) | ~v1_funct_1(E_398) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_395) | ~v2_pre_topc(B_395) | v2_struct_0(B_395) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1257])).
% 9.05/3.33  tff(c_1262, plain, (![B_395, E_398, F_394]: (v1_funct_2(k10_tmap_1('#skF_1', B_395, '#skF_3', '#skF_4', E_398, F_394), u1_struct_0('#skF_1'), u1_struct_0(B_395)) | ~m1_subset_1(F_394, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_395)))) | ~v1_funct_2(F_394, u1_struct_0('#skF_4'), u1_struct_0(B_395)) | ~v1_funct_1(F_394) | ~m1_subset_1(E_398, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_395)))) | ~v1_funct_2(E_398, u1_struct_0('#skF_3'), u1_struct_0(B_395)) | ~v1_funct_1(E_398) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_395) | ~v2_pre_topc(B_395) | v2_struct_0(B_395) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_1260])).
% 9.05/3.33  tff(c_1275, plain, (![B_401, E_402, F_403]: (v1_funct_2(k10_tmap_1('#skF_1', B_401, '#skF_3', '#skF_4', E_402, F_403), u1_struct_0('#skF_1'), u1_struct_0(B_401)) | ~m1_subset_1(F_403, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_401)))) | ~v1_funct_2(F_403, u1_struct_0('#skF_4'), u1_struct_0(B_401)) | ~v1_funct_1(F_403) | ~m1_subset_1(E_402, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_401)))) | ~v1_funct_2(E_402, u1_struct_0('#skF_3'), u1_struct_0(B_401)) | ~v1_funct_1(E_402) | ~l1_pre_topc(B_401) | ~v2_pre_topc(B_401) | v2_struct_0(B_401))), inference(negUnitSimplification, [status(thm)], [c_88, c_76, c_72, c_1262])).
% 9.05/3.33  tff(c_1280, plain, (![E_402]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_402, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_402, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_402, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_402) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_1275])).
% 9.05/3.33  tff(c_1284, plain, (![E_402]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_402, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_402, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_402, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_402) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_58, c_56, c_1280])).
% 9.05/3.33  tff(c_1286, plain, (![E_404]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_404, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_404, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_404, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_404))), inference(negUnitSimplification, [status(thm)], [c_82, c_1284])).
% 9.05/3.33  tff(c_1293, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_1286])).
% 9.05/3.33  tff(c_1300, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1293])).
% 9.05/3.33  tff(c_1302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_999, c_1300])).
% 9.05/3.33  tff(c_1303, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_986])).
% 9.05/3.33  tff(c_218, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_44])).
% 9.05/3.33  tff(c_1304, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_986])).
% 9.05/3.33  tff(c_987, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_217])).
% 9.05/3.33  tff(c_42, plain, (![A_47]: (m1_pre_topc(A_47, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_177])).
% 9.05/3.33  tff(c_1310, plain, (![C_405, E_409, B_407, D_408, A_406]: (v1_funct_2(k3_tmap_1(A_406, B_407, C_405, D_408, E_409), u1_struct_0(D_408), u1_struct_0(B_407)) | ~m1_subset_1(E_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_405), u1_struct_0(B_407)))) | ~v1_funct_2(E_409, u1_struct_0(C_405), u1_struct_0(B_407)) | ~v1_funct_1(E_409) | ~m1_pre_topc(D_408, A_406) | ~m1_pre_topc(C_405, A_406) | ~l1_pre_topc(B_407) | ~v2_pre_topc(B_407) | v2_struct_0(B_407) | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.05/3.33  tff(c_1312, plain, (![A_406, D_408]: (v1_funct_2(k3_tmap_1(A_406, '#skF_2', '#skF_1', D_408, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_408), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_408, A_406) | ~m1_pre_topc('#skF_1', A_406) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406))), inference(resolution, [status(thm)], [c_987, c_1310])).
% 9.05/3.33  tff(c_1319, plain, (![A_406, D_408]: (v1_funct_2(k3_tmap_1(A_406, '#skF_2', '#skF_1', D_408, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_408), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_408, A_406) | ~m1_pre_topc('#skF_1', A_406) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_218, c_1304, c_1312])).
% 9.05/3.33  tff(c_1320, plain, (![A_406, D_408]: (v1_funct_2(k3_tmap_1(A_406, '#skF_2', '#skF_1', D_408, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_408), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_408, A_406) | ~m1_pre_topc('#skF_1', A_406) | ~l1_pre_topc(A_406) | ~v2_pre_topc(A_406) | v2_struct_0(A_406))), inference(negUnitSimplification, [status(thm)], [c_82, c_1319])).
% 9.05/3.33  tff(c_16, plain, (![D_14, E_15, B_12, A_11, C_13]: (v1_funct_1(k3_tmap_1(A_11, B_12, C_13, D_14, E_15)) | ~m1_subset_1(E_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13), u1_struct_0(B_12)))) | ~v1_funct_2(E_15, u1_struct_0(C_13), u1_struct_0(B_12)) | ~v1_funct_1(E_15) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(C_13, A_11) | ~l1_pre_topc(B_12) | ~v2_pre_topc(B_12) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.05/3.33  tff(c_989, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_1', D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_1', A_11) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(resolution, [status(thm)], [c_987, c_16])).
% 9.05/3.33  tff(c_994, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_1', D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_1', A_11) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_218, c_989])).
% 9.05/3.33  tff(c_995, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_1', D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_1', A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(negUnitSimplification, [status(thm)], [c_82, c_994])).
% 9.05/3.33  tff(c_1305, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_995])).
% 9.05/3.33  tff(c_1307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1304, c_1305])).
% 9.05/3.33  tff(c_1308, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_1', D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_1', A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(splitRight, [status(thm)], [c_995])).
% 9.05/3.33  tff(c_50, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_89, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_50])).
% 9.05/3.33  tff(c_107, plain, (![D_109, C_110, A_111, B_112]: (D_109=C_110 | ~r2_funct_2(A_111, B_112, C_110, D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(D_109, A_111, B_112) | ~v1_funct_1(D_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(C_110, A_111, B_112) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.05/3.33  tff(c_109, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_89, c_107])).
% 9.05/3.33  tff(c_118, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_109])).
% 9.05/3.33  tff(c_1507, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_118])).
% 9.05/3.33  tff(c_1510, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1308, c_1507])).
% 9.05/3.33  tff(c_1513, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_1510])).
% 9.05/3.33  tff(c_1514, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_88, c_1513])).
% 9.05/3.33  tff(c_1517, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1514])).
% 9.05/3.33  tff(c_1521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1517])).
% 9.05/3.33  tff(c_1523, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_118])).
% 9.05/3.33  tff(c_12, plain, (![D_14, E_15, B_12, A_11, C_13]: (m1_subset_1(k3_tmap_1(A_11, B_12, C_13, D_14, E_15), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_14), u1_struct_0(B_12)))) | ~m1_subset_1(E_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13), u1_struct_0(B_12)))) | ~v1_funct_2(E_15, u1_struct_0(C_13), u1_struct_0(B_12)) | ~v1_funct_1(E_15) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(C_13, A_11) | ~l1_pre_topc(B_12) | ~v2_pre_topc(B_12) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_113])).
% 9.05/3.33  tff(c_1522, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_118])).
% 9.05/3.33  tff(c_1524, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1522])).
% 9.05/3.33  tff(c_1537, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1524])).
% 9.05/3.33  tff(c_1540, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_74, c_218, c_1304, c_987, c_1537])).
% 9.05/3.33  tff(c_1541, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_1540])).
% 9.05/3.33  tff(c_1544, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1541])).
% 9.05/3.33  tff(c_1548, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1544])).
% 9.05/3.33  tff(c_1550, plain, (m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1522])).
% 9.05/3.33  tff(c_1352, plain, (![A_427, B_425, F_424, D_423, C_426, E_428]: (v1_funct_1(k10_tmap_1(A_427, B_425, C_426, D_423, E_428, F_424)) | ~m1_subset_1(F_424, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_423), u1_struct_0(B_425)))) | ~v1_funct_2(F_424, u1_struct_0(D_423), u1_struct_0(B_425)) | ~v1_funct_1(F_424) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426), u1_struct_0(B_425)))) | ~v1_funct_2(E_428, u1_struct_0(C_426), u1_struct_0(B_425)) | ~v1_funct_1(E_428) | ~m1_pre_topc(D_423, A_427) | v2_struct_0(D_423) | ~m1_pre_topc(C_426, A_427) | v2_struct_0(C_426) | ~l1_pre_topc(B_425) | ~v2_pre_topc(B_425) | v2_struct_0(B_425) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.05/3.33  tff(c_1360, plain, (![A_427, C_426, E_428]: (v1_funct_1(k10_tmap_1(A_427, '#skF_2', C_426, '#skF_3', E_428, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_428, u1_struct_0(C_426), u1_struct_0('#skF_2')) | ~v1_funct_1(E_428) | ~m1_pre_topc('#skF_3', A_427) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_426, A_427) | v2_struct_0(C_426) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(resolution, [status(thm)], [c_60, c_1352])).
% 9.05/3.33  tff(c_1372, plain, (![A_427, C_426, E_428]: (v1_funct_1(k10_tmap_1(A_427, '#skF_2', C_426, '#skF_3', E_428, '#skF_5')) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_428, u1_struct_0(C_426), u1_struct_0('#skF_2')) | ~v1_funct_1(E_428) | ~m1_pre_topc('#skF_3', A_427) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_426, A_427) | v2_struct_0(C_426) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_64, c_1360])).
% 9.05/3.33  tff(c_1373, plain, (![A_427, C_426, E_428]: (v1_funct_1(k10_tmap_1(A_427, '#skF_2', C_426, '#skF_3', E_428, '#skF_5')) | ~m1_subset_1(E_428, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_426), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_428, u1_struct_0(C_426), u1_struct_0('#skF_2')) | ~v1_funct_1(E_428) | ~m1_pre_topc('#skF_3', A_427) | ~m1_pre_topc(C_426, A_427) | v2_struct_0(C_426) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(negUnitSimplification, [status(thm)], [c_82, c_76, c_1372])).
% 9.05/3.33  tff(c_1554, plain, (![A_427]: (v1_funct_1(k10_tmap_1(A_427, '#skF_2', '#skF_3', '#skF_3', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc('#skF_3', A_427) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(resolution, [status(thm)], [c_1550, c_1373])).
% 9.05/3.33  tff(c_1571, plain, (![A_427]: (v1_funct_1(k10_tmap_1(A_427, '#skF_2', '#skF_3', '#skF_3', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', A_427) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(demodulation, [status(thm), theory('equality')], [c_1523, c_1554])).
% 9.05/3.33  tff(c_1572, plain, (![A_427]: (v1_funct_1(k10_tmap_1(A_427, '#skF_2', '#skF_3', '#skF_3', k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', A_427) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427) | v2_struct_0(A_427))), inference(negUnitSimplification, [status(thm)], [c_76, c_1571])).
% 9.05/3.33  tff(c_1592, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1572])).
% 9.05/3.33  tff(c_1595, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1320, c_1592])).
% 9.05/3.33  tff(c_1598, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_1595])).
% 9.05/3.33  tff(c_1599, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_88, c_1598])).
% 9.05/3.33  tff(c_1602, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1599])).
% 9.05/3.33  tff(c_1606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1602])).
% 9.05/3.33  tff(c_1608, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1572])).
% 9.05/3.33  tff(c_1549, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1522])).
% 9.05/3.33  tff(c_1611, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1608, c_1549])).
% 9.05/3.33  tff(c_62, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_48, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_90, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_48])).
% 9.05/3.33  tff(c_111, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_90, c_107])).
% 9.05/3.33  tff(c_121, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_111])).
% 9.05/3.33  tff(c_1674, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_121])).
% 9.05/3.33  tff(c_1677, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1308, c_1674])).
% 9.05/3.33  tff(c_1680, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_70, c_1677])).
% 9.05/3.33  tff(c_1681, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_88, c_1680])).
% 9.05/3.33  tff(c_1684, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1681])).
% 9.05/3.33  tff(c_1688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1684])).
% 9.05/3.33  tff(c_1689, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_121])).
% 9.05/3.33  tff(c_1712, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1689])).
% 9.05/3.33  tff(c_1717, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1712])).
% 9.05/3.33  tff(c_1720, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_80, c_78, c_70, c_218, c_1304, c_987, c_1717])).
% 9.05/3.33  tff(c_1721, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_88, c_82, c_1720])).
% 9.05/3.33  tff(c_1724, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1721])).
% 9.05/3.33  tff(c_1728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1724])).
% 9.05/3.33  tff(c_1729, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1689])).
% 9.05/3.33  tff(c_1772, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1729])).
% 9.05/3.33  tff(c_1775, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1320, c_1772])).
% 9.05/3.33  tff(c_1778, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_70, c_1775])).
% 9.05/3.33  tff(c_1779, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_88, c_1778])).
% 9.05/3.33  tff(c_1792, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1779])).
% 9.05/3.33  tff(c_1796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1792])).
% 9.05/3.33  tff(c_1797, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1729])).
% 9.05/3.33  tff(c_54, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_46, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 9.05/3.33  tff(c_2610, plain, (![C_584, D_583, E_582, A_585, B_581]: (v5_pre_topc(E_582, k1_tsep_1(A_585, C_584, D_583), B_581) | ~m1_subset_1(k3_tmap_1(A_585, B_581, k1_tsep_1(A_585, C_584, D_583), D_583, E_582), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_583), u1_struct_0(B_581)))) | ~v5_pre_topc(k3_tmap_1(A_585, B_581, k1_tsep_1(A_585, C_584, D_583), D_583, E_582), D_583, B_581) | ~v1_funct_2(k3_tmap_1(A_585, B_581, k1_tsep_1(A_585, C_584, D_583), D_583, E_582), u1_struct_0(D_583), u1_struct_0(B_581)) | ~v1_funct_1(k3_tmap_1(A_585, B_581, k1_tsep_1(A_585, C_584, D_583), D_583, E_582)) | ~m1_subset_1(k3_tmap_1(A_585, B_581, k1_tsep_1(A_585, C_584, D_583), C_584, E_582), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_584), u1_struct_0(B_581)))) | ~v5_pre_topc(k3_tmap_1(A_585, B_581, k1_tsep_1(A_585, C_584, D_583), C_584, E_582), C_584, B_581) | ~v1_funct_2(k3_tmap_1(A_585, B_581, k1_tsep_1(A_585, C_584, D_583), C_584, E_582), u1_struct_0(C_584), u1_struct_0(B_581)) | ~v1_funct_1(k3_tmap_1(A_585, B_581, k1_tsep_1(A_585, C_584, D_583), C_584, E_582)) | ~m1_subset_1(E_582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_585, C_584, D_583)), u1_struct_0(B_581)))) | ~v1_funct_2(E_582, u1_struct_0(k1_tsep_1(A_585, C_584, D_583)), u1_struct_0(B_581)) | ~v1_funct_1(E_582) | ~r4_tsep_1(A_585, C_584, D_583) | ~m1_pre_topc(D_583, A_585) | v2_struct_0(D_583) | ~m1_pre_topc(C_584, A_585) | v2_struct_0(C_584) | ~l1_pre_topc(B_581) | ~v2_pre_topc(B_581) | v2_struct_0(B_581) | ~l1_pre_topc(A_585) | ~v2_pre_topc(A_585) | v2_struct_0(A_585))), inference(cnfTransformation, [status(thm)], [f_173])).
% 9.05/3.33  tff(c_2620, plain, (![E_582, B_581]: (v5_pre_topc(E_582, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), B_581) | ~m1_subset_1(k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_4', E_582), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_581)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_581, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_582), '#skF_4', B_581) | ~v1_funct_2(k3_tmap_1('#skF_1', B_581, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_582), u1_struct_0('#skF_4'), u1_struct_0(B_581)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_581, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_582)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_581, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_582), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_581)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_581, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_582), '#skF_3', B_581) | ~v1_funct_2(k3_tmap_1('#skF_1', B_581, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_582), u1_struct_0('#skF_3'), u1_struct_0(B_581)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_581, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_582)) | ~m1_subset_1(E_582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_581)))) | ~v1_funct_2(E_582, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_581)) | ~v1_funct_1(E_582) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_581) | ~v2_pre_topc(B_581) | v2_struct_0(B_581) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2610])).
% 9.05/3.33  tff(c_2625, plain, (![E_582, B_581]: (v5_pre_topc(E_582, '#skF_1', B_581) | ~m1_subset_1(k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_4', E_582), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_581)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_4', E_582), '#skF_4', B_581) | ~v1_funct_2(k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_4', E_582), u1_struct_0('#skF_4'), u1_struct_0(B_581)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_4', E_582)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_3', E_582), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_581)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_3', E_582), '#skF_3', B_581) | ~v1_funct_2(k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_3', E_582), u1_struct_0('#skF_3'), u1_struct_0(B_581)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_581, '#skF_1', '#skF_3', E_582)) | ~m1_subset_1(E_582, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_581)))) | ~v1_funct_2(E_582, u1_struct_0('#skF_1'), u1_struct_0(B_581)) | ~v1_funct_1(E_582) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_581) | ~v2_pre_topc(B_581) | v2_struct_0(B_581) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_46, c_68, c_68, c_68, c_68, c_68, c_68, c_68, c_68, c_68, c_68, c_2620])).
% 9.05/3.33  tff(c_4289, plain, (![E_844, B_845]: (v5_pre_topc(E_844, '#skF_1', B_845) | ~m1_subset_1(k3_tmap_1('#skF_1', B_845, '#skF_1', '#skF_4', E_844), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_845)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_845, '#skF_1', '#skF_4', E_844), '#skF_4', B_845) | ~v1_funct_2(k3_tmap_1('#skF_1', B_845, '#skF_1', '#skF_4', E_844), u1_struct_0('#skF_4'), u1_struct_0(B_845)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_845, '#skF_1', '#skF_4', E_844)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_845, '#skF_1', '#skF_3', E_844), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_845)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_845, '#skF_1', '#skF_3', E_844), '#skF_3', B_845) | ~v1_funct_2(k3_tmap_1('#skF_1', B_845, '#skF_1', '#skF_3', E_844), u1_struct_0('#skF_3'), u1_struct_0(B_845)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_845, '#skF_1', '#skF_3', E_844)) | ~m1_subset_1(E_844, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_845)))) | ~v1_funct_2(E_844, u1_struct_0('#skF_1'), u1_struct_0(B_845)) | ~v1_funct_1(E_844) | ~l1_pre_topc(B_845) | ~v2_pre_topc(B_845) | v2_struct_0(B_845))), inference(negUnitSimplification, [status(thm)], [c_88, c_76, c_72, c_2625])).
% 9.05/3.33  tff(c_4295, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1611, c_4289])).
% 9.05/3.33  tff(c_4302, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_218, c_1304, c_987, c_66, c_1611, c_64, c_1611, c_62, c_1611, c_60, c_58, c_1797, c_56, c_1797, c_54, c_1797, c_52, c_1797, c_4295])).
% 9.05/3.33  tff(c_4304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_1303, c_4302])).
% 9.05/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.05/3.33  
% 9.05/3.33  Inference rules
% 9.05/3.33  ----------------------
% 9.05/3.33  #Ref     : 0
% 9.05/3.33  #Sup     : 718
% 9.05/3.33  #Fact    : 0
% 9.05/3.33  #Define  : 0
% 9.05/3.33  #Split   : 15
% 9.05/3.33  #Chain   : 0
% 9.05/3.33  #Close   : 0
% 9.05/3.33  
% 9.05/3.33  Ordering : KBO
% 9.05/3.33  
% 9.05/3.33  Simplification rules
% 9.05/3.33  ----------------------
% 9.05/3.33  #Subsume      : 108
% 9.05/3.33  #Demod        : 2093
% 9.05/3.33  #Tautology    : 50
% 9.05/3.33  #SimpNegUnit  : 441
% 9.05/3.33  #BackRed      : 8
% 9.05/3.33  
% 9.05/3.33  #Partial instantiations: 0
% 9.05/3.33  #Strategies tried      : 1
% 9.05/3.33  
% 9.05/3.33  Timing (in seconds)
% 9.05/3.33  ----------------------
% 9.05/3.33  Preprocessing        : 0.43
% 9.05/3.33  Parsing              : 0.21
% 9.05/3.34  CNF conversion       : 0.07
% 9.05/3.34  Main loop            : 2.06
% 9.05/3.34  Inferencing          : 0.64
% 9.05/3.34  Reduction            : 0.63
% 9.05/3.34  Demodulation         : 0.47
% 9.05/3.34  BG Simplification    : 0.07
% 9.05/3.34  Subsumption          : 0.65
% 9.05/3.34  Abstraction          : 0.09
% 9.05/3.34  MUC search           : 0.00
% 9.05/3.34  Cooper               : 0.00
% 9.05/3.34  Total                : 2.57
% 9.05/3.34  Index Insertion      : 0.00
% 9.05/3.34  Index Deletion       : 0.00
% 9.05/3.34  Index Matching       : 0.00
% 9.05/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
