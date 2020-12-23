%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:10 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.93s
% Verified   : 
% Statistics : Number of formulae       :  166 (2145 expanded)
%              Number of leaves         :   35 ( 851 expanded)
%              Depth                    :   20
%              Number of atoms          :  752 (23814 expanded)
%              Number of equality atoms :   13 ( 166 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_314,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(C,D)
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
                             => ( ( r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F))
                                  & r4_tsep_1(A,C,D) )
                               => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                  & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                  & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                  & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_tmap_1)).

tff(f_163,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_141,axiom,(
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

tff(f_193,axiom,(
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

tff(f_99,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( ( v1_funct_1(F)
                            & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                            & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                         => ( ( r1_tsep_1(C,D)
                              | r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F)) )
                           => ! [G] :
                                ( ( v1_funct_1(G)
                                  & v1_funct_2(G,u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                  & m1_subset_1(G,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) )
                               => ( G = k10_tmap_1(A,B,C,D,E,F)
                                <=> ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,G),E)
                                    & r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,G),F) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_tmap_1)).

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

tff(f_253,axiom,(
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

tff(c_68,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_102,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_98,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_88,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_84,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_24,plain,(
    ! [A_138,B_139,C_140] :
      ( m1_pre_topc(k1_tsep_1(A_138,B_139,C_140),A_138)
      | ~ m1_pre_topc(C_140,A_138)
      | v2_struct_0(C_140)
      | ~ m1_pre_topc(B_139,A_138)
      | v2_struct_0(B_139)
      | ~ l1_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_100,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_94,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_92,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_78,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_70,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_671,plain,(
    ! [C_432,D_436,F_435,B_433,A_431,E_434] :
      ( v1_funct_2(k10_tmap_1(A_431,B_433,C_432,D_436,E_434,F_435),u1_struct_0(k1_tsep_1(A_431,C_432,D_436)),u1_struct_0(B_433))
      | ~ m1_subset_1(F_435,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_436),u1_struct_0(B_433))))
      | ~ v1_funct_2(F_435,u1_struct_0(D_436),u1_struct_0(B_433))
      | ~ v1_funct_1(F_435)
      | ~ m1_subset_1(E_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_432),u1_struct_0(B_433))))
      | ~ v1_funct_2(E_434,u1_struct_0(C_432),u1_struct_0(B_433))
      | ~ v1_funct_1(E_434)
      | ~ m1_pre_topc(D_436,A_431)
      | v2_struct_0(D_436)
      | ~ m1_pre_topc(C_432,A_431)
      | v2_struct_0(C_432)
      | ~ l1_pre_topc(B_433)
      | ~ v2_pre_topc(B_433)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_469,plain,(
    ! [C_381,A_380,F_384,D_385,E_383,B_382] :
      ( m1_subset_1(k10_tmap_1(A_380,B_382,C_381,D_385,E_383,F_384),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_380,C_381,D_385)),u1_struct_0(B_382))))
      | ~ m1_subset_1(F_384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_385),u1_struct_0(B_382))))
      | ~ v1_funct_2(F_384,u1_struct_0(D_385),u1_struct_0(B_382))
      | ~ v1_funct_1(F_384)
      | ~ m1_subset_1(E_383,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_381),u1_struct_0(B_382))))
      | ~ v1_funct_2(E_383,u1_struct_0(C_381),u1_struct_0(B_382))
      | ~ v1_funct_1(E_383)
      | ~ m1_pre_topc(D_385,A_380)
      | v2_struct_0(D_385)
      | ~ m1_pre_topc(C_381,A_380)
      | v2_struct_0(C_381)
      | ~ l1_pre_topc(B_382)
      | ~ v2_pre_topc(B_382)
      | v2_struct_0(B_382)
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_174,plain,(
    ! [F_277,D_278,C_274,B_275,A_273,E_276] :
      ( v1_funct_1(k10_tmap_1(A_273,B_275,C_274,D_278,E_276,F_277))
      | ~ m1_subset_1(F_277,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_278),u1_struct_0(B_275))))
      | ~ v1_funct_2(F_277,u1_struct_0(D_278),u1_struct_0(B_275))
      | ~ v1_funct_1(F_277)
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_274),u1_struct_0(B_275))))
      | ~ v1_funct_2(E_276,u1_struct_0(C_274),u1_struct_0(B_275))
      | ~ v1_funct_1(E_276)
      | ~ m1_pre_topc(D_278,A_273)
      | v2_struct_0(D_278)
      | ~ m1_pre_topc(C_274,A_273)
      | v2_struct_0(C_274)
      | ~ l1_pre_topc(B_275)
      | ~ v2_pre_topc(B_275)
      | v2_struct_0(B_275)
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_178,plain,(
    ! [A_273,C_274,E_276] :
      ( v1_funct_1(k10_tmap_1(A_273,'#skF_2',C_274,'#skF_4',E_276,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_274),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_276,u1_struct_0(C_274),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_276)
      | ~ m1_pre_topc('#skF_4',A_273)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_274,A_273)
      | v2_struct_0(C_274)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_66,c_174])).

tff(c_184,plain,(
    ! [A_273,C_274,E_276] :
      ( v1_funct_1(k10_tmap_1(A_273,'#skF_2',C_274,'#skF_4',E_276,'#skF_6'))
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_274),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_276,u1_struct_0(C_274),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_276)
      | ~ m1_pre_topc('#skF_4',A_273)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_274,A_273)
      | v2_struct_0(C_274)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_72,c_70,c_178])).

tff(c_190,plain,(
    ! [A_279,C_280,E_281] :
      ( v1_funct_1(k10_tmap_1(A_279,'#skF_2',C_280,'#skF_4',E_281,'#skF_6'))
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_280),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_281,u1_struct_0(C_280),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_281)
      | ~ m1_pre_topc('#skF_4',A_279)
      | ~ m1_pre_topc(C_280,A_279)
      | v2_struct_0(C_280)
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_86,c_184])).

tff(c_197,plain,(
    ! [A_279] :
      ( v1_funct_1(k10_tmap_1(A_279,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_279)
      | ~ m1_pre_topc('#skF_3',A_279)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(resolution,[status(thm)],[c_74,c_190])).

tff(c_208,plain,(
    ! [A_279] :
      ( v1_funct_1(k10_tmap_1(A_279,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_279)
      | ~ m1_pre_topc('#skF_3',A_279)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_279)
      | ~ v2_pre_topc(A_279)
      | v2_struct_0(A_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_197])).

tff(c_211,plain,(
    ! [A_283] :
      ( v1_funct_1(k10_tmap_1(A_283,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_283)
      | ~ m1_pre_topc('#skF_3',A_283)
      | ~ l1_pre_topc(A_283)
      | ~ v2_pre_topc(A_283)
      | v2_struct_0(A_283) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_208])).

tff(c_60,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_146,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_214,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_211,c_146])).

tff(c_217,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_88,c_84,c_214])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_217])).

tff(c_220,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_237,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_492,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
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
    inference(resolution,[status(thm)],[c_469,c_237])).

tff(c_516,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_94,c_92,c_88,c_84,c_80,c_78,c_74,c_72,c_70,c_66,c_492])).

tff(c_518,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_90,c_86,c_516])).

tff(c_519,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_538,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_674,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
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
    inference(resolution,[status(thm)],[c_671,c_538])).

tff(c_677,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_94,c_92,c_88,c_84,c_80,c_78,c_74,c_72,c_70,c_66,c_674])).

tff(c_679,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_90,c_86,c_677])).

tff(c_681,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_221,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_520,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_32,plain,(
    ! [C_143,A_141,D_144,E_145,B_142] :
      ( v1_funct_2(k3_tmap_1(A_141,B_142,C_143,D_144,E_145),u1_struct_0(D_144),u1_struct_0(B_142))
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0(B_142))))
      | ~ v1_funct_2(E_145,u1_struct_0(C_143),u1_struct_0(B_142))
      | ~ v1_funct_1(E_145)
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(C_143,A_141)
      | ~ l1_pre_topc(B_142)
      | ~ v2_pre_topc(B_142)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_522,plain,(
    ! [A_141,D_144] :
      ( v1_funct_2(k3_tmap_1(A_141,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_144,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_144),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_141)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_520,c_32])).

tff(c_529,plain,(
    ! [A_141,D_144] :
      ( v1_funct_2(k3_tmap_1(A_141,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_144,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_144),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_141)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_221,c_522])).

tff(c_530,plain,(
    ! [A_141,D_144] :
      ( v1_funct_2(k3_tmap_1(A_141,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_144,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_144),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_529])).

tff(c_706,plain,(
    ! [A_141,D_144] :
      ( v1_funct_2(k3_tmap_1(A_141,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_144,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_144),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_530])).

tff(c_680,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_62,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_30,plain,(
    ! [C_143,A_141,D_144,E_145,B_142] :
      ( m1_subset_1(k3_tmap_1(A_141,B_142,C_143,D_144,E_145),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_144),u1_struct_0(B_142))))
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0(B_142))))
      | ~ v1_funct_2(E_145,u1_struct_0(C_143),u1_struct_0(B_142))
      | ~ v1_funct_1(E_145)
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(C_143,A_141)
      | ~ l1_pre_topc(B_142)
      | ~ v2_pre_topc(B_142)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_34,plain,(
    ! [C_143,A_141,D_144,E_145,B_142] :
      ( v1_funct_1(k3_tmap_1(A_141,B_142,C_143,D_144,E_145))
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143),u1_struct_0(B_142))))
      | ~ v1_funct_2(E_145,u1_struct_0(C_143),u1_struct_0(B_142))
      | ~ v1_funct_1(E_145)
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(C_143,A_141)
      | ~ l1_pre_topc(B_142)
      | ~ v2_pre_topc(B_142)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_524,plain,(
    ! [A_141,D_144] :
      ( v1_funct_1(k3_tmap_1(A_141,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_144,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_141)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_520,c_34])).

tff(c_533,plain,(
    ! [A_141,D_144] :
      ( v1_funct_1(k3_tmap_1(A_141,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_144,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_141)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_221,c_524])).

tff(c_534,plain,(
    ! [A_141,D_144] :
      ( v1_funct_1(k3_tmap_1(A_141,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_144,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_533])).

tff(c_685,plain,(
    ! [A_141,D_144] :
      ( v1_funct_1(k3_tmap_1(A_141,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_144,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_144,A_141)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_141)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_534])).

tff(c_64,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_1537,plain,(
    ! [F_736,D_735,A_734,C_733,E_732,B_731] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_734,C_733,D_735)),u1_struct_0(B_731),k3_tmap_1(A_734,B_731,C_733,k2_tsep_1(A_734,C_733,D_735),E_732),k3_tmap_1(A_734,B_731,D_735,k2_tsep_1(A_734,C_733,D_735),F_736))
      | r2_funct_2(u1_struct_0(C_733),u1_struct_0(B_731),k3_tmap_1(A_734,B_731,k1_tsep_1(A_734,C_733,D_735),C_733,k10_tmap_1(A_734,B_731,C_733,D_735,E_732,F_736)),E_732)
      | ~ m1_subset_1(k10_tmap_1(A_734,B_731,C_733,D_735,E_732,F_736),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_734,C_733,D_735)),u1_struct_0(B_731))))
      | ~ v1_funct_2(k10_tmap_1(A_734,B_731,C_733,D_735,E_732,F_736),u1_struct_0(k1_tsep_1(A_734,C_733,D_735)),u1_struct_0(B_731))
      | ~ v1_funct_1(k10_tmap_1(A_734,B_731,C_733,D_735,E_732,F_736))
      | ~ m1_subset_1(F_736,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_735),u1_struct_0(B_731))))
      | ~ v1_funct_2(F_736,u1_struct_0(D_735),u1_struct_0(B_731))
      | ~ v1_funct_1(F_736)
      | ~ m1_subset_1(E_732,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_733),u1_struct_0(B_731))))
      | ~ v1_funct_2(E_732,u1_struct_0(C_733),u1_struct_0(B_731))
      | ~ v1_funct_1(E_732)
      | ~ m1_pre_topc(D_735,A_734)
      | v2_struct_0(D_735)
      | ~ m1_pre_topc(C_733,A_734)
      | v2_struct_0(C_733)
      | ~ l1_pre_topc(B_731)
      | ~ v2_pre_topc(B_731)
      | v2_struct_0(B_731)
      | ~ l1_pre_topc(A_734)
      | ~ v2_pre_topc(A_734)
      | v2_struct_0(A_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1542,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
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
    inference(resolution,[status(thm)],[c_64,c_1537])).

tff(c_1546,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_94,c_92,c_88,c_84,c_80,c_78,c_74,c_72,c_70,c_66,c_221,c_681,c_520,c_1542])).

tff(c_1547,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_90,c_86,c_1546])).

tff(c_4,plain,(
    ! [D_4,C_3,A_1,B_2] :
      ( D_4 = C_3
      | ~ r2_funct_2(A_1,B_2,C_3,D_4)
      | ~ m1_subset_1(D_4,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(D_4,A_1,B_2)
      | ~ v1_funct_1(D_4)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2)))
      | ~ v1_funct_2(C_3,A_1,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1549,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1547,c_4])).

tff(c_1552,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_1549])).

tff(c_1553,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1552])).

tff(c_1556,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_685,c_1553])).

tff(c_1559,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_88,c_1556])).

tff(c_1560,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_1559])).

tff(c_1563,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1560])).

tff(c_1566,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_88,c_84,c_1563])).

tff(c_1568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_90,c_86,c_1566])).

tff(c_1569,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1552])).

tff(c_1571,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1569])).

tff(c_1577,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1571])).

tff(c_1584,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_94,c_92,c_88,c_221,c_681,c_520,c_1577])).

tff(c_1585,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_1584])).

tff(c_1588,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1585])).

tff(c_1591,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_88,c_84,c_1588])).

tff(c_1593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_90,c_86,c_1591])).

tff(c_1594,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1569])).

tff(c_1682,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1594])).

tff(c_1685,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_706,c_1682])).

tff(c_1688,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_88,c_1685])).

tff(c_1689,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_1688])).

tff(c_1692,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1689])).

tff(c_1695,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_88,c_84,c_1692])).

tff(c_1697,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_90,c_86,c_1695])).

tff(c_1698,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1594])).

tff(c_76,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_314])).

tff(c_1660,plain,(
    ! [C_739,D_741,A_740,F_742,E_738,B_737] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_740,C_739,D_741)),u1_struct_0(B_737),k3_tmap_1(A_740,B_737,C_739,k2_tsep_1(A_740,C_739,D_741),E_738),k3_tmap_1(A_740,B_737,D_741,k2_tsep_1(A_740,C_739,D_741),F_742))
      | r2_funct_2(u1_struct_0(D_741),u1_struct_0(B_737),k3_tmap_1(A_740,B_737,k1_tsep_1(A_740,C_739,D_741),D_741,k10_tmap_1(A_740,B_737,C_739,D_741,E_738,F_742)),F_742)
      | ~ m1_subset_1(k10_tmap_1(A_740,B_737,C_739,D_741,E_738,F_742),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_740,C_739,D_741)),u1_struct_0(B_737))))
      | ~ v1_funct_2(k10_tmap_1(A_740,B_737,C_739,D_741,E_738,F_742),u1_struct_0(k1_tsep_1(A_740,C_739,D_741)),u1_struct_0(B_737))
      | ~ v1_funct_1(k10_tmap_1(A_740,B_737,C_739,D_741,E_738,F_742))
      | ~ m1_subset_1(F_742,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_741),u1_struct_0(B_737))))
      | ~ v1_funct_2(F_742,u1_struct_0(D_741),u1_struct_0(B_737))
      | ~ v1_funct_1(F_742)
      | ~ m1_subset_1(E_738,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_739),u1_struct_0(B_737))))
      | ~ v1_funct_2(E_738,u1_struct_0(C_739),u1_struct_0(B_737))
      | ~ v1_funct_1(E_738)
      | ~ m1_pre_topc(D_741,A_740)
      | v2_struct_0(D_741)
      | ~ m1_pre_topc(C_739,A_740)
      | v2_struct_0(C_739)
      | ~ l1_pre_topc(B_737)
      | ~ v2_pre_topc(B_737)
      | v2_struct_0(B_737)
      | ~ l1_pre_topc(A_740)
      | ~ v2_pre_topc(A_740)
      | v2_struct_0(A_740) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1665,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
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
    inference(resolution,[status(thm)],[c_64,c_1660])).

tff(c_1669,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_94,c_92,c_88,c_84,c_80,c_78,c_74,c_72,c_70,c_66,c_221,c_681,c_520,c_1665])).

tff(c_1670,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_90,c_86,c_1669])).

tff(c_1674,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1670,c_4])).

tff(c_1681,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_1674])).

tff(c_1862,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1681])).

tff(c_1865,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_685,c_1862])).

tff(c_1868,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_84,c_1865])).

tff(c_1869,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_1868])).

tff(c_1872,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1869])).

tff(c_1875,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_88,c_84,c_1872])).

tff(c_1877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_90,c_86,c_1875])).

tff(c_1879,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1681])).

tff(c_1878,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1681])).

tff(c_1880,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1878])).

tff(c_1893,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1880])).

tff(c_1900,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_94,c_92,c_84,c_221,c_681,c_520,c_1893])).

tff(c_1901,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_1900])).

tff(c_1904,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1901])).

tff(c_1907,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_88,c_84,c_1904])).

tff(c_1909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_90,c_86,c_1907])).

tff(c_1911,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1878])).

tff(c_38,plain,(
    ! [C_170,A_146,E_176,D_174,B_162] :
      ( v5_pre_topc(E_176,k1_tsep_1(A_146,C_170,D_174),B_162)
      | ~ m1_subset_1(k3_tmap_1(A_146,B_162,k1_tsep_1(A_146,C_170,D_174),D_174,E_176),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_174),u1_struct_0(B_162))))
      | ~ v5_pre_topc(k3_tmap_1(A_146,B_162,k1_tsep_1(A_146,C_170,D_174),D_174,E_176),D_174,B_162)
      | ~ v1_funct_2(k3_tmap_1(A_146,B_162,k1_tsep_1(A_146,C_170,D_174),D_174,E_176),u1_struct_0(D_174),u1_struct_0(B_162))
      | ~ v1_funct_1(k3_tmap_1(A_146,B_162,k1_tsep_1(A_146,C_170,D_174),D_174,E_176))
      | ~ m1_subset_1(k3_tmap_1(A_146,B_162,k1_tsep_1(A_146,C_170,D_174),C_170,E_176),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_170),u1_struct_0(B_162))))
      | ~ v5_pre_topc(k3_tmap_1(A_146,B_162,k1_tsep_1(A_146,C_170,D_174),C_170,E_176),C_170,B_162)
      | ~ v1_funct_2(k3_tmap_1(A_146,B_162,k1_tsep_1(A_146,C_170,D_174),C_170,E_176),u1_struct_0(C_170),u1_struct_0(B_162))
      | ~ v1_funct_1(k3_tmap_1(A_146,B_162,k1_tsep_1(A_146,C_170,D_174),C_170,E_176))
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_146,C_170,D_174)),u1_struct_0(B_162))))
      | ~ v1_funct_2(E_176,u1_struct_0(k1_tsep_1(A_146,C_170,D_174)),u1_struct_0(B_162))
      | ~ v1_funct_1(E_176)
      | ~ r4_tsep_1(A_146,C_170,D_174)
      | ~ m1_pre_topc(D_174,A_146)
      | v2_struct_0(D_174)
      | ~ m1_pre_topc(C_170,A_146)
      | v2_struct_0(C_170)
      | ~ l1_pre_topc(B_162)
      | ~ v2_pre_topc(B_162)
      | v2_struct_0(B_162)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_1913,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_3','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_1911,c_38])).

tff(c_1938,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_94,c_92,c_88,c_84,c_62,c_221,c_681,c_520,c_80,c_1698,c_78,c_1698,c_76,c_1698,c_74,c_1698,c_1879,c_1913])).

tff(c_1939,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_96,c_90,c_86,c_680,c_1938])).

tff(c_1982,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1939])).

tff(c_1985,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_706,c_1982])).

tff(c_1988,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_98,c_84,c_1985])).

tff(c_1989,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_1988])).

tff(c_1992,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_1989])).

tff(c_1995,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_88,c_84,c_1992])).

tff(c_1997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_90,c_86,c_1995])).

tff(c_1999,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1939])).

tff(c_1910,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1878])).

tff(c_2037,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1999,c_1910])).

tff(c_1998,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1939])).

tff(c_2039,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2037,c_1998])).

tff(c_2046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2039])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.57/2.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.66  
% 7.57/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.67  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.57/2.67  
% 7.57/2.67  %Foreground sorts:
% 7.57/2.67  
% 7.57/2.67  
% 7.57/2.67  %Background operators:
% 7.57/2.67  
% 7.57/2.67  
% 7.57/2.67  %Foreground operators:
% 7.57/2.67  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.57/2.67  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.57/2.67  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.57/2.67  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.57/2.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.57/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.57/2.67  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.57/2.67  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 7.57/2.67  tff('#skF_5', type, '#skF_5': $i).
% 7.57/2.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.57/2.67  tff('#skF_6', type, '#skF_6': $i).
% 7.57/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.57/2.67  tff('#skF_3', type, '#skF_3': $i).
% 7.57/2.67  tff('#skF_1', type, '#skF_1': $i).
% 7.57/2.67  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.57/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.57/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.57/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.57/2.67  tff('#skF_4', type, '#skF_4': $i).
% 7.57/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.57/2.67  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.57/2.67  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.57/2.67  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 7.57/2.67  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.57/2.67  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 7.57/2.67  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.57/2.67  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.57/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.57/2.67  
% 7.93/2.72  tff(f_314, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_tmap_1)).
% 7.93/2.72  tff(f_163, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 7.93/2.72  tff(f_141, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 7.93/2.72  tff(f_193, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 7.93/2.72  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r1_tsep_1(C, D) | r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((G = k10_tmap_1(A, B, C, D, E, F)) <=> (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, G), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, G), F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_tmap_1)).
% 7.93/2.72  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.93/2.72  tff(f_253, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_tmap_1)).
% 7.93/2.72  tff(c_68, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_102, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_90, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_86, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_98, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_88, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_84, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_24, plain, (![A_138, B_139, C_140]: (m1_pre_topc(k1_tsep_1(A_138, B_139, C_140), A_138) | ~m1_pre_topc(C_140, A_138) | v2_struct_0(C_140) | ~m1_pre_topc(B_139, A_138) | v2_struct_0(B_139) | ~l1_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_163])).
% 7.93/2.72  tff(c_100, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_96, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_94, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_92, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_78, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_74, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_70, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_671, plain, (![C_432, D_436, F_435, B_433, A_431, E_434]: (v1_funct_2(k10_tmap_1(A_431, B_433, C_432, D_436, E_434, F_435), u1_struct_0(k1_tsep_1(A_431, C_432, D_436)), u1_struct_0(B_433)) | ~m1_subset_1(F_435, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_436), u1_struct_0(B_433)))) | ~v1_funct_2(F_435, u1_struct_0(D_436), u1_struct_0(B_433)) | ~v1_funct_1(F_435) | ~m1_subset_1(E_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_432), u1_struct_0(B_433)))) | ~v1_funct_2(E_434, u1_struct_0(C_432), u1_struct_0(B_433)) | ~v1_funct_1(E_434) | ~m1_pre_topc(D_436, A_431) | v2_struct_0(D_436) | ~m1_pre_topc(C_432, A_431) | v2_struct_0(C_432) | ~l1_pre_topc(B_433) | ~v2_pre_topc(B_433) | v2_struct_0(B_433) | ~l1_pre_topc(A_431) | ~v2_pre_topc(A_431) | v2_struct_0(A_431))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.93/2.72  tff(c_469, plain, (![C_381, A_380, F_384, D_385, E_383, B_382]: (m1_subset_1(k10_tmap_1(A_380, B_382, C_381, D_385, E_383, F_384), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_380, C_381, D_385)), u1_struct_0(B_382)))) | ~m1_subset_1(F_384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_385), u1_struct_0(B_382)))) | ~v1_funct_2(F_384, u1_struct_0(D_385), u1_struct_0(B_382)) | ~v1_funct_1(F_384) | ~m1_subset_1(E_383, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_381), u1_struct_0(B_382)))) | ~v1_funct_2(E_383, u1_struct_0(C_381), u1_struct_0(B_382)) | ~v1_funct_1(E_383) | ~m1_pre_topc(D_385, A_380) | v2_struct_0(D_385) | ~m1_pre_topc(C_381, A_380) | v2_struct_0(C_381) | ~l1_pre_topc(B_382) | ~v2_pre_topc(B_382) | v2_struct_0(B_382) | ~l1_pre_topc(A_380) | ~v2_pre_topc(A_380) | v2_struct_0(A_380))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.93/2.72  tff(c_174, plain, (![F_277, D_278, C_274, B_275, A_273, E_276]: (v1_funct_1(k10_tmap_1(A_273, B_275, C_274, D_278, E_276, F_277)) | ~m1_subset_1(F_277, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_278), u1_struct_0(B_275)))) | ~v1_funct_2(F_277, u1_struct_0(D_278), u1_struct_0(B_275)) | ~v1_funct_1(F_277) | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_274), u1_struct_0(B_275)))) | ~v1_funct_2(E_276, u1_struct_0(C_274), u1_struct_0(B_275)) | ~v1_funct_1(E_276) | ~m1_pre_topc(D_278, A_273) | v2_struct_0(D_278) | ~m1_pre_topc(C_274, A_273) | v2_struct_0(C_274) | ~l1_pre_topc(B_275) | ~v2_pre_topc(B_275) | v2_struct_0(B_275) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.93/2.72  tff(c_178, plain, (![A_273, C_274, E_276]: (v1_funct_1(k10_tmap_1(A_273, '#skF_2', C_274, '#skF_4', E_276, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_274), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_276, u1_struct_0(C_274), u1_struct_0('#skF_2')) | ~v1_funct_1(E_276) | ~m1_pre_topc('#skF_4', A_273) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_274, A_273) | v2_struct_0(C_274) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(resolution, [status(thm)], [c_66, c_174])).
% 7.93/2.72  tff(c_184, plain, (![A_273, C_274, E_276]: (v1_funct_1(k10_tmap_1(A_273, '#skF_2', C_274, '#skF_4', E_276, '#skF_6')) | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_274), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_276, u1_struct_0(C_274), u1_struct_0('#skF_2')) | ~v1_funct_1(E_276) | ~m1_pre_topc('#skF_4', A_273) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_274, A_273) | v2_struct_0(C_274) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_72, c_70, c_178])).
% 7.93/2.72  tff(c_190, plain, (![A_279, C_280, E_281]: (v1_funct_1(k10_tmap_1(A_279, '#skF_2', C_280, '#skF_4', E_281, '#skF_6')) | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_280), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_281, u1_struct_0(C_280), u1_struct_0('#skF_2')) | ~v1_funct_1(E_281) | ~m1_pre_topc('#skF_4', A_279) | ~m1_pre_topc(C_280, A_279) | v2_struct_0(C_280) | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279))), inference(negUnitSimplification, [status(thm)], [c_96, c_86, c_184])).
% 7.93/2.72  tff(c_197, plain, (![A_279]: (v1_funct_1(k10_tmap_1(A_279, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_279) | ~m1_pre_topc('#skF_3', A_279) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279))), inference(resolution, [status(thm)], [c_74, c_190])).
% 7.93/2.72  tff(c_208, plain, (![A_279]: (v1_funct_1(k10_tmap_1(A_279, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_279) | ~m1_pre_topc('#skF_3', A_279) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_279) | ~v2_pre_topc(A_279) | v2_struct_0(A_279))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_197])).
% 7.93/2.72  tff(c_211, plain, (![A_283]: (v1_funct_1(k10_tmap_1(A_283, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_283) | ~m1_pre_topc('#skF_3', A_283) | ~l1_pre_topc(A_283) | ~v2_pre_topc(A_283) | v2_struct_0(A_283))), inference(negUnitSimplification, [status(thm)], [c_90, c_208])).
% 7.93/2.72  tff(c_60, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_146, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_60])).
% 7.93/2.72  tff(c_214, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_211, c_146])).
% 7.93/2.72  tff(c_217, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_88, c_84, c_214])).
% 7.93/2.72  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_217])).
% 7.93/2.72  tff(c_220, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_60])).
% 7.93/2.72  tff(c_237, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_220])).
% 7.93/2.72  tff(c_492, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_469, c_237])).
% 7.93/2.72  tff(c_516, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_94, c_92, c_88, c_84, c_80, c_78, c_74, c_72, c_70, c_66, c_492])).
% 7.93/2.72  tff(c_518, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_90, c_86, c_516])).
% 7.93/2.72  tff(c_519, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_220])).
% 7.93/2.72  tff(c_538, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_519])).
% 7.93/2.72  tff(c_674, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_671, c_538])).
% 7.93/2.72  tff(c_677, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_94, c_92, c_88, c_84, c_80, c_78, c_74, c_72, c_70, c_66, c_674])).
% 7.93/2.72  tff(c_679, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_90, c_86, c_677])).
% 7.93/2.72  tff(c_681, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_519])).
% 7.93/2.72  tff(c_221, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_60])).
% 7.93/2.72  tff(c_520, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_220])).
% 7.93/2.72  tff(c_32, plain, (![C_143, A_141, D_144, E_145, B_142]: (v1_funct_2(k3_tmap_1(A_141, B_142, C_143, D_144, E_145), u1_struct_0(D_144), u1_struct_0(B_142)) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0(B_142)))) | ~v1_funct_2(E_145, u1_struct_0(C_143), u1_struct_0(B_142)) | ~v1_funct_1(E_145) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(C_143, A_141) | ~l1_pre_topc(B_142) | ~v2_pre_topc(B_142) | v2_struct_0(B_142) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.93/2.72  tff(c_522, plain, (![A_141, D_144]: (v1_funct_2(k3_tmap_1(A_141, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_144, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_144), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_141) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_520, c_32])).
% 7.93/2.72  tff(c_529, plain, (![A_141, D_144]: (v1_funct_2(k3_tmap_1(A_141, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_144, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_144), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_141) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_221, c_522])).
% 7.93/2.72  tff(c_530, plain, (![A_141, D_144]: (v1_funct_2(k3_tmap_1(A_141, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_144, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_144), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(negUnitSimplification, [status(thm)], [c_96, c_529])).
% 7.93/2.72  tff(c_706, plain, (![A_141, D_144]: (v1_funct_2(k3_tmap_1(A_141, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_144, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_144), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_681, c_530])).
% 7.93/2.72  tff(c_680, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_519])).
% 7.93/2.72  tff(c_62, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_30, plain, (![C_143, A_141, D_144, E_145, B_142]: (m1_subset_1(k3_tmap_1(A_141, B_142, C_143, D_144, E_145), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_144), u1_struct_0(B_142)))) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0(B_142)))) | ~v1_funct_2(E_145, u1_struct_0(C_143), u1_struct_0(B_142)) | ~v1_funct_1(E_145) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(C_143, A_141) | ~l1_pre_topc(B_142) | ~v2_pre_topc(B_142) | v2_struct_0(B_142) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.93/2.72  tff(c_34, plain, (![C_143, A_141, D_144, E_145, B_142]: (v1_funct_1(k3_tmap_1(A_141, B_142, C_143, D_144, E_145)) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0(B_142)))) | ~v1_funct_2(E_145, u1_struct_0(C_143), u1_struct_0(B_142)) | ~v1_funct_1(E_145) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(C_143, A_141) | ~l1_pre_topc(B_142) | ~v2_pre_topc(B_142) | v2_struct_0(B_142) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_193])).
% 7.93/2.72  tff(c_524, plain, (![A_141, D_144]: (v1_funct_1(k3_tmap_1(A_141, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_144, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_141) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(resolution, [status(thm)], [c_520, c_34])).
% 7.93/2.72  tff(c_533, plain, (![A_141, D_144]: (v1_funct_1(k3_tmap_1(A_141, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_144, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_141) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_221, c_524])).
% 7.93/2.72  tff(c_534, plain, (![A_141, D_144]: (v1_funct_1(k3_tmap_1(A_141, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_144, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(negUnitSimplification, [status(thm)], [c_96, c_533])).
% 7.93/2.72  tff(c_685, plain, (![A_141, D_144]: (v1_funct_1(k3_tmap_1(A_141, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_144, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_144, A_141) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_141) | ~l1_pre_topc(A_141) | ~v2_pre_topc(A_141) | v2_struct_0(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_681, c_534])).
% 7.93/2.72  tff(c_64, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_1537, plain, (![F_736, D_735, A_734, C_733, E_732, B_731]: (~r2_funct_2(u1_struct_0(k2_tsep_1(A_734, C_733, D_735)), u1_struct_0(B_731), k3_tmap_1(A_734, B_731, C_733, k2_tsep_1(A_734, C_733, D_735), E_732), k3_tmap_1(A_734, B_731, D_735, k2_tsep_1(A_734, C_733, D_735), F_736)) | r2_funct_2(u1_struct_0(C_733), u1_struct_0(B_731), k3_tmap_1(A_734, B_731, k1_tsep_1(A_734, C_733, D_735), C_733, k10_tmap_1(A_734, B_731, C_733, D_735, E_732, F_736)), E_732) | ~m1_subset_1(k10_tmap_1(A_734, B_731, C_733, D_735, E_732, F_736), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_734, C_733, D_735)), u1_struct_0(B_731)))) | ~v1_funct_2(k10_tmap_1(A_734, B_731, C_733, D_735, E_732, F_736), u1_struct_0(k1_tsep_1(A_734, C_733, D_735)), u1_struct_0(B_731)) | ~v1_funct_1(k10_tmap_1(A_734, B_731, C_733, D_735, E_732, F_736)) | ~m1_subset_1(F_736, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_735), u1_struct_0(B_731)))) | ~v1_funct_2(F_736, u1_struct_0(D_735), u1_struct_0(B_731)) | ~v1_funct_1(F_736) | ~m1_subset_1(E_732, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_733), u1_struct_0(B_731)))) | ~v1_funct_2(E_732, u1_struct_0(C_733), u1_struct_0(B_731)) | ~v1_funct_1(E_732) | ~m1_pre_topc(D_735, A_734) | v2_struct_0(D_735) | ~m1_pre_topc(C_733, A_734) | v2_struct_0(C_733) | ~l1_pre_topc(B_731) | ~v2_pre_topc(B_731) | v2_struct_0(B_731) | ~l1_pre_topc(A_734) | ~v2_pre_topc(A_734) | v2_struct_0(A_734))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.93/2.72  tff(c_1542, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_1537])).
% 7.93/2.72  tff(c_1546, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_94, c_92, c_88, c_84, c_80, c_78, c_74, c_72, c_70, c_66, c_221, c_681, c_520, c_1542])).
% 7.93/2.72  tff(c_1547, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_90, c_86, c_1546])).
% 7.93/2.72  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.93/2.72  tff(c_1549, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1547, c_4])).
% 7.93/2.72  tff(c_1552, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_74, c_1549])).
% 7.93/2.72  tff(c_1553, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1552])).
% 7.93/2.72  tff(c_1556, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_685, c_1553])).
% 7.93/2.72  tff(c_1559, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_88, c_1556])).
% 7.93/2.72  tff(c_1560, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_102, c_1559])).
% 7.93/2.72  tff(c_1563, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1560])).
% 7.93/2.72  tff(c_1566, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_88, c_84, c_1563])).
% 7.93/2.72  tff(c_1568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_90, c_86, c_1566])).
% 7.93/2.72  tff(c_1569, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1552])).
% 7.93/2.72  tff(c_1571, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1569])).
% 7.93/2.72  tff(c_1577, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1571])).
% 7.93/2.72  tff(c_1584, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_94, c_92, c_88, c_221, c_681, c_520, c_1577])).
% 7.93/2.72  tff(c_1585, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_1584])).
% 7.93/2.72  tff(c_1588, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1585])).
% 7.93/2.72  tff(c_1591, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_88, c_84, c_1588])).
% 7.93/2.72  tff(c_1593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_90, c_86, c_1591])).
% 7.93/2.72  tff(c_1594, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1569])).
% 7.93/2.72  tff(c_1682, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1594])).
% 7.93/2.72  tff(c_1685, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_706, c_1682])).
% 7.93/2.72  tff(c_1688, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_88, c_1685])).
% 7.93/2.72  tff(c_1689, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_102, c_1688])).
% 7.93/2.72  tff(c_1692, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1689])).
% 7.93/2.72  tff(c_1695, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_88, c_84, c_1692])).
% 7.93/2.72  tff(c_1697, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_90, c_86, c_1695])).
% 7.93/2.72  tff(c_1698, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1594])).
% 7.93/2.72  tff(c_76, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_314])).
% 7.93/2.72  tff(c_1660, plain, (![C_739, D_741, A_740, F_742, E_738, B_737]: (~r2_funct_2(u1_struct_0(k2_tsep_1(A_740, C_739, D_741)), u1_struct_0(B_737), k3_tmap_1(A_740, B_737, C_739, k2_tsep_1(A_740, C_739, D_741), E_738), k3_tmap_1(A_740, B_737, D_741, k2_tsep_1(A_740, C_739, D_741), F_742)) | r2_funct_2(u1_struct_0(D_741), u1_struct_0(B_737), k3_tmap_1(A_740, B_737, k1_tsep_1(A_740, C_739, D_741), D_741, k10_tmap_1(A_740, B_737, C_739, D_741, E_738, F_742)), F_742) | ~m1_subset_1(k10_tmap_1(A_740, B_737, C_739, D_741, E_738, F_742), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_740, C_739, D_741)), u1_struct_0(B_737)))) | ~v1_funct_2(k10_tmap_1(A_740, B_737, C_739, D_741, E_738, F_742), u1_struct_0(k1_tsep_1(A_740, C_739, D_741)), u1_struct_0(B_737)) | ~v1_funct_1(k10_tmap_1(A_740, B_737, C_739, D_741, E_738, F_742)) | ~m1_subset_1(F_742, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_741), u1_struct_0(B_737)))) | ~v1_funct_2(F_742, u1_struct_0(D_741), u1_struct_0(B_737)) | ~v1_funct_1(F_742) | ~m1_subset_1(E_738, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_739), u1_struct_0(B_737)))) | ~v1_funct_2(E_738, u1_struct_0(C_739), u1_struct_0(B_737)) | ~v1_funct_1(E_738) | ~m1_pre_topc(D_741, A_740) | v2_struct_0(D_741) | ~m1_pre_topc(C_739, A_740) | v2_struct_0(C_739) | ~l1_pre_topc(B_737) | ~v2_pre_topc(B_737) | v2_struct_0(B_737) | ~l1_pre_topc(A_740) | ~v2_pre_topc(A_740) | v2_struct_0(A_740))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.93/2.72  tff(c_1665, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_64, c_1660])).
% 7.93/2.72  tff(c_1669, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_94, c_92, c_88, c_84, c_80, c_78, c_74, c_72, c_70, c_66, c_221, c_681, c_520, c_1665])).
% 7.93/2.72  tff(c_1670, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_90, c_86, c_1669])).
% 7.93/2.72  tff(c_1674, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1670, c_4])).
% 7.93/2.72  tff(c_1681, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_1674])).
% 7.93/2.72  tff(c_1862, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1681])).
% 7.93/2.72  tff(c_1865, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_685, c_1862])).
% 7.93/2.72  tff(c_1868, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_84, c_1865])).
% 7.93/2.72  tff(c_1869, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_102, c_1868])).
% 7.93/2.72  tff(c_1872, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1869])).
% 7.93/2.72  tff(c_1875, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_88, c_84, c_1872])).
% 7.93/2.72  tff(c_1877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_90, c_86, c_1875])).
% 7.93/2.72  tff(c_1879, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_1681])).
% 7.93/2.72  tff(c_1878, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1681])).
% 7.93/2.72  tff(c_1880, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1878])).
% 7.93/2.72  tff(c_1893, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1880])).
% 7.93/2.72  tff(c_1900, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_94, c_92, c_84, c_221, c_681, c_520, c_1893])).
% 7.93/2.72  tff(c_1901, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_1900])).
% 7.93/2.72  tff(c_1904, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1901])).
% 7.93/2.72  tff(c_1907, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_88, c_84, c_1904])).
% 7.93/2.72  tff(c_1909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_90, c_86, c_1907])).
% 7.93/2.72  tff(c_1911, plain, (m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1878])).
% 7.93/2.72  tff(c_38, plain, (![C_170, A_146, E_176, D_174, B_162]: (v5_pre_topc(E_176, k1_tsep_1(A_146, C_170, D_174), B_162) | ~m1_subset_1(k3_tmap_1(A_146, B_162, k1_tsep_1(A_146, C_170, D_174), D_174, E_176), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_174), u1_struct_0(B_162)))) | ~v5_pre_topc(k3_tmap_1(A_146, B_162, k1_tsep_1(A_146, C_170, D_174), D_174, E_176), D_174, B_162) | ~v1_funct_2(k3_tmap_1(A_146, B_162, k1_tsep_1(A_146, C_170, D_174), D_174, E_176), u1_struct_0(D_174), u1_struct_0(B_162)) | ~v1_funct_1(k3_tmap_1(A_146, B_162, k1_tsep_1(A_146, C_170, D_174), D_174, E_176)) | ~m1_subset_1(k3_tmap_1(A_146, B_162, k1_tsep_1(A_146, C_170, D_174), C_170, E_176), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_170), u1_struct_0(B_162)))) | ~v5_pre_topc(k3_tmap_1(A_146, B_162, k1_tsep_1(A_146, C_170, D_174), C_170, E_176), C_170, B_162) | ~v1_funct_2(k3_tmap_1(A_146, B_162, k1_tsep_1(A_146, C_170, D_174), C_170, E_176), u1_struct_0(C_170), u1_struct_0(B_162)) | ~v1_funct_1(k3_tmap_1(A_146, B_162, k1_tsep_1(A_146, C_170, D_174), C_170, E_176)) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_146, C_170, D_174)), u1_struct_0(B_162)))) | ~v1_funct_2(E_176, u1_struct_0(k1_tsep_1(A_146, C_170, D_174)), u1_struct_0(B_162)) | ~v1_funct_1(E_176) | ~r4_tsep_1(A_146, C_170, D_174) | ~m1_pre_topc(D_174, A_146) | v2_struct_0(D_174) | ~m1_pre_topc(C_170, A_146) | v2_struct_0(C_170) | ~l1_pre_topc(B_162) | ~v2_pre_topc(B_162) | v2_struct_0(B_162) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_253])).
% 7.93/2.72  tff(c_1913, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1911, c_38])).
% 7.93/2.72  tff(c_1938, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_94, c_92, c_88, c_84, c_62, c_221, c_681, c_520, c_80, c_1698, c_78, c_1698, c_76, c_1698, c_74, c_1698, c_1879, c_1913])).
% 7.93/2.72  tff(c_1939, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_102, c_96, c_90, c_86, c_680, c_1938])).
% 7.93/2.72  tff(c_1982, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1939])).
% 7.93/2.72  tff(c_1985, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_706, c_1982])).
% 7.93/2.72  tff(c_1988, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_100, c_98, c_84, c_1985])).
% 7.93/2.72  tff(c_1989, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_102, c_1988])).
% 7.93/2.72  tff(c_1992, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1989])).
% 7.93/2.72  tff(c_1995, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_88, c_84, c_1992])).
% 7.93/2.72  tff(c_1997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_90, c_86, c_1995])).
% 7.93/2.72  tff(c_1999, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1939])).
% 7.93/2.72  tff(c_1910, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1878])).
% 7.93/2.72  tff(c_2037, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1999, c_1910])).
% 7.93/2.72  tff(c_1998, plain, (~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2')), inference(splitRight, [status(thm)], [c_1939])).
% 7.93/2.72  tff(c_2039, plain, (~v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2037, c_1998])).
% 7.93/2.72  tff(c_2046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2039])).
% 7.93/2.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.93/2.72  
% 7.93/2.72  Inference rules
% 7.93/2.72  ----------------------
% 7.93/2.72  #Ref     : 0
% 7.93/2.72  #Sup     : 330
% 7.93/2.72  #Fact    : 0
% 7.93/2.72  #Define  : 0
% 7.93/2.72  #Split   : 11
% 7.93/2.72  #Chain   : 0
% 7.93/2.72  #Close   : 0
% 7.93/2.72  
% 7.93/2.72  Ordering : KBO
% 7.93/2.72  
% 7.93/2.72  Simplification rules
% 7.93/2.72  ----------------------
% 7.93/2.72  #Subsume      : 46
% 7.93/2.72  #Demod        : 936
% 7.93/2.72  #Tautology    : 25
% 7.93/2.72  #SimpNegUnit  : 186
% 7.93/2.72  #BackRed      : 8
% 7.93/2.72  
% 7.93/2.72  #Partial instantiations: 0
% 7.93/2.72  #Strategies tried      : 1
% 7.93/2.72  
% 7.93/2.72  Timing (in seconds)
% 7.93/2.72  ----------------------
% 7.93/2.72  Preprocessing        : 0.57
% 7.93/2.72  Parsing              : 0.31
% 7.93/2.72  CNF conversion       : 0.08
% 7.93/2.72  Main loop            : 1.26
% 7.93/2.72  Inferencing          : 0.43
% 7.93/2.72  Reduction            : 0.36
% 7.93/2.72  Demodulation         : 0.27
% 7.93/2.72  BG Simplification    : 0.06
% 7.93/2.73  Subsumption          : 0.37
% 7.93/2.73  Abstraction          : 0.05
% 7.93/2.73  MUC search           : 0.00
% 7.93/2.73  Cooper               : 0.00
% 7.93/2.73  Total                : 1.91
% 7.93/2.73  Index Insertion      : 0.00
% 7.93/2.73  Index Deletion       : 0.00
% 7.93/2.73  Index Matching       : 0.00
% 7.93/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
