%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:10 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.91s
% Verified   : 
% Statistics : Number of formulae       :  173 (1458 expanded)
%              Number of leaves         :   35 ( 581 expanded)
%              Depth                    :   19
%              Number of atoms          :  786 (15894 expanded)
%              Number of equality atoms :   13 ( 100 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_327,negated_conjecture,(
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

tff(f_266,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_262,axiom,(
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
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,A) )
                 => ( ( m1_pre_topc(B,C)
                      & m1_pre_topc(D,C) )
                   => m1_pre_topc(k1_tsep_1(A,B,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).

tff(f_171,axiom,(
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

tff(f_231,axiom,(
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

tff(c_100,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_98,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_96,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_92,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_90,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_86,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_82,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_78,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_76,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_68,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_687,plain,(
    ! [D_444,E_442,F_443,C_440,A_439,B_441] :
      ( v1_funct_2(k10_tmap_1(A_439,B_441,C_440,D_444,E_442,F_443),u1_struct_0(k1_tsep_1(A_439,C_440,D_444)),u1_struct_0(B_441))
      | ~ m1_subset_1(F_443,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_444),u1_struct_0(B_441))))
      | ~ v1_funct_2(F_443,u1_struct_0(D_444),u1_struct_0(B_441))
      | ~ v1_funct_1(F_443)
      | ~ m1_subset_1(E_442,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_440),u1_struct_0(B_441))))
      | ~ v1_funct_2(E_442,u1_struct_0(C_440),u1_struct_0(B_441))
      | ~ v1_funct_1(E_442)
      | ~ m1_pre_topc(D_444,A_439)
      | v2_struct_0(D_444)
      | ~ m1_pre_topc(C_440,A_439)
      | v2_struct_0(C_440)
      | ~ l1_pre_topc(B_441)
      | ~ v2_pre_topc(B_441)
      | v2_struct_0(B_441)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439)
      | v2_struct_0(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_487,plain,(
    ! [B_394,D_397,F_396,C_393,A_392,E_395] :
      ( m1_subset_1(k10_tmap_1(A_392,B_394,C_393,D_397,E_395,F_396),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_392,C_393,D_397)),u1_struct_0(B_394))))
      | ~ m1_subset_1(F_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_397),u1_struct_0(B_394))))
      | ~ v1_funct_2(F_396,u1_struct_0(D_397),u1_struct_0(B_394))
      | ~ v1_funct_1(F_396)
      | ~ m1_subset_1(E_395,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_393),u1_struct_0(B_394))))
      | ~ v1_funct_2(E_395,u1_struct_0(C_393),u1_struct_0(B_394))
      | ~ v1_funct_1(E_395)
      | ~ m1_pre_topc(D_397,A_392)
      | v2_struct_0(D_397)
      | ~ m1_pre_topc(C_393,A_392)
      | v2_struct_0(C_393)
      | ~ l1_pre_topc(B_394)
      | ~ v2_pre_topc(B_394)
      | v2_struct_0(B_394)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_171,plain,(
    ! [F_286,E_285,A_282,D_287,C_283,B_284] :
      ( v1_funct_1(k10_tmap_1(A_282,B_284,C_283,D_287,E_285,F_286))
      | ~ m1_subset_1(F_286,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_287),u1_struct_0(B_284))))
      | ~ v1_funct_2(F_286,u1_struct_0(D_287),u1_struct_0(B_284))
      | ~ v1_funct_1(F_286)
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_283),u1_struct_0(B_284))))
      | ~ v1_funct_2(E_285,u1_struct_0(C_283),u1_struct_0(B_284))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc(D_287,A_282)
      | v2_struct_0(D_287)
      | ~ m1_pre_topc(C_283,A_282)
      | v2_struct_0(C_283)
      | ~ l1_pre_topc(B_284)
      | ~ v2_pre_topc(B_284)
      | v2_struct_0(B_284)
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_177,plain,(
    ! [A_282,C_283,E_285] :
      ( v1_funct_1(k10_tmap_1(A_282,'#skF_2',C_283,'#skF_4',E_285,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_283),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_285,u1_struct_0(C_283),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc('#skF_4',A_282)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_283,A_282)
      | v2_struct_0(C_283)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(resolution,[status(thm)],[c_64,c_171])).

tff(c_185,plain,(
    ! [A_282,C_283,E_285] :
      ( v1_funct_1(k10_tmap_1(A_282,'#skF_2',C_283,'#skF_4',E_285,'#skF_6'))
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_283),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_285,u1_struct_0(C_283),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_285)
      | ~ m1_pre_topc('#skF_4',A_282)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_283,A_282)
      | v2_struct_0(C_283)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_70,c_68,c_177])).

tff(c_209,plain,(
    ! [A_293,C_294,E_295] :
      ( v1_funct_1(k10_tmap_1(A_293,'#skF_2',C_294,'#skF_4',E_295,'#skF_6'))
      | ~ m1_subset_1(E_295,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_294),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_295,u1_struct_0(C_294),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_295)
      | ~ m1_pre_topc('#skF_4',A_293)
      | ~ m1_pre_topc(C_294,A_293)
      | v2_struct_0(C_294)
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_84,c_185])).

tff(c_214,plain,(
    ! [A_293] :
      ( v1_funct_1(k10_tmap_1(A_293,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_293)
      | ~ m1_pre_topc('#skF_3',A_293)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(resolution,[status(thm)],[c_72,c_209])).

tff(c_223,plain,(
    ! [A_293] :
      ( v1_funct_1(k10_tmap_1(A_293,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_293)
      | ~ m1_pre_topc('#skF_3',A_293)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_293)
      | ~ v2_pre_topc(A_293)
      | v2_struct_0(A_293) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_214])).

tff(c_230,plain,(
    ! [A_297] :
      ( v1_funct_1(k10_tmap_1(A_297,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_297)
      | ~ m1_pre_topc('#skF_3',A_297)
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297)
      | v2_struct_0(A_297) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_223])).

tff(c_58,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_144,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_233,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_230,c_144])).

tff(c_236,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_82,c_233])).

tff(c_238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_236])).

tff(c_239,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_257,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_510,plain,
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
    inference(resolution,[status(thm)],[c_487,c_257])).

tff(c_534,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_86,c_82,c_78,c_76,c_72,c_70,c_68,c_64,c_510])).

tff(c_536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_84,c_534])).

tff(c_537,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_556,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_537])).

tff(c_690,plain,
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
    inference(resolution,[status(thm)],[c_687,c_556])).

tff(c_693,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_86,c_82,c_78,c_76,c_72,c_70,c_68,c_64,c_690])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_84,c_693])).

tff(c_696,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_537])).

tff(c_60,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_240,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_697,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_537])).

tff(c_538,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_56,plain,(
    ! [A_189] :
      ( m1_pre_topc(A_189,A_189)
      | ~ l1_pre_topc(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_54,plain,(
    ! [A_174,B_182,D_188,C_186] :
      ( m1_pre_topc(k1_tsep_1(A_174,B_182,D_188),C_186)
      | ~ m1_pre_topc(D_188,C_186)
      | ~ m1_pre_topc(B_182,C_186)
      | ~ m1_pre_topc(D_188,A_174)
      | v2_struct_0(D_188)
      | ~ m1_pre_topc(C_186,A_174)
      | v2_struct_0(C_186)
      | ~ m1_pre_topc(B_182,A_174)
      | v2_struct_0(B_182)
      | ~ l1_pre_topc(A_174)
      | ~ v2_pre_topc(A_174)
      | v2_struct_0(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_26,plain,(
    ! [C_140,D_141,A_138,E_142,B_139] :
      ( v1_funct_2(k3_tmap_1(A_138,B_139,C_140,D_141,E_142),u1_struct_0(D_141),u1_struct_0(B_139))
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_140),u1_struct_0(B_139))))
      | ~ v1_funct_2(E_142,u1_struct_0(C_140),u1_struct_0(B_139))
      | ~ v1_funct_1(E_142)
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(C_140,A_138)
      | ~ l1_pre_topc(B_139)
      | ~ v2_pre_topc(B_139)
      | v2_struct_0(B_139)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_540,plain,(
    ! [A_138,D_141] :
      ( v1_funct_2(k3_tmap_1(A_138,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_141,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_138)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_538,c_26])).

tff(c_547,plain,(
    ! [A_138,D_141] :
      ( v1_funct_2(k3_tmap_1(A_138,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_141,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_138)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_240,c_540])).

tff(c_548,plain,(
    ! [A_138,D_141] :
      ( v1_funct_2(k3_tmap_1(A_138,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_141,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_141),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_547])).

tff(c_720,plain,(
    ! [A_138,D_141] :
      ( v1_funct_2(k3_tmap_1(A_138,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_141,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_141),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_548])).

tff(c_24,plain,(
    ! [C_140,D_141,A_138,E_142,B_139] :
      ( m1_subset_1(k3_tmap_1(A_138,B_139,C_140,D_141,E_142),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_141),u1_struct_0(B_139))))
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_140),u1_struct_0(B_139))))
      | ~ v1_funct_2(E_142,u1_struct_0(C_140),u1_struct_0(B_139))
      | ~ v1_funct_1(E_142)
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(C_140,A_138)
      | ~ l1_pre_topc(B_139)
      | ~ v2_pre_topc(B_139)
      | v2_struct_0(B_139)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_28,plain,(
    ! [C_140,D_141,A_138,E_142,B_139] :
      ( v1_funct_1(k3_tmap_1(A_138,B_139,C_140,D_141,E_142))
      | ~ m1_subset_1(E_142,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_140),u1_struct_0(B_139))))
      | ~ v1_funct_2(E_142,u1_struct_0(C_140),u1_struct_0(B_139))
      | ~ v1_funct_1(E_142)
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(C_140,A_138)
      | ~ l1_pre_topc(B_139)
      | ~ v2_pre_topc(B_139)
      | v2_struct_0(B_139)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_542,plain,(
    ! [A_138,D_141] :
      ( v1_funct_1(k3_tmap_1(A_138,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_141,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_138)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_538,c_28])).

tff(c_551,plain,(
    ! [A_138,D_141] :
      ( v1_funct_1(k3_tmap_1(A_138,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_141,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_138)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_240,c_542])).

tff(c_552,plain,(
    ! [A_138,D_141] :
      ( v1_funct_1(k3_tmap_1(A_138,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_141,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_551])).

tff(c_707,plain,(
    ! [A_138,D_141] :
      ( v1_funct_1(k3_tmap_1(A_138,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_141,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_141,A_138)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_552])).

tff(c_62,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_1479,plain,(
    ! [B_736,C_738,A_739,F_741,E_737,D_740] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_739,C_738,D_740)),u1_struct_0(B_736),k3_tmap_1(A_739,B_736,C_738,k2_tsep_1(A_739,C_738,D_740),E_737),k3_tmap_1(A_739,B_736,D_740,k2_tsep_1(A_739,C_738,D_740),F_741))
      | r2_funct_2(u1_struct_0(C_738),u1_struct_0(B_736),k3_tmap_1(A_739,B_736,k1_tsep_1(A_739,C_738,D_740),C_738,k10_tmap_1(A_739,B_736,C_738,D_740,E_737,F_741)),E_737)
      | ~ m1_subset_1(k10_tmap_1(A_739,B_736,C_738,D_740,E_737,F_741),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_739,C_738,D_740)),u1_struct_0(B_736))))
      | ~ v1_funct_2(k10_tmap_1(A_739,B_736,C_738,D_740,E_737,F_741),u1_struct_0(k1_tsep_1(A_739,C_738,D_740)),u1_struct_0(B_736))
      | ~ v1_funct_1(k10_tmap_1(A_739,B_736,C_738,D_740,E_737,F_741))
      | ~ m1_subset_1(F_741,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_740),u1_struct_0(B_736))))
      | ~ v1_funct_2(F_741,u1_struct_0(D_740),u1_struct_0(B_736))
      | ~ v1_funct_1(F_741)
      | ~ m1_subset_1(E_737,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_738),u1_struct_0(B_736))))
      | ~ v1_funct_2(E_737,u1_struct_0(C_738),u1_struct_0(B_736))
      | ~ v1_funct_1(E_737)
      | ~ m1_pre_topc(D_740,A_739)
      | v2_struct_0(D_740)
      | ~ m1_pre_topc(C_738,A_739)
      | v2_struct_0(C_738)
      | ~ l1_pre_topc(B_736)
      | ~ v2_pre_topc(B_736)
      | v2_struct_0(B_736)
      | ~ l1_pre_topc(A_739)
      | ~ v2_pre_topc(A_739)
      | v2_struct_0(A_739) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1484,plain,
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
    inference(resolution,[status(thm)],[c_62,c_1479])).

tff(c_1488,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_86,c_82,c_78,c_76,c_72,c_70,c_68,c_64,c_240,c_697,c_538,c_1484])).

tff(c_1489,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_84,c_1488])).

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

tff(c_1491,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1489,c_4])).

tff(c_1494,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_72,c_1491])).

tff(c_1495,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1494])).

tff(c_1498,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_707,c_1495])).

tff(c_1501,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_1498])).

tff(c_1502,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1501])).

tff(c_1505,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1502])).

tff(c_1508,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_82,c_1505])).

tff(c_1509,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_88,c_84,c_1508])).

tff(c_1512,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1509])).

tff(c_1516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1512])).

tff(c_1517,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1494])).

tff(c_1519,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1517])).

tff(c_1525,plain,
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
    inference(resolution,[status(thm)],[c_24,c_1519])).

tff(c_1532,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_86,c_240,c_697,c_538,c_1525])).

tff(c_1533,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_1532])).

tff(c_1536,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1533])).

tff(c_1539,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_82,c_1536])).

tff(c_1540,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_88,c_84,c_1539])).

tff(c_1554,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1540])).

tff(c_1558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1554])).

tff(c_1559,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1517])).

tff(c_1614,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1559])).

tff(c_1618,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_720,c_1614])).

tff(c_1621,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_1618])).

tff(c_1622,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1621])).

tff(c_1625,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1622])).

tff(c_1628,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_82,c_1625])).

tff(c_1629,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_88,c_84,c_1628])).

tff(c_1632,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1629])).

tff(c_1636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1632])).

tff(c_1637,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1559])).

tff(c_74,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_1780,plain,(
    ! [E_749,F_753,A_751,D_752,B_748,C_750] :
      ( ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_751,C_750,D_752)),u1_struct_0(B_748),k3_tmap_1(A_751,B_748,C_750,k2_tsep_1(A_751,C_750,D_752),E_749),k3_tmap_1(A_751,B_748,D_752,k2_tsep_1(A_751,C_750,D_752),F_753))
      | r2_funct_2(u1_struct_0(D_752),u1_struct_0(B_748),k3_tmap_1(A_751,B_748,k1_tsep_1(A_751,C_750,D_752),D_752,k10_tmap_1(A_751,B_748,C_750,D_752,E_749,F_753)),F_753)
      | ~ m1_subset_1(k10_tmap_1(A_751,B_748,C_750,D_752,E_749,F_753),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_751,C_750,D_752)),u1_struct_0(B_748))))
      | ~ v1_funct_2(k10_tmap_1(A_751,B_748,C_750,D_752,E_749,F_753),u1_struct_0(k1_tsep_1(A_751,C_750,D_752)),u1_struct_0(B_748))
      | ~ v1_funct_1(k10_tmap_1(A_751,B_748,C_750,D_752,E_749,F_753))
      | ~ m1_subset_1(F_753,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_752),u1_struct_0(B_748))))
      | ~ v1_funct_2(F_753,u1_struct_0(D_752),u1_struct_0(B_748))
      | ~ v1_funct_1(F_753)
      | ~ m1_subset_1(E_749,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_750),u1_struct_0(B_748))))
      | ~ v1_funct_2(E_749,u1_struct_0(C_750),u1_struct_0(B_748))
      | ~ v1_funct_1(E_749)
      | ~ m1_pre_topc(D_752,A_751)
      | v2_struct_0(D_752)
      | ~ m1_pre_topc(C_750,A_751)
      | v2_struct_0(C_750)
      | ~ l1_pre_topc(B_748)
      | ~ v2_pre_topc(B_748)
      | v2_struct_0(B_748)
      | ~ l1_pre_topc(A_751)
      | ~ v2_pre_topc(A_751)
      | v2_struct_0(A_751) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1785,plain,
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
    inference(resolution,[status(thm)],[c_62,c_1780])).

tff(c_1789,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_86,c_82,c_78,c_76,c_72,c_70,c_68,c_64,c_240,c_697,c_538,c_1785])).

tff(c_1790,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_84,c_1789])).

tff(c_1794,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1790,c_4])).

tff(c_1801,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_1794])).

tff(c_1814,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1801])).

tff(c_1817,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_707,c_1814])).

tff(c_1820,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_82,c_1817])).

tff(c_1821,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1820])).

tff(c_1836,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1821])).

tff(c_1839,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_82,c_1836])).

tff(c_1840,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_88,c_84,c_1839])).

tff(c_1843,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1840])).

tff(c_1847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1843])).

tff(c_1848,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1801])).

tff(c_1852,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1848])).

tff(c_1858,plain,
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
    inference(resolution,[status(thm)],[c_24,c_1852])).

tff(c_1865,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_82,c_240,c_697,c_538,c_1858])).

tff(c_1866,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_1865])).

tff(c_1869,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1866])).

tff(c_1872,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_82,c_1869])).

tff(c_1873,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_88,c_84,c_1872])).

tff(c_1876,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1873])).

tff(c_1880,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1876])).

tff(c_1881,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1848])).

tff(c_1954,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1881])).

tff(c_1957,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_720,c_1954])).

tff(c_1960,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_82,c_1957])).

tff(c_1961,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_1960])).

tff(c_1964,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_1961])).

tff(c_1967,plain,
    ( v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_86,c_82,c_1964])).

tff(c_1968,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_88,c_84,c_1967])).

tff(c_1971,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_1968])).

tff(c_1975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1971])).

tff(c_1976,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1881])).

tff(c_66,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_327])).

tff(c_32,plain,(
    ! [E_173,B_159,A_143,D_171,C_167] :
      ( v5_pre_topc(E_173,k1_tsep_1(A_143,C_167,D_171),B_159)
      | ~ m1_subset_1(k3_tmap_1(A_143,B_159,k1_tsep_1(A_143,C_167,D_171),D_171,E_173),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_171),u1_struct_0(B_159))))
      | ~ v5_pre_topc(k3_tmap_1(A_143,B_159,k1_tsep_1(A_143,C_167,D_171),D_171,E_173),D_171,B_159)
      | ~ v1_funct_2(k3_tmap_1(A_143,B_159,k1_tsep_1(A_143,C_167,D_171),D_171,E_173),u1_struct_0(D_171),u1_struct_0(B_159))
      | ~ v1_funct_1(k3_tmap_1(A_143,B_159,k1_tsep_1(A_143,C_167,D_171),D_171,E_173))
      | ~ m1_subset_1(k3_tmap_1(A_143,B_159,k1_tsep_1(A_143,C_167,D_171),C_167,E_173),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_167),u1_struct_0(B_159))))
      | ~ v5_pre_topc(k3_tmap_1(A_143,B_159,k1_tsep_1(A_143,C_167,D_171),C_167,E_173),C_167,B_159)
      | ~ v1_funct_2(k3_tmap_1(A_143,B_159,k1_tsep_1(A_143,C_167,D_171),C_167,E_173),u1_struct_0(C_167),u1_struct_0(B_159))
      | ~ v1_funct_1(k3_tmap_1(A_143,B_159,k1_tsep_1(A_143,C_167,D_171),C_167,E_173))
      | ~ m1_subset_1(E_173,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_143,C_167,D_171)),u1_struct_0(B_159))))
      | ~ v1_funct_2(E_173,u1_struct_0(k1_tsep_1(A_143,C_167,D_171)),u1_struct_0(B_159))
      | ~ v1_funct_1(E_173)
      | ~ r4_tsep_1(A_143,C_167,D_171)
      | ~ m1_pre_topc(D_171,A_143)
      | v2_struct_0(D_171)
      | ~ m1_pre_topc(C_167,A_143)
      | v2_struct_0(C_167)
      | ~ l1_pre_topc(B_159)
      | ~ v2_pre_topc(B_159)
      | v2_struct_0(B_159)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_1986,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
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
    inference(superposition,[status(thm),theory(equality)],[c_1976,c_32])).

tff(c_2059,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_92,c_90,c_86,c_82,c_60,c_240,c_697,c_538,c_78,c_1637,c_76,c_1637,c_74,c_1637,c_72,c_1637,c_70,c_1976,c_68,c_1976,c_66,c_1976,c_64,c_1986])).

tff(c_2061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94,c_88,c_84,c_696,c_2059])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:43:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.52/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.52/2.65  
% 7.52/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.52/2.65  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.52/2.65  
% 7.52/2.65  %Foreground sorts:
% 7.52/2.65  
% 7.52/2.65  
% 7.52/2.65  %Background operators:
% 7.52/2.65  
% 7.52/2.65  
% 7.52/2.65  %Foreground operators:
% 7.52/2.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.52/2.65  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.52/2.65  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.52/2.65  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.52/2.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.52/2.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.52/2.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.52/2.65  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 7.52/2.65  tff('#skF_5', type, '#skF_5': $i).
% 7.52/2.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.52/2.65  tff('#skF_6', type, '#skF_6': $i).
% 7.52/2.65  tff('#skF_2', type, '#skF_2': $i).
% 7.52/2.65  tff('#skF_3', type, '#skF_3': $i).
% 7.52/2.65  tff('#skF_1', type, '#skF_1': $i).
% 7.52/2.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.52/2.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.52/2.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.52/2.65  tff('#skF_4', type, '#skF_4': $i).
% 7.52/2.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.52/2.65  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.52/2.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.52/2.65  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 7.52/2.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.52/2.65  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 7.52/2.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.52/2.65  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.52/2.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.52/2.65  
% 7.91/2.69  tff(f_327, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_tmap_1)).
% 7.91/2.69  tff(f_141, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 7.91/2.69  tff(f_266, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.91/2.69  tff(f_262, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, C) & m1_pre_topc(D, C)) => m1_pre_topc(k1_tsep_1(A, B, D), C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_tmap_1)).
% 7.91/2.69  tff(f_171, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 7.91/2.69  tff(f_99, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r1_tsep_1(C, D) | r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F))) => (![G]: (((v1_funct_1(G) & v1_funct_2(G, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(G, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((G = k10_tmap_1(A, B, C, D, E, F)) <=> (r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, G), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, G), F)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_tmap_1)).
% 7.91/2.69  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.91/2.69  tff(f_231, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_tmap_1)).
% 7.91/2.69  tff(c_100, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_94, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_88, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_84, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_98, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_96, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_92, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_90, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_86, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_82, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_78, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_76, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_68, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_687, plain, (![D_444, E_442, F_443, C_440, A_439, B_441]: (v1_funct_2(k10_tmap_1(A_439, B_441, C_440, D_444, E_442, F_443), u1_struct_0(k1_tsep_1(A_439, C_440, D_444)), u1_struct_0(B_441)) | ~m1_subset_1(F_443, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_444), u1_struct_0(B_441)))) | ~v1_funct_2(F_443, u1_struct_0(D_444), u1_struct_0(B_441)) | ~v1_funct_1(F_443) | ~m1_subset_1(E_442, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_440), u1_struct_0(B_441)))) | ~v1_funct_2(E_442, u1_struct_0(C_440), u1_struct_0(B_441)) | ~v1_funct_1(E_442) | ~m1_pre_topc(D_444, A_439) | v2_struct_0(D_444) | ~m1_pre_topc(C_440, A_439) | v2_struct_0(C_440) | ~l1_pre_topc(B_441) | ~v2_pre_topc(B_441) | v2_struct_0(B_441) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439) | v2_struct_0(A_439))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.91/2.69  tff(c_487, plain, (![B_394, D_397, F_396, C_393, A_392, E_395]: (m1_subset_1(k10_tmap_1(A_392, B_394, C_393, D_397, E_395, F_396), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_392, C_393, D_397)), u1_struct_0(B_394)))) | ~m1_subset_1(F_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_397), u1_struct_0(B_394)))) | ~v1_funct_2(F_396, u1_struct_0(D_397), u1_struct_0(B_394)) | ~v1_funct_1(F_396) | ~m1_subset_1(E_395, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_393), u1_struct_0(B_394)))) | ~v1_funct_2(E_395, u1_struct_0(C_393), u1_struct_0(B_394)) | ~v1_funct_1(E_395) | ~m1_pre_topc(D_397, A_392) | v2_struct_0(D_397) | ~m1_pre_topc(C_393, A_392) | v2_struct_0(C_393) | ~l1_pre_topc(B_394) | ~v2_pre_topc(B_394) | v2_struct_0(B_394) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.91/2.69  tff(c_171, plain, (![F_286, E_285, A_282, D_287, C_283, B_284]: (v1_funct_1(k10_tmap_1(A_282, B_284, C_283, D_287, E_285, F_286)) | ~m1_subset_1(F_286, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_287), u1_struct_0(B_284)))) | ~v1_funct_2(F_286, u1_struct_0(D_287), u1_struct_0(B_284)) | ~v1_funct_1(F_286) | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_283), u1_struct_0(B_284)))) | ~v1_funct_2(E_285, u1_struct_0(C_283), u1_struct_0(B_284)) | ~v1_funct_1(E_285) | ~m1_pre_topc(D_287, A_282) | v2_struct_0(D_287) | ~m1_pre_topc(C_283, A_282) | v2_struct_0(C_283) | ~l1_pre_topc(B_284) | ~v2_pre_topc(B_284) | v2_struct_0(B_284) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.91/2.69  tff(c_177, plain, (![A_282, C_283, E_285]: (v1_funct_1(k10_tmap_1(A_282, '#skF_2', C_283, '#skF_4', E_285, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_283), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_285, u1_struct_0(C_283), u1_struct_0('#skF_2')) | ~v1_funct_1(E_285) | ~m1_pre_topc('#skF_4', A_282) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_283, A_282) | v2_struct_0(C_283) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(resolution, [status(thm)], [c_64, c_171])).
% 7.91/2.69  tff(c_185, plain, (![A_282, C_283, E_285]: (v1_funct_1(k10_tmap_1(A_282, '#skF_2', C_283, '#skF_4', E_285, '#skF_6')) | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_283), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_285, u1_struct_0(C_283), u1_struct_0('#skF_2')) | ~v1_funct_1(E_285) | ~m1_pre_topc('#skF_4', A_282) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_283, A_282) | v2_struct_0(C_283) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_70, c_68, c_177])).
% 7.91/2.69  tff(c_209, plain, (![A_293, C_294, E_295]: (v1_funct_1(k10_tmap_1(A_293, '#skF_2', C_294, '#skF_4', E_295, '#skF_6')) | ~m1_subset_1(E_295, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_294), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_295, u1_struct_0(C_294), u1_struct_0('#skF_2')) | ~v1_funct_1(E_295) | ~m1_pre_topc('#skF_4', A_293) | ~m1_pre_topc(C_294, A_293) | v2_struct_0(C_294) | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(negUnitSimplification, [status(thm)], [c_94, c_84, c_185])).
% 7.91/2.69  tff(c_214, plain, (![A_293]: (v1_funct_1(k10_tmap_1(A_293, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_293) | ~m1_pre_topc('#skF_3', A_293) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(resolution, [status(thm)], [c_72, c_209])).
% 7.91/2.69  tff(c_223, plain, (![A_293]: (v1_funct_1(k10_tmap_1(A_293, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_293) | ~m1_pre_topc('#skF_3', A_293) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_293) | ~v2_pre_topc(A_293) | v2_struct_0(A_293))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_214])).
% 7.91/2.69  tff(c_230, plain, (![A_297]: (v1_funct_1(k10_tmap_1(A_297, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_297) | ~m1_pre_topc('#skF_3', A_297) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297) | v2_struct_0(A_297))), inference(negUnitSimplification, [status(thm)], [c_88, c_223])).
% 7.91/2.69  tff(c_58, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_144, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_58])).
% 7.91/2.69  tff(c_233, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_230, c_144])).
% 7.91/2.69  tff(c_236, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_86, c_82, c_233])).
% 7.91/2.69  tff(c_238, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_236])).
% 7.91/2.69  tff(c_239, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_58])).
% 7.91/2.69  tff(c_257, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_239])).
% 7.91/2.69  tff(c_510, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_487, c_257])).
% 7.91/2.69  tff(c_534, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_86, c_82, c_78, c_76, c_72, c_70, c_68, c_64, c_510])).
% 7.91/2.69  tff(c_536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_88, c_84, c_534])).
% 7.91/2.69  tff(c_537, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_239])).
% 7.91/2.69  tff(c_556, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_537])).
% 7.91/2.69  tff(c_690, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_687, c_556])).
% 7.91/2.69  tff(c_693, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_86, c_82, c_78, c_76, c_72, c_70, c_68, c_64, c_690])).
% 7.91/2.69  tff(c_695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_88, c_84, c_693])).
% 7.91/2.69  tff(c_696, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_537])).
% 7.91/2.69  tff(c_60, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_240, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_58])).
% 7.91/2.69  tff(c_697, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_537])).
% 7.91/2.69  tff(c_538, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_239])).
% 7.91/2.69  tff(c_56, plain, (![A_189]: (m1_pre_topc(A_189, A_189) | ~l1_pre_topc(A_189))), inference(cnfTransformation, [status(thm)], [f_266])).
% 7.91/2.69  tff(c_54, plain, (![A_174, B_182, D_188, C_186]: (m1_pre_topc(k1_tsep_1(A_174, B_182, D_188), C_186) | ~m1_pre_topc(D_188, C_186) | ~m1_pre_topc(B_182, C_186) | ~m1_pre_topc(D_188, A_174) | v2_struct_0(D_188) | ~m1_pre_topc(C_186, A_174) | v2_struct_0(C_186) | ~m1_pre_topc(B_182, A_174) | v2_struct_0(B_182) | ~l1_pre_topc(A_174) | ~v2_pre_topc(A_174) | v2_struct_0(A_174))), inference(cnfTransformation, [status(thm)], [f_262])).
% 7.91/2.69  tff(c_26, plain, (![C_140, D_141, A_138, E_142, B_139]: (v1_funct_2(k3_tmap_1(A_138, B_139, C_140, D_141, E_142), u1_struct_0(D_141), u1_struct_0(B_139)) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_140), u1_struct_0(B_139)))) | ~v1_funct_2(E_142, u1_struct_0(C_140), u1_struct_0(B_139)) | ~v1_funct_1(E_142) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(C_140, A_138) | ~l1_pre_topc(B_139) | ~v2_pre_topc(B_139) | v2_struct_0(B_139) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.91/2.69  tff(c_540, plain, (![A_138, D_141]: (v1_funct_2(k3_tmap_1(A_138, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_141, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_141), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_138) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_538, c_26])).
% 7.91/2.69  tff(c_547, plain, (![A_138, D_141]: (v1_funct_2(k3_tmap_1(A_138, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_141, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_141), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_138) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_240, c_540])).
% 7.91/2.69  tff(c_548, plain, (![A_138, D_141]: (v1_funct_2(k3_tmap_1(A_138, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_141, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_141), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(negUnitSimplification, [status(thm)], [c_94, c_547])).
% 7.91/2.69  tff(c_720, plain, (![A_138, D_141]: (v1_funct_2(k3_tmap_1(A_138, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_141, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_141), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_697, c_548])).
% 7.91/2.69  tff(c_24, plain, (![C_140, D_141, A_138, E_142, B_139]: (m1_subset_1(k3_tmap_1(A_138, B_139, C_140, D_141, E_142), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_141), u1_struct_0(B_139)))) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_140), u1_struct_0(B_139)))) | ~v1_funct_2(E_142, u1_struct_0(C_140), u1_struct_0(B_139)) | ~v1_funct_1(E_142) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(C_140, A_138) | ~l1_pre_topc(B_139) | ~v2_pre_topc(B_139) | v2_struct_0(B_139) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.91/2.69  tff(c_28, plain, (![C_140, D_141, A_138, E_142, B_139]: (v1_funct_1(k3_tmap_1(A_138, B_139, C_140, D_141, E_142)) | ~m1_subset_1(E_142, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_140), u1_struct_0(B_139)))) | ~v1_funct_2(E_142, u1_struct_0(C_140), u1_struct_0(B_139)) | ~v1_funct_1(E_142) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(C_140, A_138) | ~l1_pre_topc(B_139) | ~v2_pre_topc(B_139) | v2_struct_0(B_139) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_171])).
% 7.91/2.69  tff(c_542, plain, (![A_138, D_141]: (v1_funct_1(k3_tmap_1(A_138, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_141, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_138) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_538, c_28])).
% 7.91/2.69  tff(c_551, plain, (![A_138, D_141]: (v1_funct_1(k3_tmap_1(A_138, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_141, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_138) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_240, c_542])).
% 7.91/2.69  tff(c_552, plain, (![A_138, D_141]: (v1_funct_1(k3_tmap_1(A_138, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_141, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(negUnitSimplification, [status(thm)], [c_94, c_551])).
% 7.91/2.69  tff(c_707, plain, (![A_138, D_141]: (v1_funct_1(k3_tmap_1(A_138, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_141, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_141, A_138) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_697, c_552])).
% 7.91/2.69  tff(c_62, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_1479, plain, (![B_736, C_738, A_739, F_741, E_737, D_740]: (~r2_funct_2(u1_struct_0(k2_tsep_1(A_739, C_738, D_740)), u1_struct_0(B_736), k3_tmap_1(A_739, B_736, C_738, k2_tsep_1(A_739, C_738, D_740), E_737), k3_tmap_1(A_739, B_736, D_740, k2_tsep_1(A_739, C_738, D_740), F_741)) | r2_funct_2(u1_struct_0(C_738), u1_struct_0(B_736), k3_tmap_1(A_739, B_736, k1_tsep_1(A_739, C_738, D_740), C_738, k10_tmap_1(A_739, B_736, C_738, D_740, E_737, F_741)), E_737) | ~m1_subset_1(k10_tmap_1(A_739, B_736, C_738, D_740, E_737, F_741), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_739, C_738, D_740)), u1_struct_0(B_736)))) | ~v1_funct_2(k10_tmap_1(A_739, B_736, C_738, D_740, E_737, F_741), u1_struct_0(k1_tsep_1(A_739, C_738, D_740)), u1_struct_0(B_736)) | ~v1_funct_1(k10_tmap_1(A_739, B_736, C_738, D_740, E_737, F_741)) | ~m1_subset_1(F_741, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_740), u1_struct_0(B_736)))) | ~v1_funct_2(F_741, u1_struct_0(D_740), u1_struct_0(B_736)) | ~v1_funct_1(F_741) | ~m1_subset_1(E_737, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_738), u1_struct_0(B_736)))) | ~v1_funct_2(E_737, u1_struct_0(C_738), u1_struct_0(B_736)) | ~v1_funct_1(E_737) | ~m1_pre_topc(D_740, A_739) | v2_struct_0(D_740) | ~m1_pre_topc(C_738, A_739) | v2_struct_0(C_738) | ~l1_pre_topc(B_736) | ~v2_pre_topc(B_736) | v2_struct_0(B_736) | ~l1_pre_topc(A_739) | ~v2_pre_topc(A_739) | v2_struct_0(A_739))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.91/2.69  tff(c_1484, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_1479])).
% 7.91/2.69  tff(c_1488, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_86, c_82, c_78, c_76, c_72, c_70, c_68, c_64, c_240, c_697, c_538, c_1484])).
% 7.91/2.69  tff(c_1489, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_88, c_84, c_1488])).
% 7.91/2.69  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.91/2.69  tff(c_1491, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1489, c_4])).
% 7.91/2.69  tff(c_1494, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_72, c_1491])).
% 7.91/2.69  tff(c_1495, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1494])).
% 7.91/2.69  tff(c_1498, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_707, c_1495])).
% 7.91/2.69  tff(c_1501, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_86, c_1498])).
% 7.91/2.69  tff(c_1502, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_1501])).
% 7.91/2.69  tff(c_1505, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1502])).
% 7.91/2.69  tff(c_1508, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_86, c_82, c_1505])).
% 7.91/2.69  tff(c_1509, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_88, c_84, c_1508])).
% 7.91/2.69  tff(c_1512, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1509])).
% 7.91/2.69  tff(c_1516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_1512])).
% 7.91/2.69  tff(c_1517, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1494])).
% 7.91/2.69  tff(c_1519, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1517])).
% 7.91/2.69  tff(c_1525, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1519])).
% 7.91/2.69  tff(c_1532, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_86, c_240, c_697, c_538, c_1525])).
% 7.91/2.69  tff(c_1533, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_1532])).
% 7.91/2.69  tff(c_1536, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1533])).
% 7.91/2.69  tff(c_1539, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_86, c_82, c_1536])).
% 7.91/2.69  tff(c_1540, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_88, c_84, c_1539])).
% 7.91/2.69  tff(c_1554, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1540])).
% 7.91/2.69  tff(c_1558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_1554])).
% 7.91/2.69  tff(c_1559, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1517])).
% 7.91/2.69  tff(c_1614, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1559])).
% 7.91/2.69  tff(c_1618, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_720, c_1614])).
% 7.91/2.69  tff(c_1621, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_86, c_1618])).
% 7.91/2.69  tff(c_1622, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_1621])).
% 7.91/2.69  tff(c_1625, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1622])).
% 7.91/2.69  tff(c_1628, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_86, c_82, c_1625])).
% 7.91/2.69  tff(c_1629, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_88, c_84, c_1628])).
% 7.91/2.69  tff(c_1632, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1629])).
% 7.91/2.69  tff(c_1636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_1632])).
% 7.91/2.69  tff(c_1637, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1559])).
% 7.91/2.69  tff(c_74, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_1780, plain, (![E_749, F_753, A_751, D_752, B_748, C_750]: (~r2_funct_2(u1_struct_0(k2_tsep_1(A_751, C_750, D_752)), u1_struct_0(B_748), k3_tmap_1(A_751, B_748, C_750, k2_tsep_1(A_751, C_750, D_752), E_749), k3_tmap_1(A_751, B_748, D_752, k2_tsep_1(A_751, C_750, D_752), F_753)) | r2_funct_2(u1_struct_0(D_752), u1_struct_0(B_748), k3_tmap_1(A_751, B_748, k1_tsep_1(A_751, C_750, D_752), D_752, k10_tmap_1(A_751, B_748, C_750, D_752, E_749, F_753)), F_753) | ~m1_subset_1(k10_tmap_1(A_751, B_748, C_750, D_752, E_749, F_753), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_751, C_750, D_752)), u1_struct_0(B_748)))) | ~v1_funct_2(k10_tmap_1(A_751, B_748, C_750, D_752, E_749, F_753), u1_struct_0(k1_tsep_1(A_751, C_750, D_752)), u1_struct_0(B_748)) | ~v1_funct_1(k10_tmap_1(A_751, B_748, C_750, D_752, E_749, F_753)) | ~m1_subset_1(F_753, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_752), u1_struct_0(B_748)))) | ~v1_funct_2(F_753, u1_struct_0(D_752), u1_struct_0(B_748)) | ~v1_funct_1(F_753) | ~m1_subset_1(E_749, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_750), u1_struct_0(B_748)))) | ~v1_funct_2(E_749, u1_struct_0(C_750), u1_struct_0(B_748)) | ~v1_funct_1(E_749) | ~m1_pre_topc(D_752, A_751) | v2_struct_0(D_752) | ~m1_pre_topc(C_750, A_751) | v2_struct_0(C_750) | ~l1_pre_topc(B_748) | ~v2_pre_topc(B_748) | v2_struct_0(B_748) | ~l1_pre_topc(A_751) | ~v2_pre_topc(A_751) | v2_struct_0(A_751))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.91/2.69  tff(c_1785, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_1780])).
% 7.91/2.69  tff(c_1789, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_86, c_82, c_78, c_76, c_72, c_70, c_68, c_64, c_240, c_697, c_538, c_1785])).
% 7.91/2.69  tff(c_1790, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_88, c_84, c_1789])).
% 7.91/2.69  tff(c_1794, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1790, c_4])).
% 7.91/2.69  tff(c_1801, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_1794])).
% 7.91/2.69  tff(c_1814, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1801])).
% 7.91/2.69  tff(c_1817, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_707, c_1814])).
% 7.91/2.69  tff(c_1820, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_82, c_1817])).
% 7.91/2.69  tff(c_1821, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_1820])).
% 7.91/2.69  tff(c_1836, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1821])).
% 7.91/2.69  tff(c_1839, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_86, c_82, c_1836])).
% 7.91/2.69  tff(c_1840, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_88, c_84, c_1839])).
% 7.91/2.69  tff(c_1843, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1840])).
% 7.91/2.69  tff(c_1847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_1843])).
% 7.91/2.69  tff(c_1848, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1801])).
% 7.91/2.69  tff(c_1852, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1848])).
% 7.91/2.69  tff(c_1858, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_24, c_1852])).
% 7.91/2.69  tff(c_1865, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_82, c_240, c_697, c_538, c_1858])).
% 7.91/2.69  tff(c_1866, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_1865])).
% 7.91/2.69  tff(c_1869, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1866])).
% 7.91/2.69  tff(c_1872, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_86, c_82, c_1869])).
% 7.91/2.69  tff(c_1873, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_88, c_84, c_1872])).
% 7.91/2.69  tff(c_1876, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1873])).
% 7.91/2.69  tff(c_1880, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_1876])).
% 7.91/2.69  tff(c_1881, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1848])).
% 7.91/2.69  tff(c_1954, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1881])).
% 7.91/2.69  tff(c_1957, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_720, c_1954])).
% 7.91/2.69  tff(c_1960, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_82, c_1957])).
% 7.91/2.69  tff(c_1961, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_1960])).
% 7.91/2.69  tff(c_1964, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_1961])).
% 7.91/2.69  tff(c_1967, plain, (v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_86, c_82, c_1964])).
% 7.91/2.69  tff(c_1968, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_100, c_88, c_84, c_1967])).
% 7.91/2.69  tff(c_1971, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_1968])).
% 7.91/2.69  tff(c_1975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_1971])).
% 7.91/2.69  tff(c_1976, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1881])).
% 7.91/2.69  tff(c_66, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_327])).
% 7.91/2.69  tff(c_32, plain, (![E_173, B_159, A_143, D_171, C_167]: (v5_pre_topc(E_173, k1_tsep_1(A_143, C_167, D_171), B_159) | ~m1_subset_1(k3_tmap_1(A_143, B_159, k1_tsep_1(A_143, C_167, D_171), D_171, E_173), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_171), u1_struct_0(B_159)))) | ~v5_pre_topc(k3_tmap_1(A_143, B_159, k1_tsep_1(A_143, C_167, D_171), D_171, E_173), D_171, B_159) | ~v1_funct_2(k3_tmap_1(A_143, B_159, k1_tsep_1(A_143, C_167, D_171), D_171, E_173), u1_struct_0(D_171), u1_struct_0(B_159)) | ~v1_funct_1(k3_tmap_1(A_143, B_159, k1_tsep_1(A_143, C_167, D_171), D_171, E_173)) | ~m1_subset_1(k3_tmap_1(A_143, B_159, k1_tsep_1(A_143, C_167, D_171), C_167, E_173), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_167), u1_struct_0(B_159)))) | ~v5_pre_topc(k3_tmap_1(A_143, B_159, k1_tsep_1(A_143, C_167, D_171), C_167, E_173), C_167, B_159) | ~v1_funct_2(k3_tmap_1(A_143, B_159, k1_tsep_1(A_143, C_167, D_171), C_167, E_173), u1_struct_0(C_167), u1_struct_0(B_159)) | ~v1_funct_1(k3_tmap_1(A_143, B_159, k1_tsep_1(A_143, C_167, D_171), C_167, E_173)) | ~m1_subset_1(E_173, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_143, C_167, D_171)), u1_struct_0(B_159)))) | ~v1_funct_2(E_173, u1_struct_0(k1_tsep_1(A_143, C_167, D_171)), u1_struct_0(B_159)) | ~v1_funct_1(E_173) | ~r4_tsep_1(A_143, C_167, D_171) | ~m1_pre_topc(D_171, A_143) | v2_struct_0(D_171) | ~m1_pre_topc(C_167, A_143) | v2_struct_0(C_167) | ~l1_pre_topc(B_159) | ~v2_pre_topc(B_159) | v2_struct_0(B_159) | ~l1_pre_topc(A_143) | ~v2_pre_topc(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_231])).
% 7.91/2.69  tff(c_1986, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1976, c_32])).
% 7.91/2.69  tff(c_2059, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_92, c_90, c_86, c_82, c_60, c_240, c_697, c_538, c_78, c_1637, c_76, c_1637, c_74, c_1637, c_72, c_1637, c_70, c_1976, c_68, c_1976, c_66, c_1976, c_64, c_1986])).
% 7.91/2.69  tff(c_2061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_94, c_88, c_84, c_696, c_2059])).
% 7.91/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.91/2.69  
% 7.91/2.69  Inference rules
% 7.91/2.69  ----------------------
% 7.91/2.69  #Ref     : 0
% 7.91/2.69  #Sup     : 355
% 7.91/2.69  #Fact    : 0
% 7.91/2.69  #Define  : 0
% 7.91/2.69  #Split   : 12
% 7.91/2.69  #Chain   : 0
% 7.91/2.69  #Close   : 0
% 7.91/2.69  
% 7.91/2.69  Ordering : KBO
% 7.91/2.69  
% 7.91/2.69  Simplification rules
% 7.91/2.69  ----------------------
% 7.91/2.69  #Subsume      : 51
% 7.91/2.69  #Demod        : 963
% 7.91/2.69  #Tautology    : 38
% 7.91/2.69  #SimpNegUnit  : 170
% 7.91/2.69  #BackRed      : 6
% 7.91/2.69  
% 7.91/2.69  #Partial instantiations: 0
% 7.91/2.69  #Strategies tried      : 1
% 7.91/2.69  
% 7.91/2.69  Timing (in seconds)
% 7.91/2.69  ----------------------
% 7.91/2.69  Preprocessing        : 0.60
% 7.91/2.69  Parsing              : 0.31
% 7.91/2.69  CNF conversion       : 0.09
% 7.91/2.69  Main loop            : 1.21
% 7.91/2.69  Inferencing          : 0.39
% 7.91/2.69  Reduction            : 0.33
% 7.91/2.69  Demodulation         : 0.25
% 7.91/2.69  BG Simplification    : 0.06
% 7.91/2.69  Subsumption          : 0.37
% 7.91/2.69  Abstraction          : 0.05
% 7.91/2.69  MUC search           : 0.00
% 7.91/2.69  Cooper               : 0.00
% 7.91/2.69  Total                : 1.88
% 7.91/2.69  Index Insertion      : 0.00
% 7.91/2.69  Index Deletion       : 0.00
% 8.03/2.69  Index Matching       : 0.00
% 8.03/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
