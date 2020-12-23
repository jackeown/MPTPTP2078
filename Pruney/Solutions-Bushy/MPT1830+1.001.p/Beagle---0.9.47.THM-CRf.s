%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1830+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:29 EST 2020

% Result     : Theorem 6.32s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :  172 (1962 expanded)
%              Number of leaves         :   35 ( 823 expanded)
%              Depth                    :   18
%              Number of atoms          :  819 (23474 expanded)
%              Number of equality atoms :   12 ( 125 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > v1_borsuk_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_309,negated_conjecture,(
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
                  & v1_borsuk_1(C,A)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_borsuk_1(D,A)
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
                             => ( r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F))
                               => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                  & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                  & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                  & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_tmap_1)).

tff(f_66,axiom,(
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

tff(f_118,axiom,(
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

tff(f_88,axiom,(
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

tff(f_246,axiom,(
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
                 => ( ~ r1_tsep_1(C,D)
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                       => ! [F] :
                            ( ( v1_funct_1(F)
                              & v1_funct_2(F,u1_struct_0(D),u1_struct_0(B))
                              & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                           => ( ( r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,k10_tmap_1(A,B,C,D,E,F)),E)
                                & r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,k10_tmap_1(A,B,C,D,E,F)),F) )
                            <=> r2_funct_2(u1_struct_0(k2_tsep_1(A,C,D)),u1_struct_0(B),k3_tmap_1(A,B,C,k2_tsep_1(A,C,D),E),k3_tmap_1(A,B,D,k2_tsep_1(A,C,D),F)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_tmap_1)).

tff(f_134,axiom,(
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

tff(f_196,axiom,(
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
                & v1_borsuk_1(C,A)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_borsuk_1(D,A)
                    & m1_pre_topc(D,A) )
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
                          & m1_subset_1(k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,E),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_tmap_1)).

tff(c_98,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_96,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_94,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_90,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_88,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_82,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_76,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_70,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_64,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_62,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_544,plain,(
    ! [B_345,A_347,D_344,C_346,F_342,E_343] :
      ( v1_funct_2(k10_tmap_1(A_347,B_345,C_346,D_344,E_343,F_342),u1_struct_0(k1_tsep_1(A_347,C_346,D_344)),u1_struct_0(B_345))
      | ~ m1_subset_1(F_342,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_344),u1_struct_0(B_345))))
      | ~ v1_funct_2(F_342,u1_struct_0(D_344),u1_struct_0(B_345))
      | ~ v1_funct_1(F_342)
      | ~ m1_subset_1(E_343,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_346),u1_struct_0(B_345))))
      | ~ v1_funct_2(E_343,u1_struct_0(C_346),u1_struct_0(B_345))
      | ~ v1_funct_1(E_343)
      | ~ m1_pre_topc(D_344,A_347)
      | v2_struct_0(D_344)
      | ~ m1_pre_topc(C_346,A_347)
      | v2_struct_0(C_346)
      | ~ l1_pre_topc(B_345)
      | ~ v2_pre_topc(B_345)
      | v2_struct_0(B_345)
      | ~ l1_pre_topc(A_347)
      | ~ v2_pre_topc(A_347)
      | v2_struct_0(A_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_170,plain,(
    ! [B_212,A_214,C_213,D_211,E_210,F_209] :
      ( v1_funct_1(k10_tmap_1(A_214,B_212,C_213,D_211,E_210,F_209))
      | ~ m1_subset_1(F_209,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_211),u1_struct_0(B_212))))
      | ~ v1_funct_2(F_209,u1_struct_0(D_211),u1_struct_0(B_212))
      | ~ v1_funct_1(F_209)
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_213),u1_struct_0(B_212))))
      | ~ v1_funct_2(E_210,u1_struct_0(C_213),u1_struct_0(B_212))
      | ~ v1_funct_1(E_210)
      | ~ m1_pre_topc(D_211,A_214)
      | v2_struct_0(D_211)
      | ~ m1_pre_topc(C_213,A_214)
      | v2_struct_0(C_213)
      | ~ l1_pre_topc(B_212)
      | ~ v2_pre_topc(B_212)
      | v2_struct_0(B_212)
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_174,plain,(
    ! [A_214,C_213,E_210] :
      ( v1_funct_1(k10_tmap_1(A_214,'#skF_2',C_213,'#skF_4',E_210,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_213),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_210,u1_struct_0(C_213),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_210)
      | ~ m1_pre_topc('#skF_4',A_214)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_213,A_214)
      | v2_struct_0(C_213)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(resolution,[status(thm)],[c_58,c_170])).

tff(c_180,plain,(
    ! [A_214,C_213,E_210] :
      ( v1_funct_1(k10_tmap_1(A_214,'#skF_2',C_213,'#skF_4',E_210,'#skF_6'))
      | ~ m1_subset_1(E_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_213),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_210,u1_struct_0(C_213),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_210)
      | ~ m1_pre_topc('#skF_4',A_214)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_213,A_214)
      | v2_struct_0(C_213)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_64,c_62,c_174])).

tff(c_186,plain,(
    ! [A_215,C_216,E_217] :
      ( v1_funct_1(k10_tmap_1(A_215,'#skF_2',C_216,'#skF_4',E_217,'#skF_6'))
      | ~ m1_subset_1(E_217,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_216),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_217,u1_struct_0(C_216),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_217)
      | ~ m1_pre_topc('#skF_4',A_215)
      | ~ m1_pre_topc(C_216,A_215)
      | v2_struct_0(C_216)
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_180])).

tff(c_193,plain,(
    ! [A_215] :
      ( v1_funct_1(k10_tmap_1(A_215,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_215)
      | ~ m1_pre_topc('#skF_3',A_215)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(resolution,[status(thm)],[c_66,c_186])).

tff(c_204,plain,(
    ! [A_215] :
      ( v1_funct_1(k10_tmap_1(A_215,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_215)
      | ~ m1_pre_topc('#skF_3',A_215)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_193])).

tff(c_207,plain,(
    ! [A_219] :
      ( v1_funct_1(k10_tmap_1(A_219,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_219)
      | ~ m1_pre_topc('#skF_3',A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_204])).

tff(c_54,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_129,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_210,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_207,c_129])).

tff(c_213,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_82,c_76,c_210])).

tff(c_215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_213])).

tff(c_217,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_355,plain,(
    ! [E_301,D_302,C_304,F_300,B_303,A_305] :
      ( m1_subset_1(k10_tmap_1(A_305,B_303,C_304,D_302,E_301,F_300),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_305,C_304,D_302)),u1_struct_0(B_303))))
      | ~ m1_subset_1(F_300,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_302),u1_struct_0(B_303))))
      | ~ v1_funct_2(F_300,u1_struct_0(D_302),u1_struct_0(B_303))
      | ~ v1_funct_1(F_300)
      | ~ m1_subset_1(E_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_304),u1_struct_0(B_303))))
      | ~ v1_funct_2(E_301,u1_struct_0(C_304),u1_struct_0(B_303))
      | ~ v1_funct_1(E_301)
      | ~ m1_pre_topc(D_302,A_305)
      | v2_struct_0(D_302)
      | ~ m1_pre_topc(C_304,A_305)
      | v2_struct_0(C_304)
      | ~ l1_pre_topc(B_303)
      | ~ v2_pre_topc(B_303)
      | v2_struct_0(B_303)
      | ~ l1_pre_topc(A_305)
      | ~ v2_pre_topc(A_305)
      | v2_struct_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_216,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_248,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_378,plain,
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
    inference(resolution,[status(thm)],[c_355,c_248])).

tff(c_402,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_90,c_88,c_82,c_76,c_72,c_70,c_66,c_64,c_62,c_58,c_378])).

tff(c_404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_86,c_80,c_402])).

tff(c_406,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_18,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] :
      ( v1_funct_1(k3_tmap_1(A_10,B_11,C_12,D_13,E_14))
      | ~ m1_subset_1(E_14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_12),u1_struct_0(B_11))))
      | ~ v1_funct_2(E_14,u1_struct_0(C_12),u1_struct_0(B_11))
      | ~ v1_funct_1(E_14)
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(C_12,A_10)
      | ~ l1_pre_topc(B_11)
      | ~ v2_pre_topc(B_11)
      | v2_struct_0(B_11)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_410,plain,(
    ! [A_10,D_13] :
      ( v1_funct_1(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_406,c_18])).

tff(c_419,plain,(
    ! [A_10,D_13] :
      ( v1_funct_1(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_217,c_410])).

tff(c_420,plain,(
    ! [A_10,D_13] :
      ( v1_funct_1(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_419])).

tff(c_424,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_420])).

tff(c_547,plain,
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
    inference(resolution,[status(thm)],[c_544,c_424])).

tff(c_550,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_90,c_88,c_82,c_76,c_72,c_70,c_66,c_64,c_62,c_58,c_547])).

tff(c_552,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_86,c_80,c_550])).

tff(c_554,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_405,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_556,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_405])).

tff(c_84,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_78,plain,(
    v1_borsuk_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_pre_topc(k1_tsep_1(A_7,B_8,C_9),A_7)
      | ~ m1_pre_topc(C_9,A_7)
      | v2_struct_0(C_9)
      | ~ m1_pre_topc(B_8,A_7)
      | v2_struct_0(B_8)
      | ~ l1_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] :
      ( v1_funct_2(k3_tmap_1(A_10,B_11,C_12,D_13,E_14),u1_struct_0(D_13),u1_struct_0(B_11))
      | ~ m1_subset_1(E_14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_12),u1_struct_0(B_11))))
      | ~ v1_funct_2(E_14,u1_struct_0(C_12),u1_struct_0(B_11))
      | ~ v1_funct_1(E_14)
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(C_12,A_10)
      | ~ l1_pre_topc(B_11)
      | ~ v2_pre_topc(B_11)
      | v2_struct_0(B_11)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_408,plain,(
    ! [A_10,D_13] :
      ( v1_funct_2(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_13),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_406,c_16])).

tff(c_415,plain,(
    ! [A_10,D_13] :
      ( v1_funct_2(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_13),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_217,c_408])).

tff(c_416,plain,(
    ! [A_10,D_13] :
      ( v1_funct_2(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_13),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_415])).

tff(c_559,plain,(
    ! [A_10,D_13] :
      ( v1_funct_2(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_13),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_554,c_416])).

tff(c_553,plain,(
    ! [A_10,D_13] :
      ( v1_funct_1(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(splitRight,[status(thm)],[c_420])).

tff(c_74,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_56,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_1168,plain,(
    ! [D_511,A_510,E_513,B_514,C_509,F_512] :
      ( r2_funct_2(u1_struct_0(C_509),u1_struct_0(B_514),k3_tmap_1(A_510,B_514,k1_tsep_1(A_510,C_509,D_511),C_509,k10_tmap_1(A_510,B_514,C_509,D_511,E_513,F_512)),E_513)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_510,C_509,D_511)),u1_struct_0(B_514),k3_tmap_1(A_510,B_514,C_509,k2_tsep_1(A_510,C_509,D_511),E_513),k3_tmap_1(A_510,B_514,D_511,k2_tsep_1(A_510,C_509,D_511),F_512))
      | ~ m1_subset_1(F_512,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_511),u1_struct_0(B_514))))
      | ~ v1_funct_2(F_512,u1_struct_0(D_511),u1_struct_0(B_514))
      | ~ v1_funct_1(F_512)
      | ~ m1_subset_1(E_513,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_509),u1_struct_0(B_514))))
      | ~ v1_funct_2(E_513,u1_struct_0(C_509),u1_struct_0(B_514))
      | ~ v1_funct_1(E_513)
      | r1_tsep_1(C_509,D_511)
      | ~ m1_pre_topc(D_511,A_510)
      | v2_struct_0(D_511)
      | ~ m1_pre_topc(C_509,A_510)
      | v2_struct_0(C_509)
      | ~ l1_pre_topc(B_514)
      | ~ v2_pre_topc(B_514)
      | v2_struct_0(B_514)
      | ~ l1_pre_topc(A_510)
      | ~ v2_pre_topc(A_510)
      | v2_struct_0(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_1173,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | r1_tsep_1('#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_56,c_1168])).

tff(c_1177,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_90,c_88,c_82,c_76,c_72,c_70,c_66,c_64,c_62,c_58,c_1173])).

tff(c_1178,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_86,c_80,c_74,c_1177])).

tff(c_22,plain,(
    ! [D_18,C_17,A_15,B_16] :
      ( D_18 = C_17
      | ~ r2_funct_2(A_15,B_16,C_17,D_18)
      | ~ m1_subset_1(D_18,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(D_18,A_15,B_16)
      | ~ v1_funct_1(D_18)
      | ~ m1_subset_1(C_17,k1_zfmisc_1(k2_zfmisc_1(A_15,B_16)))
      | ~ v1_funct_2(C_17,A_15,B_16)
      | ~ v1_funct_1(C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1180,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1178,c_22])).

tff(c_1183,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_1180])).

tff(c_1308,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1183])).

tff(c_1311,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_553,c_1308])).

tff(c_1314,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_82,c_1311])).

tff(c_1315,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1314])).

tff(c_1318,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1315])).

tff(c_1321,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_82,c_76,c_1318])).

tff(c_1323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_86,c_80,c_1321])).

tff(c_1325,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1183])).

tff(c_14,plain,(
    ! [B_11,A_10,C_12,E_14,D_13] :
      ( m1_subset_1(k3_tmap_1(A_10,B_11,C_12,D_13,E_14),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_13),u1_struct_0(B_11))))
      | ~ m1_subset_1(E_14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_12),u1_struct_0(B_11))))
      | ~ v1_funct_2(E_14,u1_struct_0(C_12),u1_struct_0(B_11))
      | ~ v1_funct_1(E_14)
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(C_12,A_10)
      | ~ l1_pre_topc(B_11)
      | ~ v2_pre_topc(B_11)
      | v2_struct_0(B_11)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1324,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1183])).

tff(c_1326,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1324])).

tff(c_1349,plain,
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
    inference(resolution,[status(thm)],[c_14,c_1326])).

tff(c_1356,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_90,c_88,c_82,c_217,c_554,c_406,c_1349])).

tff(c_1357,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_1356])).

tff(c_1360,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1357])).

tff(c_1363,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_82,c_76,c_1360])).

tff(c_1365,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_86,c_80,c_1363])).

tff(c_1367,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1324])).

tff(c_579,plain,(
    ! [C_361,B_360,E_358,F_357,A_362,D_359] :
      ( v1_funct_1(k10_tmap_1(A_362,B_360,C_361,D_359,E_358,F_357))
      | ~ m1_subset_1(F_357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_359),u1_struct_0(B_360))))
      | ~ v1_funct_2(F_357,u1_struct_0(D_359),u1_struct_0(B_360))
      | ~ v1_funct_1(F_357)
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_361),u1_struct_0(B_360))))
      | ~ v1_funct_2(E_358,u1_struct_0(C_361),u1_struct_0(B_360))
      | ~ v1_funct_1(E_358)
      | ~ m1_pre_topc(D_359,A_362)
      | v2_struct_0(D_359)
      | ~ m1_pre_topc(C_361,A_362)
      | v2_struct_0(C_361)
      | ~ l1_pre_topc(B_360)
      | ~ v2_pre_topc(B_360)
      | v2_struct_0(B_360)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_587,plain,(
    ! [A_362,C_361,E_358] :
      ( v1_funct_1(k10_tmap_1(A_362,'#skF_2',C_361,'#skF_3',E_358,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_361),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_358,u1_struct_0(C_361),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_358)
      | ~ m1_pre_topc('#skF_3',A_362)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_361,A_362)
      | v2_struct_0(C_361)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(resolution,[status(thm)],[c_66,c_579])).

tff(c_599,plain,(
    ! [A_362,C_361,E_358] :
      ( v1_funct_1(k10_tmap_1(A_362,'#skF_2',C_361,'#skF_3',E_358,'#skF_5'))
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_361),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_358,u1_struct_0(C_361),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_358)
      | ~ m1_pre_topc('#skF_3',A_362)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_361,A_362)
      | v2_struct_0(C_361)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_72,c_70,c_587])).

tff(c_600,plain,(
    ! [A_362,C_361,E_358] :
      ( v1_funct_1(k10_tmap_1(A_362,'#skF_2',C_361,'#skF_3',E_358,'#skF_5'))
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_361),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_358,u1_struct_0(C_361),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_358)
      | ~ m1_pre_topc('#skF_3',A_362)
      | ~ m1_pre_topc(C_361,A_362)
      | v2_struct_0(C_361)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_599])).

tff(c_1373,plain,(
    ! [A_362] :
      ( v1_funct_1(k10_tmap_1(A_362,'#skF_2','#skF_3','#skF_3',k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc('#skF_3',A_362)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(resolution,[status(thm)],[c_1367,c_600])).

tff(c_1393,plain,(
    ! [A_362] :
      ( v1_funct_1(k10_tmap_1(A_362,'#skF_2','#skF_3','#skF_3',k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_362)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1325,c_1373])).

tff(c_1394,plain,(
    ! [A_362] :
      ( v1_funct_1(k10_tmap_1(A_362,'#skF_2','#skF_3','#skF_3',k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_362)
      | ~ l1_pre_topc(A_362)
      | ~ v2_pre_topc(A_362)
      | v2_struct_0(A_362) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1393])).

tff(c_1414,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1394])).

tff(c_1417,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_559,c_1414])).

tff(c_1420,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_82,c_1417])).

tff(c_1421,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1420])).

tff(c_1424,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1421])).

tff(c_1427,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_82,c_76,c_1424])).

tff(c_1429,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_86,c_80,c_1427])).

tff(c_1431,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1394])).

tff(c_1366,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1324])).

tff(c_1452,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1431,c_1366])).

tff(c_68,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_1063,plain,(
    ! [C_503,B_508,D_505,A_504,E_507,F_506] :
      ( r2_funct_2(u1_struct_0(D_505),u1_struct_0(B_508),k3_tmap_1(A_504,B_508,k1_tsep_1(A_504,C_503,D_505),D_505,k10_tmap_1(A_504,B_508,C_503,D_505,E_507,F_506)),F_506)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_504,C_503,D_505)),u1_struct_0(B_508),k3_tmap_1(A_504,B_508,C_503,k2_tsep_1(A_504,C_503,D_505),E_507),k3_tmap_1(A_504,B_508,D_505,k2_tsep_1(A_504,C_503,D_505),F_506))
      | ~ m1_subset_1(F_506,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_505),u1_struct_0(B_508))))
      | ~ v1_funct_2(F_506,u1_struct_0(D_505),u1_struct_0(B_508))
      | ~ v1_funct_1(F_506)
      | ~ m1_subset_1(E_507,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_503),u1_struct_0(B_508))))
      | ~ v1_funct_2(E_507,u1_struct_0(C_503),u1_struct_0(B_508))
      | ~ v1_funct_1(E_507)
      | r1_tsep_1(C_503,D_505)
      | ~ m1_pre_topc(D_505,A_504)
      | v2_struct_0(D_505)
      | ~ m1_pre_topc(C_503,A_504)
      | v2_struct_0(C_503)
      | ~ l1_pre_topc(B_508)
      | ~ v2_pre_topc(B_508)
      | v2_struct_0(B_508)
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_1068,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | r1_tsep_1('#skF_3','#skF_4')
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
    inference(resolution,[status(thm)],[c_56,c_1063])).

tff(c_1072,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_90,c_88,c_82,c_76,c_72,c_70,c_66,c_64,c_62,c_58,c_1068])).

tff(c_1073,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_86,c_80,c_74,c_1072])).

tff(c_1075,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1073,c_22])).

tff(c_1078,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_58,c_1075])).

tff(c_1079,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1078])).

tff(c_1082,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_553,c_1079])).

tff(c_1085,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_76,c_1082])).

tff(c_1086,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1085])).

tff(c_1089,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1086])).

tff(c_1092,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_82,c_76,c_1089])).

tff(c_1094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_86,c_80,c_1092])).

tff(c_1095,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1078])).

tff(c_1097,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1095])).

tff(c_1103,plain,
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
    inference(resolution,[status(thm)],[c_14,c_1097])).

tff(c_1110,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_90,c_88,c_76,c_217,c_554,c_406,c_1103])).

tff(c_1111,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_1110])).

tff(c_1114,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1111])).

tff(c_1117,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_82,c_76,c_1114])).

tff(c_1119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_86,c_80,c_1117])).

tff(c_1120,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1095])).

tff(c_1184,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1120])).

tff(c_1187,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_559,c_1184])).

tff(c_1190,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_76,c_1187])).

tff(c_1191,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_1190])).

tff(c_1194,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1191])).

tff(c_1197,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_82,c_76,c_1194])).

tff(c_1199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_86,c_80,c_1197])).

tff(c_1200,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1120])).

tff(c_60,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_1541,plain,(
    ! [D_528,B_530,C_527,E_531,A_529] :
      ( v5_pre_topc(E_531,k1_tsep_1(A_529,C_527,D_528),B_530)
      | ~ m1_subset_1(k3_tmap_1(A_529,B_530,k1_tsep_1(A_529,C_527,D_528),D_528,E_531),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_528),u1_struct_0(B_530))))
      | ~ v5_pre_topc(k3_tmap_1(A_529,B_530,k1_tsep_1(A_529,C_527,D_528),D_528,E_531),D_528,B_530)
      | ~ v1_funct_2(k3_tmap_1(A_529,B_530,k1_tsep_1(A_529,C_527,D_528),D_528,E_531),u1_struct_0(D_528),u1_struct_0(B_530))
      | ~ v1_funct_1(k3_tmap_1(A_529,B_530,k1_tsep_1(A_529,C_527,D_528),D_528,E_531))
      | ~ m1_subset_1(k3_tmap_1(A_529,B_530,k1_tsep_1(A_529,C_527,D_528),C_527,E_531),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_527),u1_struct_0(B_530))))
      | ~ v5_pre_topc(k3_tmap_1(A_529,B_530,k1_tsep_1(A_529,C_527,D_528),C_527,E_531),C_527,B_530)
      | ~ v1_funct_2(k3_tmap_1(A_529,B_530,k1_tsep_1(A_529,C_527,D_528),C_527,E_531),u1_struct_0(C_527),u1_struct_0(B_530))
      | ~ v1_funct_1(k3_tmap_1(A_529,B_530,k1_tsep_1(A_529,C_527,D_528),C_527,E_531))
      | ~ m1_subset_1(E_531,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_529,C_527,D_528)),u1_struct_0(B_530))))
      | ~ v1_funct_2(E_531,u1_struct_0(k1_tsep_1(A_529,C_527,D_528)),u1_struct_0(B_530))
      | ~ v1_funct_1(E_531)
      | ~ m1_pre_topc(D_528,A_529)
      | ~ v1_borsuk_1(D_528,A_529)
      | v2_struct_0(D_528)
      | ~ m1_pre_topc(C_527,A_529)
      | ~ v1_borsuk_1(C_527,A_529)
      | v2_struct_0(C_527)
      | ~ l1_pre_topc(B_530)
      | ~ v2_pre_topc(B_530)
      | v2_struct_0(B_530)
      | ~ l1_pre_topc(A_529)
      | ~ v2_pre_topc(A_529)
      | v2_struct_0(A_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1543,plain,
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
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1200,c_1541])).

tff(c_1553,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_90,c_88,c_84,c_82,c_78,c_76,c_217,c_554,c_406,c_72,c_1452,c_70,c_1452,c_68,c_1452,c_66,c_1452,c_64,c_1200,c_62,c_1200,c_60,c_1200,c_58,c_1543])).

tff(c_1555,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_92,c_86,c_80,c_556,c_1553])).

%------------------------------------------------------------------------------
