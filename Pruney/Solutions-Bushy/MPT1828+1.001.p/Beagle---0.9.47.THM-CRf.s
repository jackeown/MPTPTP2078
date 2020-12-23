%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1828+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:29 EST 2020

% Result     : Theorem 6.23s
% Output     : CNFRefutation 6.57s
% Verified   : 
% Statistics : Number of formulae       :  170 (1865 expanded)
%              Number of leaves         :   35 ( 788 expanded)
%              Depth                    :   18
%              Number of atoms          :  806 (21630 expanded)
%              Number of equality atoms :   12 ( 125 expanded)
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

tff(f_305,negated_conjecture,(
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

tff(f_244,axiom,(
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

tff(f_194,axiom,(
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

tff(c_96,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_94,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_92,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_88,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_86,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_82,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_78,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_72,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_64,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_628,plain,(
    ! [E_368,C_371,A_372,B_370,F_367,D_369] :
      ( v1_funct_2(k10_tmap_1(A_372,B_370,C_371,D_369,E_368,F_367),u1_struct_0(k1_tsep_1(A_372,C_371,D_369)),u1_struct_0(B_370))
      | ~ m1_subset_1(F_367,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_369),u1_struct_0(B_370))))
      | ~ v1_funct_2(F_367,u1_struct_0(D_369),u1_struct_0(B_370))
      | ~ v1_funct_1(F_367)
      | ~ m1_subset_1(E_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_371),u1_struct_0(B_370))))
      | ~ v1_funct_2(E_368,u1_struct_0(C_371),u1_struct_0(B_370))
      | ~ v1_funct_1(E_368)
      | ~ m1_pre_topc(D_369,A_372)
      | v2_struct_0(D_369)
      | ~ m1_pre_topc(C_371,A_372)
      | v2_struct_0(C_371)
      | ~ l1_pre_topc(B_370)
      | ~ v2_pre_topc(B_370)
      | v2_struct_0(B_370)
      | ~ l1_pre_topc(A_372)
      | ~ v2_pre_topc(A_372)
      | v2_struct_0(A_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_412,plain,(
    ! [D_313,E_312,C_315,F_311,B_314,A_316] :
      ( m1_subset_1(k10_tmap_1(A_316,B_314,C_315,D_313,E_312,F_311),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_316,C_315,D_313)),u1_struct_0(B_314))))
      | ~ m1_subset_1(F_311,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_313),u1_struct_0(B_314))))
      | ~ v1_funct_2(F_311,u1_struct_0(D_313),u1_struct_0(B_314))
      | ~ v1_funct_1(F_311)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_315),u1_struct_0(B_314))))
      | ~ v1_funct_2(E_312,u1_struct_0(C_315),u1_struct_0(B_314))
      | ~ v1_funct_1(E_312)
      | ~ m1_pre_topc(D_313,A_316)
      | v2_struct_0(D_313)
      | ~ m1_pre_topc(C_315,A_316)
      | v2_struct_0(C_315)
      | ~ l1_pre_topc(B_314)
      | ~ v2_pre_topc(B_314)
      | v2_struct_0(B_314)
      | ~ l1_pre_topc(A_316)
      | ~ v2_pre_topc(A_316)
      | v2_struct_0(A_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_168,plain,(
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

tff(c_172,plain,(
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
    inference(resolution,[status(thm)],[c_60,c_168])).

tff(c_178,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_66,c_64,c_172])).

tff(c_184,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_178])).

tff(c_191,plain,(
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
    inference(resolution,[status(thm)],[c_68,c_184])).

tff(c_202,plain,(
    ! [A_215] :
      ( v1_funct_1(k10_tmap_1(A_215,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_215)
      | ~ m1_pre_topc('#skF_3',A_215)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_215)
      | ~ v2_pre_topc(A_215)
      | v2_struct_0(A_215) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_191])).

tff(c_205,plain,(
    ! [A_219] :
      ( v1_funct_1(k10_tmap_1(A_219,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_219)
      | ~ m1_pre_topc('#skF_3',A_219)
      | ~ l1_pre_topc(A_219)
      | ~ v2_pre_topc(A_219)
      | v2_struct_0(A_219) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_202])).

tff(c_54,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_140,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_208,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_205,c_140])).

tff(c_211,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_208])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_211])).

tff(c_214,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_218,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_437,plain,
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
    inference(resolution,[status(thm)],[c_412,c_218])).

tff(c_460,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_437])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_460])).

tff(c_463,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_476,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_631,plain,
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
    inference(resolution,[status(thm)],[c_628,c_476])).

tff(c_634,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_631])).

tff(c_636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_634])).

tff(c_637,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_56,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_215,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_638,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_464,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_214])).

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

tff(c_647,plain,(
    ! [D_376,A_375,E_374,C_377,B_373] :
      ( v1_funct_2(k3_tmap_1(A_375,B_373,C_377,D_376,E_374),u1_struct_0(D_376),u1_struct_0(B_373))
      | ~ m1_subset_1(E_374,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_377),u1_struct_0(B_373))))
      | ~ v1_funct_2(E_374,u1_struct_0(C_377),u1_struct_0(B_373))
      | ~ v1_funct_1(E_374)
      | ~ m1_pre_topc(D_376,A_375)
      | ~ m1_pre_topc(C_377,A_375)
      | ~ l1_pre_topc(B_373)
      | ~ v2_pre_topc(B_373)
      | v2_struct_0(B_373)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_649,plain,(
    ! [A_375,D_376] :
      ( v1_funct_2(k3_tmap_1(A_375,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_376,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_376),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_376,A_375)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_375)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(resolution,[status(thm)],[c_464,c_647])).

tff(c_656,plain,(
    ! [A_375,D_376] :
      ( v1_funct_2(k3_tmap_1(A_375,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_376,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_376),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_376,A_375)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_375)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_215,c_638,c_649])).

tff(c_657,plain,(
    ! [A_375,D_376] :
      ( v1_funct_2(k3_tmap_1(A_375,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_376,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_376),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_376,A_375)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_375)
      | ~ l1_pre_topc(A_375)
      | ~ v2_pre_topc(A_375)
      | v2_struct_0(A_375) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_656])).

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

tff(c_466,plain,(
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
    inference(resolution,[status(thm)],[c_464,c_18])).

tff(c_471,plain,(
    ! [A_10,D_13] :
      ( v1_funct_1(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_215,c_466])).

tff(c_472,plain,(
    ! [A_10,D_13] :
      ( v1_funct_1(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_471])).

tff(c_670,plain,(
    ! [A_10,D_13] :
      ( v1_funct_1(k3_tmap_1(A_10,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_13,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_13,A_10)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_10)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_472])).

tff(c_76,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_58,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_1086,plain,(
    ! [F_492,E_493,B_494,D_491,C_489,A_490] :
      ( r2_funct_2(u1_struct_0(C_489),u1_struct_0(B_494),k3_tmap_1(A_490,B_494,k1_tsep_1(A_490,C_489,D_491),C_489,k10_tmap_1(A_490,B_494,C_489,D_491,E_493,F_492)),E_493)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_490,C_489,D_491)),u1_struct_0(B_494),k3_tmap_1(A_490,B_494,C_489,k2_tsep_1(A_490,C_489,D_491),E_493),k3_tmap_1(A_490,B_494,D_491,k2_tsep_1(A_490,C_489,D_491),F_492))
      | ~ m1_subset_1(F_492,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_491),u1_struct_0(B_494))))
      | ~ v1_funct_2(F_492,u1_struct_0(D_491),u1_struct_0(B_494))
      | ~ v1_funct_1(F_492)
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_489),u1_struct_0(B_494))))
      | ~ v1_funct_2(E_493,u1_struct_0(C_489),u1_struct_0(B_494))
      | ~ v1_funct_1(E_493)
      | r1_tsep_1(C_489,D_491)
      | ~ m1_pre_topc(D_491,A_490)
      | v2_struct_0(D_491)
      | ~ m1_pre_topc(C_489,A_490)
      | v2_struct_0(C_489)
      | ~ l1_pre_topc(B_494)
      | ~ v2_pre_topc(B_494)
      | v2_struct_0(B_494)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1091,plain,
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
    inference(resolution,[status(thm)],[c_58,c_1086])).

tff(c_1095,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_1091])).

tff(c_1096,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_76,c_1095])).

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

tff(c_1098,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1096,c_22])).

tff(c_1101,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1098])).

tff(c_1167,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1101])).

tff(c_1181,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_670,c_1167])).

tff(c_1184,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_1181])).

tff(c_1185,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1184])).

tff(c_1188,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1185])).

tff(c_1191,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1188])).

tff(c_1193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1191])).

tff(c_1194,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1101])).

tff(c_1204,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1194])).

tff(c_1210,plain,
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
    inference(resolution,[status(thm)],[c_14,c_1204])).

tff(c_1217,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_215,c_638,c_464,c_1210])).

tff(c_1218,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_1217])).

tff(c_1221,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1218])).

tff(c_1224,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1221])).

tff(c_1226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1224])).

tff(c_1227,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1194])).

tff(c_1275,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1227])).

tff(c_1289,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_657,c_1275])).

tff(c_1292,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_1289])).

tff(c_1293,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1292])).

tff(c_1296,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1293])).

tff(c_1299,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1296])).

tff(c_1301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1299])).

tff(c_1302,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1227])).

tff(c_70,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_1388,plain,(
    ! [F_540,D_539,A_538,E_541,C_537,B_542] :
      ( r2_funct_2(u1_struct_0(D_539),u1_struct_0(B_542),k3_tmap_1(A_538,B_542,k1_tsep_1(A_538,C_537,D_539),D_539,k10_tmap_1(A_538,B_542,C_537,D_539,E_541,F_540)),F_540)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_538,C_537,D_539)),u1_struct_0(B_542),k3_tmap_1(A_538,B_542,C_537,k2_tsep_1(A_538,C_537,D_539),E_541),k3_tmap_1(A_538,B_542,D_539,k2_tsep_1(A_538,C_537,D_539),F_540))
      | ~ m1_subset_1(F_540,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_539),u1_struct_0(B_542))))
      | ~ v1_funct_2(F_540,u1_struct_0(D_539),u1_struct_0(B_542))
      | ~ v1_funct_1(F_540)
      | ~ m1_subset_1(E_541,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_537),u1_struct_0(B_542))))
      | ~ v1_funct_2(E_541,u1_struct_0(C_537),u1_struct_0(B_542))
      | ~ v1_funct_1(E_541)
      | r1_tsep_1(C_537,D_539)
      | ~ m1_pre_topc(D_539,A_538)
      | v2_struct_0(D_539)
      | ~ m1_pre_topc(C_537,A_538)
      | v2_struct_0(C_537)
      | ~ l1_pre_topc(B_542)
      | ~ v2_pre_topc(B_542)
      | v2_struct_0(B_542)
      | ~ l1_pre_topc(A_538)
      | ~ v2_pre_topc(A_538)
      | v2_struct_0(A_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1393,plain,
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
    inference(resolution,[status(thm)],[c_58,c_1388])).

tff(c_1397,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_1393])).

tff(c_1398,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_76,c_1397])).

tff(c_1400,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1398,c_22])).

tff(c_1403,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1400])).

tff(c_1416,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1403])).

tff(c_1419,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_670,c_1416])).

tff(c_1422,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_78,c_1419])).

tff(c_1423,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1422])).

tff(c_1426,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1423])).

tff(c_1429,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1426])).

tff(c_1431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1429])).

tff(c_1433,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1403])).

tff(c_1432,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1403])).

tff(c_1434,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1432])).

tff(c_1447,plain,
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
    inference(resolution,[status(thm)],[c_14,c_1434])).

tff(c_1454,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_78,c_215,c_638,c_464,c_1447])).

tff(c_1455,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_1454])).

tff(c_1458,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1455])).

tff(c_1461,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1458])).

tff(c_1463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1461])).

tff(c_1465,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1432])).

tff(c_682,plain,(
    ! [B_394,F_391,E_392,D_393,A_396,C_395] :
      ( v1_funct_1(k10_tmap_1(A_396,B_394,C_395,D_393,E_392,F_391))
      | ~ m1_subset_1(F_391,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_393),u1_struct_0(B_394))))
      | ~ v1_funct_2(F_391,u1_struct_0(D_393),u1_struct_0(B_394))
      | ~ v1_funct_1(F_391)
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_395),u1_struct_0(B_394))))
      | ~ v1_funct_2(E_392,u1_struct_0(C_395),u1_struct_0(B_394))
      | ~ v1_funct_1(E_392)
      | ~ m1_pre_topc(D_393,A_396)
      | v2_struct_0(D_393)
      | ~ m1_pre_topc(C_395,A_396)
      | v2_struct_0(C_395)
      | ~ l1_pre_topc(B_394)
      | ~ v2_pre_topc(B_394)
      | v2_struct_0(B_394)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_688,plain,(
    ! [A_396,C_395,E_392] :
      ( v1_funct_1(k10_tmap_1(A_396,'#skF_2',C_395,'#skF_4',E_392,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_395),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_392,u1_struct_0(C_395),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_392)
      | ~ m1_pre_topc('#skF_4',A_396)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_395,A_396)
      | v2_struct_0(C_395)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(resolution,[status(thm)],[c_60,c_682])).

tff(c_698,plain,(
    ! [A_396,C_395,E_392] :
      ( v1_funct_1(k10_tmap_1(A_396,'#skF_2',C_395,'#skF_4',E_392,'#skF_6'))
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_395),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_392,u1_struct_0(C_395),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_392)
      | ~ m1_pre_topc('#skF_4',A_396)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_395,A_396)
      | v2_struct_0(C_395)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_66,c_64,c_688])).

tff(c_699,plain,(
    ! [A_396,C_395,E_392] :
      ( v1_funct_1(k10_tmap_1(A_396,'#skF_2',C_395,'#skF_4',E_392,'#skF_6'))
      | ~ m1_subset_1(E_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_395),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_392,u1_struct_0(C_395),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_392)
      | ~ m1_pre_topc('#skF_4',A_396)
      | ~ m1_pre_topc(C_395,A_396)
      | v2_struct_0(C_395)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_80,c_698])).

tff(c_1473,plain,(
    ! [A_396] :
      ( v1_funct_1(k10_tmap_1(A_396,'#skF_2','#skF_4','#skF_4',k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc('#skF_4',A_396)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(resolution,[status(thm)],[c_1465,c_699])).

tff(c_1495,plain,(
    ! [A_396] :
      ( v1_funct_1(k10_tmap_1(A_396,'#skF_2','#skF_4','#skF_4',k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_4',A_396)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_1473])).

tff(c_1496,plain,(
    ! [A_396] :
      ( v1_funct_1(k10_tmap_1(A_396,'#skF_2','#skF_4','#skF_4',k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_4',A_396)
      | ~ l1_pre_topc(A_396)
      | ~ v2_pre_topc(A_396)
      | v2_struct_0(A_396) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1495])).

tff(c_1512,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1496])).

tff(c_1515,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_657,c_1512])).

tff(c_1518,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_78,c_1515])).

tff(c_1519,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1518])).

tff(c_1522,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_8,c_1519])).

tff(c_1525,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1522])).

tff(c_1527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1525])).

tff(c_1529,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1496])).

tff(c_1464,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1432])).

tff(c_1550,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1529,c_1464])).

tff(c_62,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_305])).

tff(c_1676,plain,(
    ! [E_572,D_569,A_570,B_571,C_568] :
      ( v5_pre_topc(E_572,k1_tsep_1(A_570,C_568,D_569),B_571)
      | ~ m1_subset_1(k3_tmap_1(A_570,B_571,k1_tsep_1(A_570,C_568,D_569),D_569,E_572),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_569),u1_struct_0(B_571))))
      | ~ v5_pre_topc(k3_tmap_1(A_570,B_571,k1_tsep_1(A_570,C_568,D_569),D_569,E_572),D_569,B_571)
      | ~ v1_funct_2(k3_tmap_1(A_570,B_571,k1_tsep_1(A_570,C_568,D_569),D_569,E_572),u1_struct_0(D_569),u1_struct_0(B_571))
      | ~ v1_funct_1(k3_tmap_1(A_570,B_571,k1_tsep_1(A_570,C_568,D_569),D_569,E_572))
      | ~ m1_subset_1(k3_tmap_1(A_570,B_571,k1_tsep_1(A_570,C_568,D_569),C_568,E_572),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_568),u1_struct_0(B_571))))
      | ~ v5_pre_topc(k3_tmap_1(A_570,B_571,k1_tsep_1(A_570,C_568,D_569),C_568,E_572),C_568,B_571)
      | ~ v1_funct_2(k3_tmap_1(A_570,B_571,k1_tsep_1(A_570,C_568,D_569),C_568,E_572),u1_struct_0(C_568),u1_struct_0(B_571))
      | ~ v1_funct_1(k3_tmap_1(A_570,B_571,k1_tsep_1(A_570,C_568,D_569),C_568,E_572))
      | ~ m1_subset_1(E_572,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_570,C_568,D_569)),u1_struct_0(B_571))))
      | ~ v1_funct_2(E_572,u1_struct_0(k1_tsep_1(A_570,C_568,D_569)),u1_struct_0(B_571))
      | ~ v1_funct_1(E_572)
      | ~ r4_tsep_1(A_570,C_568,D_569)
      | ~ m1_pre_topc(D_569,A_570)
      | v2_struct_0(D_569)
      | ~ m1_pre_topc(C_568,A_570)
      | v2_struct_0(C_568)
      | ~ l1_pre_topc(B_571)
      | ~ v2_pre_topc(B_571)
      | v2_struct_0(B_571)
      | ~ l1_pre_topc(A_570)
      | ~ v2_pre_topc(A_570)
      | v2_struct_0(A_570) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_1678,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1550,c_1676])).

tff(c_1688,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_56,c_215,c_638,c_464,c_74,c_1302,c_72,c_1302,c_70,c_1302,c_68,c_1302,c_66,c_1550,c_64,c_1550,c_62,c_1550,c_60,c_1678])).

tff(c_1690,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_637,c_1688])).

%------------------------------------------------------------------------------
