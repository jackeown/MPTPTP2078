%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1833+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:29 EST 2020

% Result     : Theorem 8.83s
% Output     : CNFRefutation 8.96s
% Verified   : 
% Statistics : Number of formulae       :  168 (2152 expanded)
%              Number of leaves         :   36 ( 855 expanded)
%              Depth                    :   20
%              Number of atoms          :  756 (23901 expanded)
%              Number of equality atoms :   13 ( 166 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > v1_tsep_1 > r1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_tsep_1,type,(
    v1_tsep_1: ( $i * $i ) > $o )).

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

tff(f_318,negated_conjecture,(
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
                  & v1_tsep_1(C,A)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_tsep_1(D,A)
                      & m1_pre_topc(D,A) )
                   => ( r1_tsep_1(C,D)
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
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_tmap_1)).

tff(f_146,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_124,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_176,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

tff(f_82,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_tmap_1)).

tff(f_192,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_funct_2(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_254,axiom,(
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
                & v1_tsep_1(C,A)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_tsep_1(D,A)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_tmap_1)).

tff(c_68,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_106,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_102,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_90,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_84,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_20,plain,(
    ! [A_134,B_135,C_136] :
      ( m1_pre_topc(k1_tsep_1(A_134,B_135,C_136),A_134)
      | ~ m1_pre_topc(C_136,A_134)
      | v2_struct_0(C_136)
      | ~ m1_pre_topc(B_135,A_134)
      | v2_struct_0(B_135)
      | ~ l1_pre_topc(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_104,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_100,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_98,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_96,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_78,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_74,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_70,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_1327,plain,(
    ! [B_628,E_625,C_627,A_626,D_629,F_624] :
      ( v1_funct_2(k10_tmap_1(A_626,B_628,C_627,D_629,E_625,F_624),u1_struct_0(k1_tsep_1(A_626,C_627,D_629)),u1_struct_0(B_628))
      | ~ m1_subset_1(F_624,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_629),u1_struct_0(B_628))))
      | ~ v1_funct_2(F_624,u1_struct_0(D_629),u1_struct_0(B_628))
      | ~ v1_funct_1(F_624)
      | ~ m1_subset_1(E_625,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_627),u1_struct_0(B_628))))
      | ~ v1_funct_2(E_625,u1_struct_0(C_627),u1_struct_0(B_628))
      | ~ v1_funct_1(E_625)
      | ~ m1_pre_topc(D_629,A_626)
      | v2_struct_0(D_629)
      | ~ m1_pre_topc(C_627,A_626)
      | v2_struct_0(C_627)
      | ~ l1_pre_topc(B_628)
      | ~ v2_pre_topc(B_628)
      | v2_struct_0(B_628)
      | ~ l1_pre_topc(A_626)
      | ~ v2_pre_topc(A_626)
      | v2_struct_0(A_626) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_831,plain,(
    ! [B_521,D_522,A_519,C_520,F_517,E_518] :
      ( m1_subset_1(k10_tmap_1(A_519,B_521,C_520,D_522,E_518,F_517),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_519,C_520,D_522)),u1_struct_0(B_521))))
      | ~ m1_subset_1(F_517,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_522),u1_struct_0(B_521))))
      | ~ v1_funct_2(F_517,u1_struct_0(D_522),u1_struct_0(B_521))
      | ~ v1_funct_1(F_517)
      | ~ m1_subset_1(E_518,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_520),u1_struct_0(B_521))))
      | ~ v1_funct_2(E_518,u1_struct_0(C_520),u1_struct_0(B_521))
      | ~ v1_funct_1(E_518)
      | ~ m1_pre_topc(D_522,A_519)
      | v2_struct_0(D_522)
      | ~ m1_pre_topc(C_520,A_519)
      | v2_struct_0(C_520)
      | ~ l1_pre_topc(B_521)
      | ~ v2_pre_topc(B_521)
      | v2_struct_0(B_521)
      | ~ l1_pre_topc(A_519)
      | ~ v2_pre_topc(A_519)
      | v2_struct_0(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_237,plain,(
    ! [B_301,F_297,A_299,E_298,C_300,D_302] :
      ( v1_funct_1(k10_tmap_1(A_299,B_301,C_300,D_302,E_298,F_297))
      | ~ m1_subset_1(F_297,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_302),u1_struct_0(B_301))))
      | ~ v1_funct_2(F_297,u1_struct_0(D_302),u1_struct_0(B_301))
      | ~ v1_funct_1(F_297)
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_300),u1_struct_0(B_301))))
      | ~ v1_funct_2(E_298,u1_struct_0(C_300),u1_struct_0(B_301))
      | ~ v1_funct_1(E_298)
      | ~ m1_pre_topc(D_302,A_299)
      | v2_struct_0(D_302)
      | ~ m1_pre_topc(C_300,A_299)
      | v2_struct_0(C_300)
      | ~ l1_pre_topc(B_301)
      | ~ v2_pre_topc(B_301)
      | v2_struct_0(B_301)
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_246,plain,(
    ! [A_299,C_300,E_298] :
      ( v1_funct_1(k10_tmap_1(A_299,'#skF_2',C_300,'#skF_4',E_298,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_300),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_298,u1_struct_0(C_300),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_298)
      | ~ m1_pre_topc('#skF_4',A_299)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_300,A_299)
      | v2_struct_0(C_300)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(resolution,[status(thm)],[c_66,c_237])).

tff(c_255,plain,(
    ! [A_299,C_300,E_298] :
      ( v1_funct_1(k10_tmap_1(A_299,'#skF_2',C_300,'#skF_4',E_298,'#skF_6'))
      | ~ m1_subset_1(E_298,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_300),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_298,u1_struct_0(C_300),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_298)
      | ~ m1_pre_topc('#skF_4',A_299)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_300,A_299)
      | v2_struct_0(C_300)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_299)
      | ~ v2_pre_topc(A_299)
      | v2_struct_0(A_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_72,c_70,c_246])).

tff(c_283,plain,(
    ! [A_308,C_309,E_310] :
      ( v1_funct_1(k10_tmap_1(A_308,'#skF_2',C_309,'#skF_4',E_310,'#skF_6'))
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_309),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_310,u1_struct_0(C_309),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_310)
      | ~ m1_pre_topc('#skF_4',A_308)
      | ~ m1_pre_topc(C_309,A_308)
      | v2_struct_0(C_309)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_88,c_255])).

tff(c_288,plain,(
    ! [A_308] :
      ( v1_funct_1(k10_tmap_1(A_308,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_308)
      | ~ m1_pre_topc('#skF_3',A_308)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(resolution,[status(thm)],[c_74,c_283])).

tff(c_300,plain,(
    ! [A_308] :
      ( v1_funct_1(k10_tmap_1(A_308,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_308)
      | ~ m1_pre_topc('#skF_3',A_308)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308)
      | v2_struct_0(A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_288])).

tff(c_308,plain,(
    ! [A_312] :
      ( v1_funct_1(k10_tmap_1(A_312,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_312)
      | ~ m1_pre_topc('#skF_3',A_312)
      | ~ l1_pre_topc(A_312)
      | ~ v2_pre_topc(A_312)
      | v2_struct_0(A_312) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_300])).

tff(c_64,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_147,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_311,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_308,c_147])).

tff(c_314,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_90,c_84,c_311])).

tff(c_316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_314])).

tff(c_317,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_387,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_317])).

tff(c_856,plain,
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
    inference(resolution,[status(thm)],[c_831,c_387])).

tff(c_884,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_90,c_84,c_80,c_78,c_74,c_72,c_70,c_66,c_856])).

tff(c_886,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_94,c_88,c_884])).

tff(c_887,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_921,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_887])).

tff(c_1330,plain,
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
    inference(resolution,[status(thm)],[c_1327,c_921])).

tff(c_1333,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_90,c_84,c_80,c_78,c_74,c_72,c_70,c_66,c_1330])).

tff(c_1335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_94,c_88,c_1333])).

tff(c_1337,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_887])).

tff(c_318,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_888,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_317])).

tff(c_28,plain,(
    ! [A_137,B_138,E_141,C_139,D_140] :
      ( v1_funct_2(k3_tmap_1(A_137,B_138,C_139,D_140,E_141),u1_struct_0(D_140),u1_struct_0(B_138))
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139),u1_struct_0(B_138))))
      | ~ v1_funct_2(E_141,u1_struct_0(C_139),u1_struct_0(B_138))
      | ~ v1_funct_1(E_141)
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(C_139,A_137)
      | ~ l1_pre_topc(B_138)
      | ~ v2_pre_topc(B_138)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_890,plain,(
    ! [A_137,D_140] :
      ( v1_funct_2(k3_tmap_1(A_137,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_140,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_140),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_137)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_888,c_28])).

tff(c_900,plain,(
    ! [A_137,D_140] :
      ( v1_funct_2(k3_tmap_1(A_137,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_140,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_140),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_137)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_318,c_890])).

tff(c_901,plain,(
    ! [A_137,D_140] :
      ( v1_funct_2(k3_tmap_1(A_137,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_140,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_140),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_137)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_900])).

tff(c_1375,plain,(
    ! [A_137,D_140] :
      ( v1_funct_2(k3_tmap_1(A_137,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_140,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_140),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_137)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_901])).

tff(c_1336,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_887])).

tff(c_92,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_86,plain,(
    v1_tsep_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_26,plain,(
    ! [A_137,B_138,E_141,C_139,D_140] :
      ( m1_subset_1(k3_tmap_1(A_137,B_138,C_139,D_140,E_141),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_140),u1_struct_0(B_138))))
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139),u1_struct_0(B_138))))
      | ~ v1_funct_2(E_141,u1_struct_0(C_139),u1_struct_0(B_138))
      | ~ v1_funct_1(E_141)
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(C_139,A_137)
      | ~ l1_pre_topc(B_138)
      | ~ v2_pre_topc(B_138)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_30,plain,(
    ! [A_137,B_138,E_141,C_139,D_140] :
      ( v1_funct_1(k3_tmap_1(A_137,B_138,C_139,D_140,E_141))
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139),u1_struct_0(B_138))))
      | ~ v1_funct_2(E_141,u1_struct_0(C_139),u1_struct_0(B_138))
      | ~ v1_funct_1(E_141)
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(C_139,A_137)
      | ~ l1_pre_topc(B_138)
      | ~ v2_pre_topc(B_138)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_892,plain,(
    ! [A_137,D_140] :
      ( v1_funct_1(k3_tmap_1(A_137,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_140,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_137)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_888,c_30])).

tff(c_904,plain,(
    ! [A_137,D_140] :
      ( v1_funct_1(k3_tmap_1(A_137,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_140,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_137)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_318,c_892])).

tff(c_905,plain,(
    ! [A_137,D_140] :
      ( v1_funct_1(k3_tmap_1(A_137,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_140,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_137)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_904])).

tff(c_1349,plain,(
    ! [A_137,D_140] :
      ( v1_funct_1(k3_tmap_1(A_137,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_140,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_140,A_137)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_137)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1337,c_905])).

tff(c_82,plain,(
    r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_2636,plain,(
    ! [B_885,A_890,F_886,D_889,C_887,E_888] :
      ( ~ r1_tsep_1(C_887,D_889)
      | r2_funct_2(u1_struct_0(C_887),u1_struct_0(B_885),k3_tmap_1(A_890,B_885,k1_tsep_1(A_890,C_887,D_889),C_887,k10_tmap_1(A_890,B_885,C_887,D_889,E_888,F_886)),E_888)
      | ~ m1_subset_1(k10_tmap_1(A_890,B_885,C_887,D_889,E_888,F_886),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_890,C_887,D_889)),u1_struct_0(B_885))))
      | ~ v1_funct_2(k10_tmap_1(A_890,B_885,C_887,D_889,E_888,F_886),u1_struct_0(k1_tsep_1(A_890,C_887,D_889)),u1_struct_0(B_885))
      | ~ v1_funct_1(k10_tmap_1(A_890,B_885,C_887,D_889,E_888,F_886))
      | ~ m1_subset_1(F_886,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_889),u1_struct_0(B_885))))
      | ~ v1_funct_2(F_886,u1_struct_0(D_889),u1_struct_0(B_885))
      | ~ v1_funct_1(F_886)
      | ~ m1_subset_1(E_888,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_887),u1_struct_0(B_885))))
      | ~ v1_funct_2(E_888,u1_struct_0(C_887),u1_struct_0(B_885))
      | ~ v1_funct_1(E_888)
      | ~ m1_pre_topc(D_889,A_890)
      | v2_struct_0(D_889)
      | ~ m1_pre_topc(C_887,A_890)
      | v2_struct_0(C_887)
      | ~ l1_pre_topc(B_885)
      | ~ v2_pre_topc(B_885)
      | v2_struct_0(B_885)
      | ~ l1_pre_topc(A_890)
      | ~ v2_pre_topc(A_890)
      | v2_struct_0(A_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2640,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
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
    inference(resolution,[status(thm)],[c_888,c_2636])).

tff(c_2647,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_90,c_84,c_80,c_78,c_74,c_72,c_70,c_66,c_318,c_1337,c_82,c_2640])).

tff(c_2648,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_94,c_88,c_2647])).

tff(c_34,plain,(
    ! [D_145,C_144,A_142,B_143] :
      ( D_145 = C_144
      | ~ r2_funct_2(A_142,B_143,C_144,D_145)
      | ~ m1_subset_1(D_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_2(D_145,A_142,B_143)
      | ~ v1_funct_1(D_145)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143)))
      | ~ v1_funct_2(C_144,A_142,B_143)
      | ~ v1_funct_1(C_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_2651,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_2648,c_34])).

tff(c_2654,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_74,c_2651])).

tff(c_2878,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_2654])).

tff(c_2881,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1349,c_2878])).

tff(c_2884,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_90,c_2881])).

tff(c_2885,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_2884])).

tff(c_2888,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_2885])).

tff(c_2891,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_90,c_84,c_2888])).

tff(c_2893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_94,c_88,c_2891])).

tff(c_2894,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2654])).

tff(c_2901,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_2894])).

tff(c_2907,plain,
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
    inference(resolution,[status(thm)],[c_26,c_2901])).

tff(c_2917,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_90,c_318,c_1337,c_888,c_2907])).

tff(c_2918,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_2917])).

tff(c_2922,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_2918])).

tff(c_2925,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_90,c_84,c_2922])).

tff(c_2927,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_94,c_88,c_2925])).

tff(c_2928,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2894])).

tff(c_3059,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2928])).

tff(c_3065,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1375,c_3059])).

tff(c_3075,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_90,c_3065])).

tff(c_3076,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_3075])).

tff(c_3083,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_3076])).

tff(c_3086,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_90,c_84,c_3083])).

tff(c_3088,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_94,c_88,c_3086])).

tff(c_3089,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2928])).

tff(c_76,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_318])).

tff(c_2787,plain,(
    ! [D_919,E_918,C_917,F_916,A_920,B_915] :
      ( ~ r1_tsep_1(C_917,D_919)
      | r2_funct_2(u1_struct_0(D_919),u1_struct_0(B_915),k3_tmap_1(A_920,B_915,k1_tsep_1(A_920,C_917,D_919),D_919,k10_tmap_1(A_920,B_915,C_917,D_919,E_918,F_916)),F_916)
      | ~ m1_subset_1(k10_tmap_1(A_920,B_915,C_917,D_919,E_918,F_916),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_920,C_917,D_919)),u1_struct_0(B_915))))
      | ~ v1_funct_2(k10_tmap_1(A_920,B_915,C_917,D_919,E_918,F_916),u1_struct_0(k1_tsep_1(A_920,C_917,D_919)),u1_struct_0(B_915))
      | ~ v1_funct_1(k10_tmap_1(A_920,B_915,C_917,D_919,E_918,F_916))
      | ~ m1_subset_1(F_916,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_919),u1_struct_0(B_915))))
      | ~ v1_funct_2(F_916,u1_struct_0(D_919),u1_struct_0(B_915))
      | ~ v1_funct_1(F_916)
      | ~ m1_subset_1(E_918,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_917),u1_struct_0(B_915))))
      | ~ v1_funct_2(E_918,u1_struct_0(C_917),u1_struct_0(B_915))
      | ~ v1_funct_1(E_918)
      | ~ m1_pre_topc(D_919,A_920)
      | v2_struct_0(D_919)
      | ~ m1_pre_topc(C_917,A_920)
      | v2_struct_0(C_917)
      | ~ l1_pre_topc(B_915)
      | ~ v2_pre_topc(B_915)
      | v2_struct_0(B_915)
      | ~ l1_pre_topc(A_920)
      | ~ v2_pre_topc(A_920)
      | v2_struct_0(A_920) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2791,plain,
    ( ~ r1_tsep_1('#skF_3','#skF_4')
    | r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
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
    inference(resolution,[status(thm)],[c_888,c_2787])).

tff(c_2798,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_90,c_84,c_80,c_78,c_74,c_72,c_70,c_66,c_318,c_1337,c_82,c_2791])).

tff(c_2799,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_94,c_88,c_2798])).

tff(c_2804,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_2799,c_34])).

tff(c_2811,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_2804])).

tff(c_3344,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_2811])).

tff(c_3347,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1349,c_3344])).

tff(c_3350,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_84,c_3347])).

tff(c_3351,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_3350])).

tff(c_3354,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_3351])).

tff(c_3357,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_90,c_84,c_3354])).

tff(c_3359,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_94,c_88,c_3357])).

tff(c_3361,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_2811])).

tff(c_3360,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2811])).

tff(c_3362,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_3360])).

tff(c_3401,plain,
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
    inference(resolution,[status(thm)],[c_26,c_3362])).

tff(c_3411,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_84,c_318,c_1337,c_888,c_3401])).

tff(c_3412,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_3411])).

tff(c_3416,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_3412])).

tff(c_3419,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_90,c_84,c_3416])).

tff(c_3421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_94,c_88,c_3419])).

tff(c_3423,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_3360])).

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
      | ~ m1_pre_topc(D_174,A_146)
      | ~ v1_tsep_1(D_174,A_146)
      | v2_struct_0(D_174)
      | ~ m1_pre_topc(C_170,A_146)
      | ~ v1_tsep_1(C_170,A_146)
      | v2_struct_0(C_170)
      | ~ l1_pre_topc(B_162)
      | ~ v2_pre_topc(B_162)
      | v2_struct_0(B_162)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_3425,plain,
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
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_3423,c_38])).

tff(c_3449,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_98,c_96,c_92,c_90,c_86,c_84,c_318,c_1337,c_888,c_80,c_3089,c_78,c_3089,c_76,c_3089,c_74,c_3089,c_3361,c_3425])).

tff(c_3450,plain,
    ( ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2')
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_100,c_94,c_88,c_1336,c_3449])).

tff(c_3486,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3450])).

tff(c_3492,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1375,c_3486])).

tff(c_3502,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_84,c_3492])).

tff(c_3503,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_3502])).

tff(c_3510,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_3503])).

tff(c_3513,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_90,c_84,c_3510])).

tff(c_3515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_94,c_88,c_3513])).

tff(c_3517,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3450])).

tff(c_3422,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_3360])).

tff(c_3672,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3517,c_3422])).

tff(c_3516,plain,(
    ~ v5_pre_topc(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_4','#skF_2') ),
    inference(splitRight,[status(thm)],[c_3450])).

tff(c_3681,plain,(
    ~ v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3672,c_3516])).

tff(c_3690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3681])).

%------------------------------------------------------------------------------
