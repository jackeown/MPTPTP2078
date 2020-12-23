%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:10 EST 2020

% Result     : Theorem 6.26s
% Output     : CNFRefutation 6.34s
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

tff(f_306,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_tmap_1)).

tff(f_105,axiom,(
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

tff(f_135,axiom,(
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

tff(f_245,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

tff(f_195,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).

tff(c_96,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_94,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_92,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_88,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_86,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_82,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_78,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_74,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_72,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_64,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_628,plain,(
    ! [B_369,E_372,F_368,A_371,D_367,C_370] :
      ( v1_funct_2(k10_tmap_1(A_371,B_369,C_370,D_367,E_372,F_368),u1_struct_0(k1_tsep_1(A_371,C_370,D_367)),u1_struct_0(B_369))
      | ~ m1_subset_1(F_368,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_367),u1_struct_0(B_369))))
      | ~ v1_funct_2(F_368,u1_struct_0(D_367),u1_struct_0(B_369))
      | ~ v1_funct_1(F_368)
      | ~ m1_subset_1(E_372,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_370),u1_struct_0(B_369))))
      | ~ v1_funct_2(E_372,u1_struct_0(C_370),u1_struct_0(B_369))
      | ~ v1_funct_1(E_372)
      | ~ m1_pre_topc(D_367,A_371)
      | v2_struct_0(D_367)
      | ~ m1_pre_topc(C_370,A_371)
      | v2_struct_0(C_370)
      | ~ l1_pre_topc(B_369)
      | ~ v2_pre_topc(B_369)
      | v2_struct_0(B_369)
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_412,plain,(
    ! [A_315,F_312,D_311,C_314,E_316,B_313] :
      ( m1_subset_1(k10_tmap_1(A_315,B_313,C_314,D_311,E_316,F_312),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_315,C_314,D_311)),u1_struct_0(B_313))))
      | ~ m1_subset_1(F_312,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_311),u1_struct_0(B_313))))
      | ~ v1_funct_2(F_312,u1_struct_0(D_311),u1_struct_0(B_313))
      | ~ v1_funct_1(F_312)
      | ~ m1_subset_1(E_316,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_314),u1_struct_0(B_313))))
      | ~ v1_funct_2(E_316,u1_struct_0(C_314),u1_struct_0(B_313))
      | ~ v1_funct_1(E_316)
      | ~ m1_pre_topc(D_311,A_315)
      | v2_struct_0(D_311)
      | ~ m1_pre_topc(C_314,A_315)
      | v2_struct_0(C_314)
      | ~ l1_pre_topc(B_313)
      | ~ v2_pre_topc(B_313)
      | v2_struct_0(B_313)
      | ~ l1_pre_topc(A_315)
      | ~ v2_pre_topc(A_315)
      | v2_struct_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_168,plain,(
    ! [B_211,A_213,D_209,F_210,C_212,E_214] :
      ( v1_funct_1(k10_tmap_1(A_213,B_211,C_212,D_209,E_214,F_210))
      | ~ m1_subset_1(F_210,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_209),u1_struct_0(B_211))))
      | ~ v1_funct_2(F_210,u1_struct_0(D_209),u1_struct_0(B_211))
      | ~ v1_funct_1(F_210)
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212),u1_struct_0(B_211))))
      | ~ v1_funct_2(E_214,u1_struct_0(C_212),u1_struct_0(B_211))
      | ~ v1_funct_1(E_214)
      | ~ m1_pre_topc(D_209,A_213)
      | v2_struct_0(D_209)
      | ~ m1_pre_topc(C_212,A_213)
      | v2_struct_0(C_212)
      | ~ l1_pre_topc(B_211)
      | ~ v2_pre_topc(B_211)
      | v2_struct_0(B_211)
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_172,plain,(
    ! [A_213,C_212,E_214] :
      ( v1_funct_1(k10_tmap_1(A_213,'#skF_2',C_212,'#skF_4',E_214,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_214,u1_struct_0(C_212),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_214)
      | ~ m1_pre_topc('#skF_4',A_213)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_212,A_213)
      | v2_struct_0(C_212)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
    inference(resolution,[status(thm)],[c_60,c_168])).

tff(c_178,plain,(
    ! [A_213,C_212,E_214] :
      ( v1_funct_1(k10_tmap_1(A_213,'#skF_2',C_212,'#skF_4',E_214,'#skF_6'))
      | ~ m1_subset_1(E_214,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_214,u1_struct_0(C_212),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_214)
      | ~ m1_pre_topc('#skF_4',A_213)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_212,A_213)
      | v2_struct_0(C_212)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_213)
      | ~ v2_pre_topc(A_213)
      | v2_struct_0(A_213) ) ),
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
    inference(cnfTransformation,[status(thm)],[f_306])).

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
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_215,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_638,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_464,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( m1_pre_topc(k1_tsep_1(A_11,B_12,C_13),A_11)
      | ~ m1_pre_topc(C_13,A_11)
      | v2_struct_0(C_13)
      | ~ m1_pre_topc(B_12,A_11)
      | v2_struct_0(B_12)
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_647,plain,(
    ! [C_375,D_374,A_377,E_373,B_376] :
      ( v1_funct_2(k3_tmap_1(A_377,B_376,C_375,D_374,E_373),u1_struct_0(D_374),u1_struct_0(B_376))
      | ~ m1_subset_1(E_373,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_375),u1_struct_0(B_376))))
      | ~ v1_funct_2(E_373,u1_struct_0(C_375),u1_struct_0(B_376))
      | ~ v1_funct_1(E_373)
      | ~ m1_pre_topc(D_374,A_377)
      | ~ m1_pre_topc(C_375,A_377)
      | ~ l1_pre_topc(B_376)
      | ~ v2_pre_topc(B_376)
      | v2_struct_0(B_376)
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_649,plain,(
    ! [A_377,D_374] :
      ( v1_funct_2(k3_tmap_1(A_377,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_374,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_374),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_374,A_377)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_377)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(resolution,[status(thm)],[c_464,c_647])).

tff(c_656,plain,(
    ! [A_377,D_374] :
      ( v1_funct_2(k3_tmap_1(A_377,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_374,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_374),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_374,A_377)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_377)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_215,c_638,c_649])).

tff(c_657,plain,(
    ! [A_377,D_374] :
      ( v1_funct_2(k3_tmap_1(A_377,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_374,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_374),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_374,A_377)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_377)
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_656])).

tff(c_22,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] :
      ( v1_funct_1(k3_tmap_1(A_14,B_15,C_16,D_17,E_18))
      | ~ m1_subset_1(E_18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_16),u1_struct_0(B_15))))
      | ~ v1_funct_2(E_18,u1_struct_0(C_16),u1_struct_0(B_15))
      | ~ v1_funct_1(E_18)
      | ~ m1_pre_topc(D_17,A_14)
      | ~ m1_pre_topc(C_16,A_14)
      | ~ l1_pre_topc(B_15)
      | ~ v2_pre_topc(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_466,plain,(
    ! [A_14,D_17] :
      ( v1_funct_1(k3_tmap_1(A_14,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_17,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_17,A_14)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_14)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_464,c_22])).

tff(c_471,plain,(
    ! [A_14,D_17] :
      ( v1_funct_1(k3_tmap_1(A_14,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_17,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_17,A_14)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_14)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_215,c_466])).

tff(c_472,plain,(
    ! [A_14,D_17] :
      ( v1_funct_1(k3_tmap_1(A_14,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_17,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_17,A_14)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_471])).

tff(c_670,plain,(
    ! [A_14,D_17] :
      ( v1_funct_1(k3_tmap_1(A_14,'#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),D_17,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_17,A_14)
      | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),A_14)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_638,c_472])).

tff(c_76,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_58,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_1388,plain,(
    ! [F_540,D_539,A_538,E_541,C_537,B_542] :
      ( r2_funct_2(u1_struct_0(C_537),u1_struct_0(B_542),k3_tmap_1(A_538,B_542,k1_tsep_1(A_538,C_537,D_539),C_537,k10_tmap_1(A_538,B_542,C_537,D_539,E_541,F_540)),E_541)
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
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_1393,plain,
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
    inference(resolution,[status(thm)],[c_58,c_1388])).

tff(c_1397,plain,
    ( r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_1393])).

tff(c_1398,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_76,c_1397])).

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

tff(c_1400,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1398,c_4])).

tff(c_1403,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_1400])).

tff(c_1416,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1403])).

tff(c_1419,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_670,c_1416])).

tff(c_1422,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_1419])).

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
    inference(resolution,[status(thm)],[c_12,c_1423])).

tff(c_1429,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1426])).

tff(c_1431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1429])).

tff(c_1433,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_1403])).

tff(c_18,plain,(
    ! [E_18,C_16,D_17,A_14,B_15] :
      ( m1_subset_1(k3_tmap_1(A_14,B_15,C_16,D_17,E_18),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_17),u1_struct_0(B_15))))
      | ~ m1_subset_1(E_18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_16),u1_struct_0(B_15))))
      | ~ v1_funct_2(E_18,u1_struct_0(C_16),u1_struct_0(B_15))
      | ~ v1_funct_1(E_18)
      | ~ m1_pre_topc(D_17,A_14)
      | ~ m1_pre_topc(C_16,A_14)
      | ~ l1_pre_topc(B_15)
      | ~ v2_pre_topc(B_15)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1432,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1403])).

tff(c_1434,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1432])).

tff(c_1446,plain,
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
    inference(resolution,[status(thm)],[c_18,c_1434])).

tff(c_1453,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_215,c_638,c_464,c_1446])).

tff(c_1454,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_1453])).

tff(c_1457,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1454])).

tff(c_1460,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1457])).

tff(c_1462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1460])).

tff(c_1464,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_1432])).

tff(c_682,plain,(
    ! [D_391,B_393,F_392,A_395,C_394,E_396] :
      ( v1_funct_1(k10_tmap_1(A_395,B_393,C_394,D_391,E_396,F_392))
      | ~ m1_subset_1(F_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_391),u1_struct_0(B_393))))
      | ~ v1_funct_2(F_392,u1_struct_0(D_391),u1_struct_0(B_393))
      | ~ v1_funct_1(F_392)
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394),u1_struct_0(B_393))))
      | ~ v1_funct_2(E_396,u1_struct_0(C_394),u1_struct_0(B_393))
      | ~ v1_funct_1(E_396)
      | ~ m1_pre_topc(D_391,A_395)
      | v2_struct_0(D_391)
      | ~ m1_pre_topc(C_394,A_395)
      | v2_struct_0(C_394)
      | ~ l1_pre_topc(B_393)
      | ~ v2_pre_topc(B_393)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_690,plain,(
    ! [A_395,C_394,E_396] :
      ( v1_funct_1(k10_tmap_1(A_395,'#skF_2',C_394,'#skF_3',E_396,'#skF_5'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_396,u1_struct_0(C_394),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_396)
      | ~ m1_pre_topc('#skF_3',A_395)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_394,A_395)
      | v2_struct_0(C_394)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(resolution,[status(thm)],[c_68,c_682])).

tff(c_702,plain,(
    ! [A_395,C_394,E_396] :
      ( v1_funct_1(k10_tmap_1(A_395,'#skF_2',C_394,'#skF_3',E_396,'#skF_5'))
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_396,u1_struct_0(C_394),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_396)
      | ~ m1_pre_topc('#skF_3',A_395)
      | v2_struct_0('#skF_3')
      | ~ m1_pre_topc(C_394,A_395)
      | v2_struct_0(C_394)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_72,c_690])).

tff(c_703,plain,(
    ! [A_395,C_394,E_396] :
      ( v1_funct_1(k10_tmap_1(A_395,'#skF_2',C_394,'#skF_3',E_396,'#skF_5'))
      | ~ m1_subset_1(E_396,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_396,u1_struct_0(C_394),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_396)
      | ~ m1_pre_topc('#skF_3',A_395)
      | ~ m1_pre_topc(C_394,A_395)
      | v2_struct_0(C_394)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_702])).

tff(c_1470,plain,(
    ! [A_395] :
      ( v1_funct_1(k10_tmap_1(A_395,'#skF_2','#skF_3','#skF_3',k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc('#skF_3',A_395)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(resolution,[status(thm)],[c_1464,c_703])).

tff(c_1490,plain,(
    ! [A_395] :
      ( v1_funct_1(k10_tmap_1(A_395,'#skF_2','#skF_3','#skF_3',k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_395)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1433,c_1470])).

tff(c_1491,plain,(
    ! [A_395] :
      ( v1_funct_1(k10_tmap_1(A_395,'#skF_2','#skF_3','#skF_3',k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5'))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc('#skF_3',A_395)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_1490])).

tff(c_1511,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1491])).

tff(c_1514,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_657,c_1511])).

tff(c_1517,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_1514])).

tff(c_1518,plain,(
    ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_1517])).

tff(c_1521,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1518])).

tff(c_1524,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1521])).

tff(c_1526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1524])).

tff(c_1528,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1491])).

tff(c_1463,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1432])).

tff(c_1549,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1528,c_1463])).

tff(c_70,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_1086,plain,(
    ! [F_492,E_493,B_494,D_491,C_489,A_490] :
      ( r2_funct_2(u1_struct_0(D_491),u1_struct_0(B_494),k3_tmap_1(A_490,B_494,k1_tsep_1(A_490,C_489,D_491),D_491,k10_tmap_1(A_490,B_494,C_489,D_491,E_493,F_492)),F_492)
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
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_1091,plain,
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
    inference(resolution,[status(thm)],[c_58,c_1086])).

tff(c_1095,plain,
    ( r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_74,c_72,c_68,c_66,c_64,c_60,c_1091])).

tff(c_1096,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_76,c_1095])).

tff(c_1098,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_1096,c_4])).

tff(c_1101,plain,
    ( k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_1098])).

tff(c_1167,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_1101])).

tff(c_1181,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_670,c_1167])).

tff(c_1184,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_78,c_1181])).

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
    inference(resolution,[status(thm)],[c_12,c_1185])).

tff(c_1191,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1188])).

tff(c_1193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1191])).

tff(c_1194,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1101])).

tff(c_1204,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1194])).

tff(c_1210,plain,
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
    inference(resolution,[status(thm)],[c_18,c_1204])).

tff(c_1217,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_78,c_215,c_638,c_464,c_1210])).

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
    inference(resolution,[status(thm)],[c_12,c_1218])).

tff(c_1224,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1221])).

tff(c_1226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1224])).

tff(c_1227,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1194])).

tff(c_1275,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1227])).

tff(c_1289,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_657,c_1275])).

tff(c_1292,plain,
    ( ~ m1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_78,c_1289])).

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
    inference(resolution,[status(thm)],[c_12,c_1293])).

tff(c_1299,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_82,c_78,c_1296])).

tff(c_1301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_84,c_80,c_1299])).

tff(c_1302,plain,(
    k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1227])).

tff(c_62,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_306])).

tff(c_1675,plain,(
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
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1677,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1302,c_1675])).

tff(c_1687,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_88,c_86,c_82,c_78,c_56,c_215,c_638,c_464,c_74,c_1549,c_72,c_1549,c_70,c_1549,c_68,c_1549,c_66,c_1302,c_64,c_1302,c_62,c_1302,c_60,c_1677])).

tff(c_1689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_90,c_84,c_80,c_637,c_1687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:56:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.26/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.14  
% 6.34/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.14  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.34/2.14  
% 6.34/2.14  %Foreground sorts:
% 6.34/2.14  
% 6.34/2.14  
% 6.34/2.14  %Background operators:
% 6.34/2.14  
% 6.34/2.14  
% 6.34/2.14  %Foreground operators:
% 6.34/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.34/2.14  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.34/2.14  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 6.34/2.14  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.34/2.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.34/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.34/2.14  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 6.34/2.14  tff('#skF_5', type, '#skF_5': $i).
% 6.34/2.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.34/2.14  tff('#skF_6', type, '#skF_6': $i).
% 6.34/2.14  tff('#skF_2', type, '#skF_2': $i).
% 6.34/2.14  tff('#skF_3', type, '#skF_3': $i).
% 6.34/2.14  tff('#skF_1', type, '#skF_1': $i).
% 6.34/2.14  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 6.34/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.34/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.34/2.14  tff('#skF_4', type, '#skF_4': $i).
% 6.34/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.14  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 6.34/2.14  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.34/2.14  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 6.34/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.34/2.14  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 6.34/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.34/2.14  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 6.34/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.34/2.14  
% 6.34/2.18  tff(f_306, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_tmap_1)).
% 6.34/2.18  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 6.34/2.18  tff(f_105, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 6.34/2.18  tff(f_135, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 6.34/2.18  tff(f_245, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_tmap_1)).
% 6.34/2.18  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 6.34/2.18  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_tmap_1)).
% 6.34/2.18  tff(c_96, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_90, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_84, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_80, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_94, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_92, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_88, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_86, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_82, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_78, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_74, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_72, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_64, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_60, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_628, plain, (![B_369, E_372, F_368, A_371, D_367, C_370]: (v1_funct_2(k10_tmap_1(A_371, B_369, C_370, D_367, E_372, F_368), u1_struct_0(k1_tsep_1(A_371, C_370, D_367)), u1_struct_0(B_369)) | ~m1_subset_1(F_368, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_367), u1_struct_0(B_369)))) | ~v1_funct_2(F_368, u1_struct_0(D_367), u1_struct_0(B_369)) | ~v1_funct_1(F_368) | ~m1_subset_1(E_372, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_370), u1_struct_0(B_369)))) | ~v1_funct_2(E_372, u1_struct_0(C_370), u1_struct_0(B_369)) | ~v1_funct_1(E_372) | ~m1_pre_topc(D_367, A_371) | v2_struct_0(D_367) | ~m1_pre_topc(C_370, A_371) | v2_struct_0(C_370) | ~l1_pre_topc(B_369) | ~v2_pre_topc(B_369) | v2_struct_0(B_369) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.34/2.18  tff(c_412, plain, (![A_315, F_312, D_311, C_314, E_316, B_313]: (m1_subset_1(k10_tmap_1(A_315, B_313, C_314, D_311, E_316, F_312), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_315, C_314, D_311)), u1_struct_0(B_313)))) | ~m1_subset_1(F_312, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_311), u1_struct_0(B_313)))) | ~v1_funct_2(F_312, u1_struct_0(D_311), u1_struct_0(B_313)) | ~v1_funct_1(F_312) | ~m1_subset_1(E_316, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_314), u1_struct_0(B_313)))) | ~v1_funct_2(E_316, u1_struct_0(C_314), u1_struct_0(B_313)) | ~v1_funct_1(E_316) | ~m1_pre_topc(D_311, A_315) | v2_struct_0(D_311) | ~m1_pre_topc(C_314, A_315) | v2_struct_0(C_314) | ~l1_pre_topc(B_313) | ~v2_pre_topc(B_313) | v2_struct_0(B_313) | ~l1_pre_topc(A_315) | ~v2_pre_topc(A_315) | v2_struct_0(A_315))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.34/2.18  tff(c_168, plain, (![B_211, A_213, D_209, F_210, C_212, E_214]: (v1_funct_1(k10_tmap_1(A_213, B_211, C_212, D_209, E_214, F_210)) | ~m1_subset_1(F_210, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_209), u1_struct_0(B_211)))) | ~v1_funct_2(F_210, u1_struct_0(D_209), u1_struct_0(B_211)) | ~v1_funct_1(F_210) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212), u1_struct_0(B_211)))) | ~v1_funct_2(E_214, u1_struct_0(C_212), u1_struct_0(B_211)) | ~v1_funct_1(E_214) | ~m1_pre_topc(D_209, A_213) | v2_struct_0(D_209) | ~m1_pre_topc(C_212, A_213) | v2_struct_0(C_212) | ~l1_pre_topc(B_211) | ~v2_pre_topc(B_211) | v2_struct_0(B_211) | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.34/2.18  tff(c_172, plain, (![A_213, C_212, E_214]: (v1_funct_1(k10_tmap_1(A_213, '#skF_2', C_212, '#skF_4', E_214, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_214, u1_struct_0(C_212), u1_struct_0('#skF_2')) | ~v1_funct_1(E_214) | ~m1_pre_topc('#skF_4', A_213) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_212, A_213) | v2_struct_0(C_212) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(resolution, [status(thm)], [c_60, c_168])).
% 6.34/2.18  tff(c_178, plain, (![A_213, C_212, E_214]: (v1_funct_1(k10_tmap_1(A_213, '#skF_2', C_212, '#skF_4', E_214, '#skF_6')) | ~m1_subset_1(E_214, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_212), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_214, u1_struct_0(C_212), u1_struct_0('#skF_2')) | ~v1_funct_1(E_214) | ~m1_pre_topc('#skF_4', A_213) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_212, A_213) | v2_struct_0(C_212) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_213) | ~v2_pre_topc(A_213) | v2_struct_0(A_213))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_66, c_64, c_172])).
% 6.34/2.18  tff(c_184, plain, (![A_215, C_216, E_217]: (v1_funct_1(k10_tmap_1(A_215, '#skF_2', C_216, '#skF_4', E_217, '#skF_6')) | ~m1_subset_1(E_217, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_216), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_217, u1_struct_0(C_216), u1_struct_0('#skF_2')) | ~v1_funct_1(E_217) | ~m1_pre_topc('#skF_4', A_215) | ~m1_pre_topc(C_216, A_215) | v2_struct_0(C_216) | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(negUnitSimplification, [status(thm)], [c_90, c_80, c_178])).
% 6.34/2.18  tff(c_191, plain, (![A_215]: (v1_funct_1(k10_tmap_1(A_215, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_215) | ~m1_pre_topc('#skF_3', A_215) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(resolution, [status(thm)], [c_68, c_184])).
% 6.34/2.18  tff(c_202, plain, (![A_215]: (v1_funct_1(k10_tmap_1(A_215, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_215) | ~m1_pre_topc('#skF_3', A_215) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_215) | ~v2_pre_topc(A_215) | v2_struct_0(A_215))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_191])).
% 6.34/2.18  tff(c_205, plain, (![A_219]: (v1_funct_1(k10_tmap_1(A_219, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_219) | ~m1_pre_topc('#skF_3', A_219) | ~l1_pre_topc(A_219) | ~v2_pre_topc(A_219) | v2_struct_0(A_219))), inference(negUnitSimplification, [status(thm)], [c_84, c_202])).
% 6.34/2.18  tff(c_54, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_140, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_54])).
% 6.34/2.18  tff(c_208, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_205, c_140])).
% 6.34/2.18  tff(c_211, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_208])).
% 6.34/2.18  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_211])).
% 6.34/2.18  tff(c_214, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_54])).
% 6.34/2.18  tff(c_218, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_214])).
% 6.34/2.18  tff(c_437, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_412, c_218])).
% 6.34/2.18  tff(c_460, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_74, c_72, c_68, c_66, c_64, c_60, c_437])).
% 6.34/2.18  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_460])).
% 6.34/2.18  tff(c_463, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_214])).
% 6.34/2.18  tff(c_476, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_463])).
% 6.34/2.18  tff(c_631, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_628, c_476])).
% 6.34/2.18  tff(c_634, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_74, c_72, c_68, c_66, c_64, c_60, c_631])).
% 6.34/2.18  tff(c_636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_634])).
% 6.34/2.18  tff(c_637, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_463])).
% 6.34/2.18  tff(c_56, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_215, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_54])).
% 6.34/2.18  tff(c_638, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_463])).
% 6.34/2.18  tff(c_464, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_214])).
% 6.34/2.18  tff(c_12, plain, (![A_11, B_12, C_13]: (m1_pre_topc(k1_tsep_1(A_11, B_12, C_13), A_11) | ~m1_pre_topc(C_13, A_11) | v2_struct_0(C_13) | ~m1_pre_topc(B_12, A_11) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.34/2.18  tff(c_647, plain, (![C_375, D_374, A_377, E_373, B_376]: (v1_funct_2(k3_tmap_1(A_377, B_376, C_375, D_374, E_373), u1_struct_0(D_374), u1_struct_0(B_376)) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_375), u1_struct_0(B_376)))) | ~v1_funct_2(E_373, u1_struct_0(C_375), u1_struct_0(B_376)) | ~v1_funct_1(E_373) | ~m1_pre_topc(D_374, A_377) | ~m1_pre_topc(C_375, A_377) | ~l1_pre_topc(B_376) | ~v2_pre_topc(B_376) | v2_struct_0(B_376) | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.34/2.18  tff(c_649, plain, (![A_377, D_374]: (v1_funct_2(k3_tmap_1(A_377, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_374, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_374), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_374, A_377) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_377) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(resolution, [status(thm)], [c_464, c_647])).
% 6.34/2.18  tff(c_656, plain, (![A_377, D_374]: (v1_funct_2(k3_tmap_1(A_377, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_374, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_374), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_374, A_377) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_377) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_215, c_638, c_649])).
% 6.34/2.18  tff(c_657, plain, (![A_377, D_374]: (v1_funct_2(k3_tmap_1(A_377, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_374, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_374), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_374, A_377) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_377) | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(negUnitSimplification, [status(thm)], [c_90, c_656])).
% 6.34/2.18  tff(c_22, plain, (![E_18, C_16, D_17, A_14, B_15]: (v1_funct_1(k3_tmap_1(A_14, B_15, C_16, D_17, E_18)) | ~m1_subset_1(E_18, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_16), u1_struct_0(B_15)))) | ~v1_funct_2(E_18, u1_struct_0(C_16), u1_struct_0(B_15)) | ~v1_funct_1(E_18) | ~m1_pre_topc(D_17, A_14) | ~m1_pre_topc(C_16, A_14) | ~l1_pre_topc(B_15) | ~v2_pre_topc(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.34/2.18  tff(c_466, plain, (![A_14, D_17]: (v1_funct_1(k3_tmap_1(A_14, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_17, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_17, A_14) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_14) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(resolution, [status(thm)], [c_464, c_22])).
% 6.34/2.18  tff(c_471, plain, (![A_14, D_17]: (v1_funct_1(k3_tmap_1(A_14, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_17, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_17, A_14) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_14) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_215, c_466])).
% 6.34/2.18  tff(c_472, plain, (![A_14, D_17]: (v1_funct_1(k3_tmap_1(A_14, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_17, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_17, A_14) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(negUnitSimplification, [status(thm)], [c_90, c_471])).
% 6.34/2.18  tff(c_670, plain, (![A_14, D_17]: (v1_funct_1(k3_tmap_1(A_14, '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), D_17, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_17, A_14) | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), A_14) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_638, c_472])).
% 6.34/2.18  tff(c_76, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_58, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_1388, plain, (![F_540, D_539, A_538, E_541, C_537, B_542]: (r2_funct_2(u1_struct_0(C_537), u1_struct_0(B_542), k3_tmap_1(A_538, B_542, k1_tsep_1(A_538, C_537, D_539), C_537, k10_tmap_1(A_538, B_542, C_537, D_539, E_541, F_540)), E_541) | ~r2_funct_2(u1_struct_0(k2_tsep_1(A_538, C_537, D_539)), u1_struct_0(B_542), k3_tmap_1(A_538, B_542, C_537, k2_tsep_1(A_538, C_537, D_539), E_541), k3_tmap_1(A_538, B_542, D_539, k2_tsep_1(A_538, C_537, D_539), F_540)) | ~m1_subset_1(F_540, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_539), u1_struct_0(B_542)))) | ~v1_funct_2(F_540, u1_struct_0(D_539), u1_struct_0(B_542)) | ~v1_funct_1(F_540) | ~m1_subset_1(E_541, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_537), u1_struct_0(B_542)))) | ~v1_funct_2(E_541, u1_struct_0(C_537), u1_struct_0(B_542)) | ~v1_funct_1(E_541) | r1_tsep_1(C_537, D_539) | ~m1_pre_topc(D_539, A_538) | v2_struct_0(D_539) | ~m1_pre_topc(C_537, A_538) | v2_struct_0(C_537) | ~l1_pre_topc(B_542) | ~v2_pre_topc(B_542) | v2_struct_0(B_542) | ~l1_pre_topc(A_538) | ~v2_pre_topc(A_538) | v2_struct_0(A_538))), inference(cnfTransformation, [status(thm)], [f_245])).
% 6.34/2.18  tff(c_1393, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_1388])).
% 6.34/2.18  tff(c_1397, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_74, c_72, c_68, c_66, c_64, c_60, c_1393])).
% 6.34/2.18  tff(c_1398, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_76, c_1397])).
% 6.34/2.18  tff(c_4, plain, (![D_4, C_3, A_1, B_2]: (D_4=C_3 | ~r2_funct_2(A_1, B_2, C_3, D_4) | ~m1_subset_1(D_4, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(D_4, A_1, B_2) | ~v1_funct_1(D_4) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))) | ~v1_funct_2(C_3, A_1, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.34/2.18  tff(c_1400, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1398, c_4])).
% 6.34/2.18  tff(c_1403, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_1400])).
% 6.34/2.18  tff(c_1416, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1403])).
% 6.34/2.18  tff(c_1419, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_670, c_1416])).
% 6.34/2.18  tff(c_1422, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_1419])).
% 6.34/2.18  tff(c_1423, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_1422])).
% 6.34/2.18  tff(c_1426, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1423])).
% 6.34/2.18  tff(c_1429, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_82, c_78, c_1426])).
% 6.34/2.18  tff(c_1431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_1429])).
% 6.34/2.18  tff(c_1433, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_1403])).
% 6.34/2.18  tff(c_18, plain, (![E_18, C_16, D_17, A_14, B_15]: (m1_subset_1(k3_tmap_1(A_14, B_15, C_16, D_17, E_18), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_17), u1_struct_0(B_15)))) | ~m1_subset_1(E_18, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_16), u1_struct_0(B_15)))) | ~v1_funct_2(E_18, u1_struct_0(C_16), u1_struct_0(B_15)) | ~v1_funct_1(E_18) | ~m1_pre_topc(D_17, A_14) | ~m1_pre_topc(C_16, A_14) | ~l1_pre_topc(B_15) | ~v2_pre_topc(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_135])).
% 6.34/2.18  tff(c_1432, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1403])).
% 6.34/2.18  tff(c_1434, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1432])).
% 6.34/2.18  tff(c_1446, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1434])).
% 6.34/2.18  tff(c_1453, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_215, c_638, c_464, c_1446])).
% 6.34/2.18  tff(c_1454, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_1453])).
% 6.34/2.18  tff(c_1457, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1454])).
% 6.34/2.18  tff(c_1460, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_82, c_78, c_1457])).
% 6.34/2.18  tff(c_1462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_1460])).
% 6.34/2.18  tff(c_1464, plain, (m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_1432])).
% 6.34/2.18  tff(c_682, plain, (![D_391, B_393, F_392, A_395, C_394, E_396]: (v1_funct_1(k10_tmap_1(A_395, B_393, C_394, D_391, E_396, F_392)) | ~m1_subset_1(F_392, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_391), u1_struct_0(B_393)))) | ~v1_funct_2(F_392, u1_struct_0(D_391), u1_struct_0(B_393)) | ~v1_funct_1(F_392) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394), u1_struct_0(B_393)))) | ~v1_funct_2(E_396, u1_struct_0(C_394), u1_struct_0(B_393)) | ~v1_funct_1(E_396) | ~m1_pre_topc(D_391, A_395) | v2_struct_0(D_391) | ~m1_pre_topc(C_394, A_395) | v2_struct_0(C_394) | ~l1_pre_topc(B_393) | ~v2_pre_topc(B_393) | v2_struct_0(B_393) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.34/2.18  tff(c_690, plain, (![A_395, C_394, E_396]: (v1_funct_1(k10_tmap_1(A_395, '#skF_2', C_394, '#skF_3', E_396, '#skF_5')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_396, u1_struct_0(C_394), u1_struct_0('#skF_2')) | ~v1_funct_1(E_396) | ~m1_pre_topc('#skF_3', A_395) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_394, A_395) | v2_struct_0(C_394) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(resolution, [status(thm)], [c_68, c_682])).
% 6.34/2.18  tff(c_702, plain, (![A_395, C_394, E_396]: (v1_funct_1(k10_tmap_1(A_395, '#skF_2', C_394, '#skF_3', E_396, '#skF_5')) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_396, u1_struct_0(C_394), u1_struct_0('#skF_2')) | ~v1_funct_1(E_396) | ~m1_pre_topc('#skF_3', A_395) | v2_struct_0('#skF_3') | ~m1_pre_topc(C_394, A_395) | v2_struct_0(C_394) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_72, c_690])).
% 6.34/2.18  tff(c_703, plain, (![A_395, C_394, E_396]: (v1_funct_1(k10_tmap_1(A_395, '#skF_2', C_394, '#skF_3', E_396, '#skF_5')) | ~m1_subset_1(E_396, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_394), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_396, u1_struct_0(C_394), u1_struct_0('#skF_2')) | ~v1_funct_1(E_396) | ~m1_pre_topc('#skF_3', A_395) | ~m1_pre_topc(C_394, A_395) | v2_struct_0(C_394) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_702])).
% 6.34/2.18  tff(c_1470, plain, (![A_395]: (v1_funct_1(k10_tmap_1(A_395, '#skF_2', '#skF_3', '#skF_3', k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc('#skF_3', A_395) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(resolution, [status(thm)], [c_1464, c_703])).
% 6.34/2.18  tff(c_1490, plain, (![A_395]: (v1_funct_1(k10_tmap_1(A_395, '#skF_2', '#skF_3', '#skF_3', k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', A_395) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(demodulation, [status(thm), theory('equality')], [c_1433, c_1470])).
% 6.34/2.18  tff(c_1491, plain, (![A_395]: (v1_funct_1(k10_tmap_1(A_395, '#skF_2', '#skF_3', '#skF_3', k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_pre_topc('#skF_3', A_395) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(negUnitSimplification, [status(thm)], [c_84, c_1490])).
% 6.34/2.18  tff(c_1511, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1491])).
% 6.34/2.18  tff(c_1514, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_657, c_1511])).
% 6.34/2.18  tff(c_1517, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_1514])).
% 6.34/2.18  tff(c_1518, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_1517])).
% 6.34/2.18  tff(c_1521, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1518])).
% 6.34/2.18  tff(c_1524, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_82, c_78, c_1521])).
% 6.34/2.18  tff(c_1526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_1524])).
% 6.34/2.18  tff(c_1528, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1491])).
% 6.34/2.18  tff(c_1463, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1432])).
% 6.34/2.18  tff(c_1549, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1528, c_1463])).
% 6.34/2.18  tff(c_70, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_1086, plain, (![F_492, E_493, B_494, D_491, C_489, A_490]: (r2_funct_2(u1_struct_0(D_491), u1_struct_0(B_494), k3_tmap_1(A_490, B_494, k1_tsep_1(A_490, C_489, D_491), D_491, k10_tmap_1(A_490, B_494, C_489, D_491, E_493, F_492)), F_492) | ~r2_funct_2(u1_struct_0(k2_tsep_1(A_490, C_489, D_491)), u1_struct_0(B_494), k3_tmap_1(A_490, B_494, C_489, k2_tsep_1(A_490, C_489, D_491), E_493), k3_tmap_1(A_490, B_494, D_491, k2_tsep_1(A_490, C_489, D_491), F_492)) | ~m1_subset_1(F_492, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_491), u1_struct_0(B_494)))) | ~v1_funct_2(F_492, u1_struct_0(D_491), u1_struct_0(B_494)) | ~v1_funct_1(F_492) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_489), u1_struct_0(B_494)))) | ~v1_funct_2(E_493, u1_struct_0(C_489), u1_struct_0(B_494)) | ~v1_funct_1(E_493) | r1_tsep_1(C_489, D_491) | ~m1_pre_topc(D_491, A_490) | v2_struct_0(D_491) | ~m1_pre_topc(C_489, A_490) | v2_struct_0(C_489) | ~l1_pre_topc(B_494) | ~v2_pre_topc(B_494) | v2_struct_0(B_494) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(cnfTransformation, [status(thm)], [f_245])).
% 6.34/2.18  tff(c_1091, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_58, c_1086])).
% 6.34/2.18  tff(c_1095, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6') | r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_74, c_72, c_68, c_66, c_64, c_60, c_1091])).
% 6.34/2.18  tff(c_1096, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_76, c_1095])).
% 6.34/2.18  tff(c_1098, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_1096, c_4])).
% 6.34/2.18  tff(c_1101, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_1098])).
% 6.34/2.18  tff(c_1167, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_1101])).
% 6.34/2.18  tff(c_1181, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_670, c_1167])).
% 6.34/2.18  tff(c_1184, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_78, c_1181])).
% 6.34/2.18  tff(c_1185, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_1184])).
% 6.34/2.18  tff(c_1188, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1185])).
% 6.34/2.18  tff(c_1191, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_82, c_78, c_1188])).
% 6.34/2.18  tff(c_1193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_1191])).
% 6.34/2.18  tff(c_1194, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1101])).
% 6.34/2.18  tff(c_1204, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1194])).
% 6.34/2.18  tff(c_1210, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1204])).
% 6.34/2.18  tff(c_1217, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_78, c_215, c_638, c_464, c_1210])).
% 6.34/2.18  tff(c_1218, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_1217])).
% 6.34/2.18  tff(c_1221, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1218])).
% 6.34/2.18  tff(c_1224, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_82, c_78, c_1221])).
% 6.34/2.18  tff(c_1226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_1224])).
% 6.34/2.18  tff(c_1227, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1194])).
% 6.34/2.18  tff(c_1275, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1227])).
% 6.34/2.18  tff(c_1289, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_657, c_1275])).
% 6.34/2.18  tff(c_1292, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_78, c_1289])).
% 6.34/2.18  tff(c_1293, plain, (~m1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_96, c_1292])).
% 6.34/2.18  tff(c_1296, plain, (~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1293])).
% 6.34/2.18  tff(c_1299, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_82, c_78, c_1296])).
% 6.34/2.18  tff(c_1301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_84, c_80, c_1299])).
% 6.34/2.18  tff(c_1302, plain, (k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1227])).
% 6.34/2.18  tff(c_62, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_306])).
% 6.34/2.18  tff(c_1675, plain, (![E_572, D_569, A_570, B_571, C_568]: (v5_pre_topc(E_572, k1_tsep_1(A_570, C_568, D_569), B_571) | ~m1_subset_1(k3_tmap_1(A_570, B_571, k1_tsep_1(A_570, C_568, D_569), D_569, E_572), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_569), u1_struct_0(B_571)))) | ~v5_pre_topc(k3_tmap_1(A_570, B_571, k1_tsep_1(A_570, C_568, D_569), D_569, E_572), D_569, B_571) | ~v1_funct_2(k3_tmap_1(A_570, B_571, k1_tsep_1(A_570, C_568, D_569), D_569, E_572), u1_struct_0(D_569), u1_struct_0(B_571)) | ~v1_funct_1(k3_tmap_1(A_570, B_571, k1_tsep_1(A_570, C_568, D_569), D_569, E_572)) | ~m1_subset_1(k3_tmap_1(A_570, B_571, k1_tsep_1(A_570, C_568, D_569), C_568, E_572), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_568), u1_struct_0(B_571)))) | ~v5_pre_topc(k3_tmap_1(A_570, B_571, k1_tsep_1(A_570, C_568, D_569), C_568, E_572), C_568, B_571) | ~v1_funct_2(k3_tmap_1(A_570, B_571, k1_tsep_1(A_570, C_568, D_569), C_568, E_572), u1_struct_0(C_568), u1_struct_0(B_571)) | ~v1_funct_1(k3_tmap_1(A_570, B_571, k1_tsep_1(A_570, C_568, D_569), C_568, E_572)) | ~m1_subset_1(E_572, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_570, C_568, D_569)), u1_struct_0(B_571)))) | ~v1_funct_2(E_572, u1_struct_0(k1_tsep_1(A_570, C_568, D_569)), u1_struct_0(B_571)) | ~v1_funct_1(E_572) | ~r4_tsep_1(A_570, C_568, D_569) | ~m1_pre_topc(D_569, A_570) | v2_struct_0(D_569) | ~m1_pre_topc(C_568, A_570) | v2_struct_0(C_568) | ~l1_pre_topc(B_571) | ~v2_pre_topc(B_571) | v2_struct_0(B_571) | ~l1_pre_topc(A_570) | ~v2_pre_topc(A_570) | v2_struct_0(A_570))), inference(cnfTransformation, [status(thm)], [f_195])).
% 6.34/2.18  tff(c_1677, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1302, c_1675])).
% 6.34/2.18  tff(c_1687, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_88, c_86, c_82, c_78, c_56, c_215, c_638, c_464, c_74, c_1549, c_72, c_1549, c_70, c_1549, c_68, c_1549, c_66, c_1302, c_64, c_1302, c_62, c_1302, c_60, c_1677])).
% 6.34/2.18  tff(c_1689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_90, c_84, c_80, c_637, c_1687])).
% 6.34/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.34/2.18  
% 6.34/2.18  Inference rules
% 6.34/2.18  ----------------------
% 6.34/2.18  #Ref     : 0
% 6.34/2.18  #Sup     : 272
% 6.34/2.18  #Fact    : 0
% 6.34/2.18  #Define  : 0
% 6.34/2.18  #Split   : 11
% 6.34/2.18  #Chain   : 0
% 6.34/2.18  #Close   : 0
% 6.34/2.18  
% 6.34/2.18  Ordering : KBO
% 6.34/2.18  
% 6.34/2.18  Simplification rules
% 6.34/2.18  ----------------------
% 6.34/2.18  #Subsume      : 49
% 6.34/2.18  #Demod        : 895
% 6.34/2.18  #Tautology    : 34
% 6.34/2.18  #SimpNegUnit  : 150
% 6.34/2.18  #BackRed      : 8
% 6.34/2.18  
% 6.34/2.18  #Partial instantiations: 0
% 6.34/2.18  #Strategies tried      : 1
% 6.34/2.18  
% 6.34/2.18  Timing (in seconds)
% 6.34/2.18  ----------------------
% 6.34/2.18  Preprocessing        : 0.47
% 6.34/2.18  Parsing              : 0.22
% 6.34/2.18  CNF conversion       : 0.08
% 6.34/2.18  Main loop            : 0.91
% 6.34/2.18  Inferencing          : 0.31
% 6.34/2.18  Reduction            : 0.29
% 6.34/2.18  Demodulation         : 0.22
% 6.34/2.18  BG Simplification    : 0.05
% 6.34/2.18  Subsumption          : 0.22
% 6.34/2.18  Abstraction          : 0.04
% 6.34/2.18  MUC search           : 0.00
% 6.34/2.18  Cooper               : 0.00
% 6.34/2.18  Total                : 1.44
% 6.34/2.18  Index Insertion      : 0.00
% 6.34/2.18  Index Deletion       : 0.00
% 6.34/2.18  Index Matching       : 0.00
% 6.34/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
