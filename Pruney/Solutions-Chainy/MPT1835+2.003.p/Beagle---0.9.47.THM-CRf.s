%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:12 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 400 expanded)
%              Number of leaves         :   32 ( 178 expanded)
%              Depth                    :   15
%              Number of atoms          :  631 (4752 expanded)
%              Number of equality atoms :    2 ( 151 expanded)
%              Maximal formula depth    :   29 (   8 average)
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

tff(f_296,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_tmap_1)).

tff(f_67,axiom,(
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

tff(f_234,axiom,(
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
                           => ( r4_tsep_1(A,C,D)
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),k1_tsep_1(A,C,D),B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A,C,D)),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_tmap_1)).

tff(f_117,axiom,(
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

tff(f_177,axiom,(
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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_42,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_54,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_207,plain,(
    ! [C_305,D_303,E_302,F_301,A_306,B_304] :
      ( m1_subset_1(k10_tmap_1(A_306,B_304,C_305,D_303,E_302,F_301),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_306,C_305,D_303)),u1_struct_0(B_304))))
      | ~ m1_subset_1(F_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_303),u1_struct_0(B_304))))
      | ~ v1_funct_2(F_301,u1_struct_0(D_303),u1_struct_0(B_304))
      | ~ v1_funct_1(F_301)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_305),u1_struct_0(B_304))))
      | ~ v1_funct_2(E_302,u1_struct_0(C_305),u1_struct_0(B_304))
      | ~ v1_funct_1(E_302)
      | ~ m1_pre_topc(D_303,A_306)
      | v2_struct_0(D_303)
      | ~ m1_pre_topc(C_305,A_306)
      | v2_struct_0(C_305)
      | ~ l1_pre_topc(B_304)
      | ~ v2_pre_topc(B_304)
      | v2_struct_0(B_304)
      | ~ l1_pre_topc(A_306)
      | ~ v2_pre_topc(A_306)
      | v2_struct_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_218,plain,(
    ! [B_304,E_302,F_301] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_304,'#skF_3','#skF_4',E_302,F_301),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_304))))
      | ~ m1_subset_1(F_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_304))))
      | ~ v1_funct_2(F_301,u1_struct_0('#skF_4'),u1_struct_0(B_304))
      | ~ v1_funct_1(F_301)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_304))))
      | ~ v1_funct_2(E_302,u1_struct_0('#skF_3'),u1_struct_0(B_304))
      | ~ v1_funct_1(E_302)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_304)
      | ~ v2_pre_topc(B_304)
      | v2_struct_0(B_304)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_207])).

tff(c_229,plain,(
    ! [B_304,E_302,F_301] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_304,'#skF_3','#skF_4',E_302,F_301),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_304))))
      | ~ m1_subset_1(F_301,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_304))))
      | ~ v1_funct_2(F_301,u1_struct_0('#skF_4'),u1_struct_0(B_304))
      | ~ v1_funct_1(F_301)
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_304))))
      | ~ v1_funct_2(E_302,u1_struct_0('#skF_3'),u1_struct_0(B_304))
      | ~ v1_funct_1(E_302)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_304)
      | ~ v2_pre_topc(B_304)
      | v2_struct_0(B_304)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_218])).

tff(c_231,plain,(
    ! [B_307,E_308,F_309] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_307,'#skF_3','#skF_4',E_308,F_309),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_307))))
      | ~ m1_subset_1(F_309,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_307))))
      | ~ v1_funct_2(F_309,u1_struct_0('#skF_4'),u1_struct_0(B_307))
      | ~ v1_funct_1(F_309)
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_307))))
      | ~ v1_funct_2(E_308,u1_struct_0('#skF_3'),u1_struct_0(B_307))
      | ~ v1_funct_1(E_308)
      | ~ l1_pre_topc(B_307)
      | ~ v2_pre_topc(B_307)
      | v2_struct_0(B_307) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_62,c_58,c_229])).

tff(c_82,plain,(
    ! [A_258,B_256,F_253,D_255,C_257,E_254] :
      ( v1_funct_1(k10_tmap_1(A_258,B_256,C_257,D_255,E_254,F_253))
      | ~ m1_subset_1(F_253,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_255),u1_struct_0(B_256))))
      | ~ v1_funct_2(F_253,u1_struct_0(D_255),u1_struct_0(B_256))
      | ~ v1_funct_1(F_253)
      | ~ m1_subset_1(E_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257),u1_struct_0(B_256))))
      | ~ v1_funct_2(E_254,u1_struct_0(C_257),u1_struct_0(B_256))
      | ~ v1_funct_1(E_254)
      | ~ m1_pre_topc(D_255,A_258)
      | v2_struct_0(D_255)
      | ~ m1_pre_topc(C_257,A_258)
      | v2_struct_0(C_257)
      | ~ l1_pre_topc(B_256)
      | ~ v2_pre_topc(B_256)
      | v2_struct_0(B_256)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_86,plain,(
    ! [A_258,C_257,E_254] :
      ( v1_funct_1(k10_tmap_1(A_258,'#skF_2',C_257,'#skF_4',E_254,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_254,u1_struct_0(C_257),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_254)
      | ~ m1_pre_topc('#skF_4',A_258)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_257,A_258)
      | v2_struct_0(C_257)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258) ) ),
    inference(resolution,[status(thm)],[c_38,c_82])).

tff(c_93,plain,(
    ! [A_258,C_257,E_254] :
      ( v1_funct_1(k10_tmap_1(A_258,'#skF_2',C_257,'#skF_4',E_254,'#skF_6'))
      | ~ m1_subset_1(E_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_254,u1_struct_0(C_257),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_254)
      | ~ m1_pre_topc('#skF_4',A_258)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_257,A_258)
      | v2_struct_0(C_257)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_44,c_42,c_86])).

tff(c_117,plain,(
    ! [A_270,C_271,E_272] :
      ( v1_funct_1(k10_tmap_1(A_270,'#skF_2',C_271,'#skF_4',E_272,'#skF_6'))
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_271),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_272,u1_struct_0(C_271),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_272)
      | ~ m1_pre_topc('#skF_4',A_270)
      | ~ m1_pre_topc(C_271,A_270)
      | v2_struct_0(C_271)
      | ~ l1_pre_topc(A_270)
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_93])).

tff(c_119,plain,(
    ! [A_270] :
      ( v1_funct_1(k10_tmap_1(A_270,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_270)
      | ~ m1_pre_topc('#skF_3',A_270)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_270)
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270) ) ),
    inference(resolution,[status(thm)],[c_46,c_117])).

tff(c_124,plain,(
    ! [A_270] :
      ( v1_funct_1(k10_tmap_1(A_270,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_270)
      | ~ m1_pre_topc('#skF_3',A_270)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_270)
      | ~ v2_pre_topc(A_270)
      | v2_struct_0(A_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_119])).

tff(c_131,plain,(
    ! [A_274] :
      ( v1_funct_1(k10_tmap_1(A_274,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ m1_pre_topc('#skF_3',A_274)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_124])).

tff(c_30,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_81,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_134,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_131,c_81])).

tff(c_137,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_134])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_137])).

tff(c_140,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_142,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_242,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_231,c_142])).

tff(c_256,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_50,c_46,c_44,c_42,c_38,c_242])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_256])).

tff(c_259,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_261,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_302,plain,(
    ! [A_326,F_321,E_322,D_323,C_325,B_324] :
      ( v1_funct_2(k10_tmap_1(A_326,B_324,C_325,D_323,E_322,F_321),u1_struct_0(k1_tsep_1(A_326,C_325,D_323)),u1_struct_0(B_324))
      | ~ m1_subset_1(F_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_323),u1_struct_0(B_324))))
      | ~ v1_funct_2(F_321,u1_struct_0(D_323),u1_struct_0(B_324))
      | ~ v1_funct_1(F_321)
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_325),u1_struct_0(B_324))))
      | ~ v1_funct_2(E_322,u1_struct_0(C_325),u1_struct_0(B_324))
      | ~ v1_funct_1(E_322)
      | ~ m1_pre_topc(D_323,A_326)
      | v2_struct_0(D_323)
      | ~ m1_pre_topc(C_325,A_326)
      | v2_struct_0(C_325)
      | ~ l1_pre_topc(B_324)
      | ~ v2_pre_topc(B_324)
      | v2_struct_0(B_324)
      | ~ l1_pre_topc(A_326)
      | ~ v2_pre_topc(A_326)
      | v2_struct_0(A_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_305,plain,(
    ! [B_324,E_322,F_321] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_324,'#skF_3','#skF_4',E_322,F_321),u1_struct_0('#skF_1'),u1_struct_0(B_324))
      | ~ m1_subset_1(F_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_324))))
      | ~ v1_funct_2(F_321,u1_struct_0('#skF_4'),u1_struct_0(B_324))
      | ~ v1_funct_1(F_321)
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_324))))
      | ~ v1_funct_2(E_322,u1_struct_0('#skF_3'),u1_struct_0(B_324))
      | ~ v1_funct_1(E_322)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_324)
      | ~ v2_pre_topc(B_324)
      | v2_struct_0(B_324)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_302])).

tff(c_307,plain,(
    ! [B_324,E_322,F_321] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_324,'#skF_3','#skF_4',E_322,F_321),u1_struct_0('#skF_1'),u1_struct_0(B_324))
      | ~ m1_subset_1(F_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_324))))
      | ~ v1_funct_2(F_321,u1_struct_0('#skF_4'),u1_struct_0(B_324))
      | ~ v1_funct_1(F_321)
      | ~ m1_subset_1(E_322,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_324))))
      | ~ v1_funct_2(E_322,u1_struct_0('#skF_3'),u1_struct_0(B_324))
      | ~ v1_funct_1(E_322)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_324)
      | ~ v2_pre_topc(B_324)
      | v2_struct_0(B_324)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_305])).

tff(c_330,plain,(
    ! [B_332,E_333,F_334] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_332,'#skF_3','#skF_4',E_333,F_334),u1_struct_0('#skF_1'),u1_struct_0(B_332))
      | ~ m1_subset_1(F_334,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_332))))
      | ~ v1_funct_2(F_334,u1_struct_0('#skF_4'),u1_struct_0(B_332))
      | ~ v1_funct_1(F_334)
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_332))))
      | ~ v1_funct_2(E_333,u1_struct_0('#skF_3'),u1_struct_0(B_332))
      | ~ v1_funct_1(E_333)
      | ~ l1_pre_topc(B_332)
      | ~ v2_pre_topc(B_332)
      | v2_struct_0(B_332) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_62,c_58,c_307])).

tff(c_332,plain,(
    ! [E_333] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_333,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_333,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_333)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_330])).

tff(c_335,plain,(
    ! [E_333] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_333,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_333,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_333)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_44,c_42,c_332])).

tff(c_337,plain,(
    ! [E_335] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_335,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_335,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_335,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_335) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_335])).

tff(c_340,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_337])).

tff(c_343,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_340])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_343])).

tff(c_346,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_32,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_48,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_40,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_530,plain,(
    ! [F_388,A_391,E_393,C_392,B_390,D_389] :
      ( v5_pre_topc(k10_tmap_1(A_391,B_390,C_392,D_389,E_393,F_388),k1_tsep_1(A_391,C_392,D_389),B_390)
      | ~ r4_tsep_1(A_391,C_392,D_389)
      | ~ m1_subset_1(F_388,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_389),u1_struct_0(B_390))))
      | ~ v5_pre_topc(F_388,D_389,B_390)
      | ~ v1_funct_2(F_388,u1_struct_0(D_389),u1_struct_0(B_390))
      | ~ v1_funct_1(F_388)
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_392),u1_struct_0(B_390))))
      | ~ v5_pre_topc(E_393,C_392,B_390)
      | ~ v1_funct_2(E_393,u1_struct_0(C_392),u1_struct_0(B_390))
      | ~ v1_funct_1(E_393)
      | ~ r1_tsep_1(C_392,D_389)
      | ~ m1_pre_topc(D_389,A_391)
      | v2_struct_0(D_389)
      | ~ m1_pre_topc(C_392,A_391)
      | v2_struct_0(C_392)
      | ~ l1_pre_topc(B_390)
      | ~ v2_pre_topc(B_390)
      | v2_struct_0(B_390)
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_540,plain,(
    ! [A_391,C_392,E_393] :
      ( v5_pre_topc(k10_tmap_1(A_391,'#skF_2',C_392,'#skF_4',E_393,'#skF_6'),k1_tsep_1(A_391,C_392,'#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_391,C_392,'#skF_4')
      | ~ v5_pre_topc('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_392),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(E_393,C_392,'#skF_2')
      | ~ v1_funct_2(E_393,u1_struct_0(C_392),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_393)
      | ~ r1_tsep_1(C_392,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_391)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_392,A_391)
      | v2_struct_0(C_392)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391) ) ),
    inference(resolution,[status(thm)],[c_38,c_530])).

tff(c_555,plain,(
    ! [A_391,C_392,E_393] :
      ( v5_pre_topc(k10_tmap_1(A_391,'#skF_2',C_392,'#skF_4',E_393,'#skF_6'),k1_tsep_1(A_391,C_392,'#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_391,C_392,'#skF_4')
      | ~ m1_subset_1(E_393,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_392),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(E_393,C_392,'#skF_2')
      | ~ v1_funct_2(E_393,u1_struct_0(C_392),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_393)
      | ~ r1_tsep_1(C_392,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_391)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_392,A_391)
      | v2_struct_0(C_392)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_44,c_42,c_40,c_540])).

tff(c_593,plain,(
    ! [A_403,C_404,E_405] :
      ( v5_pre_topc(k10_tmap_1(A_403,'#skF_2',C_404,'#skF_4',E_405,'#skF_6'),k1_tsep_1(A_403,C_404,'#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_403,C_404,'#skF_4')
      | ~ m1_subset_1(E_405,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_404),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(E_405,C_404,'#skF_2')
      | ~ v1_funct_2(E_405,u1_struct_0(C_404),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_405)
      | ~ r1_tsep_1(C_404,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_403)
      | ~ m1_pre_topc(C_404,A_403)
      | v2_struct_0(C_404)
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | v2_struct_0(A_403) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_58,c_555])).

tff(c_603,plain,(
    ! [A_403] :
      ( v5_pre_topc(k10_tmap_1(A_403,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_403,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_403,'#skF_3','#skF_4')
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_403)
      | ~ m1_pre_topc('#skF_3',A_403)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | v2_struct_0(A_403) ) ),
    inference(resolution,[status(thm)],[c_46,c_593])).

tff(c_620,plain,(
    ! [A_403] :
      ( v5_pre_topc(k10_tmap_1(A_403,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_403,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_403,'#skF_3','#skF_4')
      | ~ r1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_403)
      | ~ m1_pre_topc('#skF_3',A_403)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | v2_struct_0(A_403) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_603])).

tff(c_621,plain,(
    ! [A_403] :
      ( v5_pre_topc(k10_tmap_1(A_403,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_403,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_403,'#skF_3','#skF_4')
      | ~ r1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_403)
      | ~ m1_pre_topc('#skF_3',A_403)
      | ~ l1_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | v2_struct_0(A_403) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_620])).

tff(c_627,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_36,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_75,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_36])).

tff(c_34,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_296])).

tff(c_76,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_34])).

tff(c_685,plain,(
    ! [B_438,F_441,E_436,C_437,D_440,A_439] :
      ( r2_funct_2(u1_struct_0(k2_tsep_1(A_439,C_437,D_440)),u1_struct_0(B_438),k3_tmap_1(A_439,B_438,C_437,k2_tsep_1(A_439,C_437,D_440),E_436),k3_tmap_1(A_439,B_438,D_440,k2_tsep_1(A_439,C_437,D_440),F_441))
      | ~ r2_funct_2(u1_struct_0(D_440),u1_struct_0(B_438),k3_tmap_1(A_439,B_438,k1_tsep_1(A_439,C_437,D_440),D_440,k10_tmap_1(A_439,B_438,C_437,D_440,E_436,F_441)),F_441)
      | ~ r2_funct_2(u1_struct_0(C_437),u1_struct_0(B_438),k3_tmap_1(A_439,B_438,k1_tsep_1(A_439,C_437,D_440),C_437,k10_tmap_1(A_439,B_438,C_437,D_440,E_436,F_441)),E_436)
      | ~ m1_subset_1(F_441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_440),u1_struct_0(B_438))))
      | ~ v1_funct_2(F_441,u1_struct_0(D_440),u1_struct_0(B_438))
      | ~ v1_funct_1(F_441)
      | ~ m1_subset_1(E_436,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_437),u1_struct_0(B_438))))
      | ~ v1_funct_2(E_436,u1_struct_0(C_437),u1_struct_0(B_438))
      | ~ v1_funct_1(E_436)
      | r1_tsep_1(C_437,D_440)
      | ~ m1_pre_topc(D_440,A_439)
      | v2_struct_0(D_440)
      | ~ m1_pre_topc(C_437,A_439)
      | v2_struct_0(C_437)
      | ~ l1_pre_topc(B_438)
      | ~ v2_pre_topc(B_438)
      | v2_struct_0(B_438)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439)
      | v2_struct_0(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_687,plain,(
    ! [B_438,E_436,F_441] :
      ( r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_438),k3_tmap_1('#skF_1',B_438,'#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),E_436),k3_tmap_1('#skF_1',B_438,'#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),F_441))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_438),k3_tmap_1('#skF_1',B_438,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_438,'#skF_3','#skF_4',E_436,F_441)),F_441)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_438),k3_tmap_1('#skF_1',B_438,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_438,'#skF_3','#skF_4',E_436,F_441)),E_436)
      | ~ m1_subset_1(F_441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_438))))
      | ~ v1_funct_2(F_441,u1_struct_0('#skF_4'),u1_struct_0(B_438))
      | ~ v1_funct_1(F_441)
      | ~ m1_subset_1(E_436,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_438))))
      | ~ v1_funct_2(E_436,u1_struct_0('#skF_3'),u1_struct_0(B_438))
      | ~ v1_funct_1(E_436)
      | r1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_438)
      | ~ v2_pre_topc(B_438)
      | v2_struct_0(B_438)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_685])).

tff(c_689,plain,(
    ! [B_438,E_436,F_441] :
      ( r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_438),k3_tmap_1('#skF_1',B_438,'#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),E_436),k3_tmap_1('#skF_1',B_438,'#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),F_441))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_438),k3_tmap_1('#skF_1',B_438,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_438,'#skF_3','#skF_4',E_436,F_441)),F_441)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_438),k3_tmap_1('#skF_1',B_438,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_438,'#skF_3','#skF_4',E_436,F_441)),E_436)
      | ~ m1_subset_1(F_441,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_438))))
      | ~ v1_funct_2(F_441,u1_struct_0('#skF_4'),u1_struct_0(B_438))
      | ~ v1_funct_1(F_441)
      | ~ m1_subset_1(E_436,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_438))))
      | ~ v1_funct_2(E_436,u1_struct_0('#skF_3'),u1_struct_0(B_438))
      | ~ v1_funct_1(E_436)
      | r1_tsep_1('#skF_3','#skF_4')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_438)
      | ~ v2_pre_topc(B_438)
      | v2_struct_0(B_438)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_54,c_687])).

tff(c_802,plain,(
    ! [B_466,E_467,F_468] :
      ( r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_466),k3_tmap_1('#skF_1',B_466,'#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),E_467),k3_tmap_1('#skF_1',B_466,'#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),F_468))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_466),k3_tmap_1('#skF_1',B_466,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_466,'#skF_3','#skF_4',E_467,F_468)),F_468)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_466),k3_tmap_1('#skF_1',B_466,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_466,'#skF_3','#skF_4',E_467,F_468)),E_467)
      | ~ m1_subset_1(F_468,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_466))))
      | ~ v1_funct_2(F_468,u1_struct_0('#skF_4'),u1_struct_0(B_466))
      | ~ v1_funct_1(F_468)
      | ~ m1_subset_1(E_467,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_466))))
      | ~ v1_funct_2(E_467,u1_struct_0('#skF_3'),u1_struct_0(B_466))
      | ~ v1_funct_1(E_467)
      | ~ l1_pre_topc(B_466)
      | ~ v2_pre_topc(B_466)
      | v2_struct_0(B_466) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_62,c_58,c_627,c_689])).

tff(c_804,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6'))
    | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_76,c_802])).

tff(c_807,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_52,c_50,c_46,c_44,c_42,c_38,c_75,c_804])).

tff(c_808,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_807])).

tff(c_16,plain,(
    ! [D_126,E_130,A_70,B_102,F_132,C_118] :
      ( v5_pre_topc(k10_tmap_1(A_70,B_102,C_118,D_126,E_130,F_132),k1_tsep_1(A_70,C_118,D_126),B_102)
      | ~ r4_tsep_1(A_70,C_118,D_126)
      | ~ r2_funct_2(u1_struct_0(k2_tsep_1(A_70,C_118,D_126)),u1_struct_0(B_102),k3_tmap_1(A_70,B_102,C_118,k2_tsep_1(A_70,C_118,D_126),E_130),k3_tmap_1(A_70,B_102,D_126,k2_tsep_1(A_70,C_118,D_126),F_132))
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_126),u1_struct_0(B_102))))
      | ~ v5_pre_topc(F_132,D_126,B_102)
      | ~ v1_funct_2(F_132,u1_struct_0(D_126),u1_struct_0(B_102))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_118),u1_struct_0(B_102))))
      | ~ v5_pre_topc(E_130,C_118,B_102)
      | ~ v1_funct_2(E_130,u1_struct_0(C_118),u1_struct_0(B_102))
      | ~ v1_funct_1(E_130)
      | r1_tsep_1(C_118,D_126)
      | ~ m1_pre_topc(D_126,A_70)
      | v2_struct_0(D_126)
      | ~ m1_pre_topc(C_118,A_70)
      | v2_struct_0(C_118)
      | ~ l1_pre_topc(B_102)
      | ~ v2_pre_topc(B_102)
      | v2_struct_0(B_102)
      | ~ l1_pre_topc(A_70)
      | ~ v2_pre_topc(A_70)
      | v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_811,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_6','#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
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
    inference(resolution,[status(thm)],[c_808,c_16])).

tff(c_818,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_32,c_54,c_811])).

tff(c_820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_627,c_346,c_818])).

tff(c_823,plain,(
    ! [A_469] :
      ( v5_pre_topc(k10_tmap_1(A_469,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_469,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_469,'#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ m1_pre_topc('#skF_3',A_469)
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_826,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_823])).

tff(c_828,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_60,c_56,c_32,c_826])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_346,c_828])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.96/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.96/1.80  
% 4.96/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.96/1.80  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.96/1.80  
% 4.96/1.80  %Foreground sorts:
% 4.96/1.80  
% 4.96/1.80  
% 4.96/1.80  %Background operators:
% 4.96/1.80  
% 4.96/1.80  
% 4.96/1.80  %Foreground operators:
% 4.96/1.80  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.96/1.80  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.96/1.80  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.96/1.80  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.96/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.96/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.96/1.80  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.96/1.80  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 4.96/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.96/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.96/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.96/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.96/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.96/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.96/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.96/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.96/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.96/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.96/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.96/1.80  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 4.96/1.80  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.96/1.80  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 4.96/1.80  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.96/1.80  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.96/1.80  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.96/1.80  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 4.96/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.96/1.80  
% 5.16/1.84  tff(f_296, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_tmap_1)).
% 5.16/1.84  tff(f_67, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 5.16/1.84  tff(f_234, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (r4_tsep_1(A, C, D) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_tmap_1)).
% 5.16/1.84  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_tmap_1)).
% 5.16/1.84  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_tmap_1)).
% 5.16/1.84  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_50, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_44, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_42, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_54, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_207, plain, (![C_305, D_303, E_302, F_301, A_306, B_304]: (m1_subset_1(k10_tmap_1(A_306, B_304, C_305, D_303, E_302, F_301), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_306, C_305, D_303)), u1_struct_0(B_304)))) | ~m1_subset_1(F_301, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_303), u1_struct_0(B_304)))) | ~v1_funct_2(F_301, u1_struct_0(D_303), u1_struct_0(B_304)) | ~v1_funct_1(F_301) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_305), u1_struct_0(B_304)))) | ~v1_funct_2(E_302, u1_struct_0(C_305), u1_struct_0(B_304)) | ~v1_funct_1(E_302) | ~m1_pre_topc(D_303, A_306) | v2_struct_0(D_303) | ~m1_pre_topc(C_305, A_306) | v2_struct_0(C_305) | ~l1_pre_topc(B_304) | ~v2_pre_topc(B_304) | v2_struct_0(B_304) | ~l1_pre_topc(A_306) | ~v2_pre_topc(A_306) | v2_struct_0(A_306))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.16/1.84  tff(c_218, plain, (![B_304, E_302, F_301]: (m1_subset_1(k10_tmap_1('#skF_1', B_304, '#skF_3', '#skF_4', E_302, F_301), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_304)))) | ~m1_subset_1(F_301, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_304)))) | ~v1_funct_2(F_301, u1_struct_0('#skF_4'), u1_struct_0(B_304)) | ~v1_funct_1(F_301) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_304)))) | ~v1_funct_2(E_302, u1_struct_0('#skF_3'), u1_struct_0(B_304)) | ~v1_funct_1(E_302) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_304) | ~v2_pre_topc(B_304) | v2_struct_0(B_304) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_207])).
% 5.16/1.84  tff(c_229, plain, (![B_304, E_302, F_301]: (m1_subset_1(k10_tmap_1('#skF_1', B_304, '#skF_3', '#skF_4', E_302, F_301), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_304)))) | ~m1_subset_1(F_301, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_304)))) | ~v1_funct_2(F_301, u1_struct_0('#skF_4'), u1_struct_0(B_304)) | ~v1_funct_1(F_301) | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_304)))) | ~v1_funct_2(E_302, u1_struct_0('#skF_3'), u1_struct_0(B_304)) | ~v1_funct_1(E_302) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_304) | ~v2_pre_topc(B_304) | v2_struct_0(B_304) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_218])).
% 5.16/1.84  tff(c_231, plain, (![B_307, E_308, F_309]: (m1_subset_1(k10_tmap_1('#skF_1', B_307, '#skF_3', '#skF_4', E_308, F_309), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_307)))) | ~m1_subset_1(F_309, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_307)))) | ~v1_funct_2(F_309, u1_struct_0('#skF_4'), u1_struct_0(B_307)) | ~v1_funct_1(F_309) | ~m1_subset_1(E_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_307)))) | ~v1_funct_2(E_308, u1_struct_0('#skF_3'), u1_struct_0(B_307)) | ~v1_funct_1(E_308) | ~l1_pre_topc(B_307) | ~v2_pre_topc(B_307) | v2_struct_0(B_307))), inference(negUnitSimplification, [status(thm)], [c_74, c_62, c_58, c_229])).
% 5.16/1.84  tff(c_82, plain, (![A_258, B_256, F_253, D_255, C_257, E_254]: (v1_funct_1(k10_tmap_1(A_258, B_256, C_257, D_255, E_254, F_253)) | ~m1_subset_1(F_253, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_255), u1_struct_0(B_256)))) | ~v1_funct_2(F_253, u1_struct_0(D_255), u1_struct_0(B_256)) | ~v1_funct_1(F_253) | ~m1_subset_1(E_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257), u1_struct_0(B_256)))) | ~v1_funct_2(E_254, u1_struct_0(C_257), u1_struct_0(B_256)) | ~v1_funct_1(E_254) | ~m1_pre_topc(D_255, A_258) | v2_struct_0(D_255) | ~m1_pre_topc(C_257, A_258) | v2_struct_0(C_257) | ~l1_pre_topc(B_256) | ~v2_pre_topc(B_256) | v2_struct_0(B_256) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.16/1.84  tff(c_86, plain, (![A_258, C_257, E_254]: (v1_funct_1(k10_tmap_1(A_258, '#skF_2', C_257, '#skF_4', E_254, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_254, u1_struct_0(C_257), u1_struct_0('#skF_2')) | ~v1_funct_1(E_254) | ~m1_pre_topc('#skF_4', A_258) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_257, A_258) | v2_struct_0(C_257) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258))), inference(resolution, [status(thm)], [c_38, c_82])).
% 5.16/1.84  tff(c_93, plain, (![A_258, C_257, E_254]: (v1_funct_1(k10_tmap_1(A_258, '#skF_2', C_257, '#skF_4', E_254, '#skF_6')) | ~m1_subset_1(E_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_257), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_254, u1_struct_0(C_257), u1_struct_0('#skF_2')) | ~v1_funct_1(E_254) | ~m1_pre_topc('#skF_4', A_258) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_257, A_258) | v2_struct_0(C_257) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_44, c_42, c_86])).
% 5.16/1.84  tff(c_117, plain, (![A_270, C_271, E_272]: (v1_funct_1(k10_tmap_1(A_270, '#skF_2', C_271, '#skF_4', E_272, '#skF_6')) | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_271), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_272, u1_struct_0(C_271), u1_struct_0('#skF_2')) | ~v1_funct_1(E_272) | ~m1_pre_topc('#skF_4', A_270) | ~m1_pre_topc(C_271, A_270) | v2_struct_0(C_271) | ~l1_pre_topc(A_270) | ~v2_pre_topc(A_270) | v2_struct_0(A_270))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_93])).
% 5.16/1.84  tff(c_119, plain, (![A_270]: (v1_funct_1(k10_tmap_1(A_270, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_270) | ~m1_pre_topc('#skF_3', A_270) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_270) | ~v2_pre_topc(A_270) | v2_struct_0(A_270))), inference(resolution, [status(thm)], [c_46, c_117])).
% 5.16/1.84  tff(c_124, plain, (![A_270]: (v1_funct_1(k10_tmap_1(A_270, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_270) | ~m1_pre_topc('#skF_3', A_270) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_270) | ~v2_pre_topc(A_270) | v2_struct_0(A_270))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_119])).
% 5.16/1.84  tff(c_131, plain, (![A_274]: (v1_funct_1(k10_tmap_1(A_274, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_274) | ~m1_pre_topc('#skF_3', A_274) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(negUnitSimplification, [status(thm)], [c_62, c_124])).
% 5.16/1.84  tff(c_30, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_81, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_30])).
% 5.16/1.84  tff(c_134, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_131, c_81])).
% 5.16/1.84  tff(c_137, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_134])).
% 5.16/1.84  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_137])).
% 5.16/1.84  tff(c_140, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_30])).
% 5.16/1.84  tff(c_142, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_140])).
% 5.16/1.84  tff(c_242, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_231, c_142])).
% 5.16/1.84  tff(c_256, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_50, c_46, c_44, c_42, c_38, c_242])).
% 5.16/1.84  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_256])).
% 5.16/1.84  tff(c_259, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_140])).
% 5.16/1.84  tff(c_261, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_259])).
% 5.16/1.84  tff(c_302, plain, (![A_326, F_321, E_322, D_323, C_325, B_324]: (v1_funct_2(k10_tmap_1(A_326, B_324, C_325, D_323, E_322, F_321), u1_struct_0(k1_tsep_1(A_326, C_325, D_323)), u1_struct_0(B_324)) | ~m1_subset_1(F_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_323), u1_struct_0(B_324)))) | ~v1_funct_2(F_321, u1_struct_0(D_323), u1_struct_0(B_324)) | ~v1_funct_1(F_321) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_325), u1_struct_0(B_324)))) | ~v1_funct_2(E_322, u1_struct_0(C_325), u1_struct_0(B_324)) | ~v1_funct_1(E_322) | ~m1_pre_topc(D_323, A_326) | v2_struct_0(D_323) | ~m1_pre_topc(C_325, A_326) | v2_struct_0(C_325) | ~l1_pre_topc(B_324) | ~v2_pre_topc(B_324) | v2_struct_0(B_324) | ~l1_pre_topc(A_326) | ~v2_pre_topc(A_326) | v2_struct_0(A_326))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.16/1.84  tff(c_305, plain, (![B_324, E_322, F_321]: (v1_funct_2(k10_tmap_1('#skF_1', B_324, '#skF_3', '#skF_4', E_322, F_321), u1_struct_0('#skF_1'), u1_struct_0(B_324)) | ~m1_subset_1(F_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_324)))) | ~v1_funct_2(F_321, u1_struct_0('#skF_4'), u1_struct_0(B_324)) | ~v1_funct_1(F_321) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_324)))) | ~v1_funct_2(E_322, u1_struct_0('#skF_3'), u1_struct_0(B_324)) | ~v1_funct_1(E_322) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_324) | ~v2_pre_topc(B_324) | v2_struct_0(B_324) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_302])).
% 5.16/1.84  tff(c_307, plain, (![B_324, E_322, F_321]: (v1_funct_2(k10_tmap_1('#skF_1', B_324, '#skF_3', '#skF_4', E_322, F_321), u1_struct_0('#skF_1'), u1_struct_0(B_324)) | ~m1_subset_1(F_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_324)))) | ~v1_funct_2(F_321, u1_struct_0('#skF_4'), u1_struct_0(B_324)) | ~v1_funct_1(F_321) | ~m1_subset_1(E_322, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_324)))) | ~v1_funct_2(E_322, u1_struct_0('#skF_3'), u1_struct_0(B_324)) | ~v1_funct_1(E_322) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_324) | ~v2_pre_topc(B_324) | v2_struct_0(B_324) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_305])).
% 5.16/1.84  tff(c_330, plain, (![B_332, E_333, F_334]: (v1_funct_2(k10_tmap_1('#skF_1', B_332, '#skF_3', '#skF_4', E_333, F_334), u1_struct_0('#skF_1'), u1_struct_0(B_332)) | ~m1_subset_1(F_334, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_332)))) | ~v1_funct_2(F_334, u1_struct_0('#skF_4'), u1_struct_0(B_332)) | ~v1_funct_1(F_334) | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_332)))) | ~v1_funct_2(E_333, u1_struct_0('#skF_3'), u1_struct_0(B_332)) | ~v1_funct_1(E_333) | ~l1_pre_topc(B_332) | ~v2_pre_topc(B_332) | v2_struct_0(B_332))), inference(negUnitSimplification, [status(thm)], [c_74, c_62, c_58, c_307])).
% 5.16/1.84  tff(c_332, plain, (![E_333]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_333, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_333, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_333) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_330])).
% 5.16/1.84  tff(c_335, plain, (![E_333]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_333, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_333, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_333) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_44, c_42, c_332])).
% 5.16/1.84  tff(c_337, plain, (![E_335]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_335, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_335, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_335, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_335))), inference(negUnitSimplification, [status(thm)], [c_68, c_335])).
% 5.16/1.84  tff(c_340, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_337])).
% 5.16/1.84  tff(c_343, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_340])).
% 5.16/1.84  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_343])).
% 5.16/1.84  tff(c_346, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_259])).
% 5.16/1.84  tff(c_32, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_48, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_40, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_530, plain, (![F_388, A_391, E_393, C_392, B_390, D_389]: (v5_pre_topc(k10_tmap_1(A_391, B_390, C_392, D_389, E_393, F_388), k1_tsep_1(A_391, C_392, D_389), B_390) | ~r4_tsep_1(A_391, C_392, D_389) | ~m1_subset_1(F_388, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_389), u1_struct_0(B_390)))) | ~v5_pre_topc(F_388, D_389, B_390) | ~v1_funct_2(F_388, u1_struct_0(D_389), u1_struct_0(B_390)) | ~v1_funct_1(F_388) | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_392), u1_struct_0(B_390)))) | ~v5_pre_topc(E_393, C_392, B_390) | ~v1_funct_2(E_393, u1_struct_0(C_392), u1_struct_0(B_390)) | ~v1_funct_1(E_393) | ~r1_tsep_1(C_392, D_389) | ~m1_pre_topc(D_389, A_391) | v2_struct_0(D_389) | ~m1_pre_topc(C_392, A_391) | v2_struct_0(C_392) | ~l1_pre_topc(B_390) | ~v2_pre_topc(B_390) | v2_struct_0(B_390) | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391) | v2_struct_0(A_391))), inference(cnfTransformation, [status(thm)], [f_234])).
% 5.16/1.84  tff(c_540, plain, (![A_391, C_392, E_393]: (v5_pre_topc(k10_tmap_1(A_391, '#skF_2', C_392, '#skF_4', E_393, '#skF_6'), k1_tsep_1(A_391, C_392, '#skF_4'), '#skF_2') | ~r4_tsep_1(A_391, C_392, '#skF_4') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_392), u1_struct_0('#skF_2')))) | ~v5_pre_topc(E_393, C_392, '#skF_2') | ~v1_funct_2(E_393, u1_struct_0(C_392), u1_struct_0('#skF_2')) | ~v1_funct_1(E_393) | ~r1_tsep_1(C_392, '#skF_4') | ~m1_pre_topc('#skF_4', A_391) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_392, A_391) | v2_struct_0(C_392) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391) | v2_struct_0(A_391))), inference(resolution, [status(thm)], [c_38, c_530])).
% 5.16/1.84  tff(c_555, plain, (![A_391, C_392, E_393]: (v5_pre_topc(k10_tmap_1(A_391, '#skF_2', C_392, '#skF_4', E_393, '#skF_6'), k1_tsep_1(A_391, C_392, '#skF_4'), '#skF_2') | ~r4_tsep_1(A_391, C_392, '#skF_4') | ~m1_subset_1(E_393, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_392), u1_struct_0('#skF_2')))) | ~v5_pre_topc(E_393, C_392, '#skF_2') | ~v1_funct_2(E_393, u1_struct_0(C_392), u1_struct_0('#skF_2')) | ~v1_funct_1(E_393) | ~r1_tsep_1(C_392, '#skF_4') | ~m1_pre_topc('#skF_4', A_391) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_392, A_391) | v2_struct_0(C_392) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391) | v2_struct_0(A_391))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_44, c_42, c_40, c_540])).
% 5.16/1.84  tff(c_593, plain, (![A_403, C_404, E_405]: (v5_pre_topc(k10_tmap_1(A_403, '#skF_2', C_404, '#skF_4', E_405, '#skF_6'), k1_tsep_1(A_403, C_404, '#skF_4'), '#skF_2') | ~r4_tsep_1(A_403, C_404, '#skF_4') | ~m1_subset_1(E_405, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_404), u1_struct_0('#skF_2')))) | ~v5_pre_topc(E_405, C_404, '#skF_2') | ~v1_funct_2(E_405, u1_struct_0(C_404), u1_struct_0('#skF_2')) | ~v1_funct_1(E_405) | ~r1_tsep_1(C_404, '#skF_4') | ~m1_pre_topc('#skF_4', A_403) | ~m1_pre_topc(C_404, A_403) | v2_struct_0(C_404) | ~l1_pre_topc(A_403) | ~v2_pre_topc(A_403) | v2_struct_0(A_403))), inference(negUnitSimplification, [status(thm)], [c_68, c_58, c_555])).
% 5.16/1.84  tff(c_603, plain, (![A_403]: (v5_pre_topc(k10_tmap_1(A_403, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_403, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_403, '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_403) | ~m1_pre_topc('#skF_3', A_403) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_403) | ~v2_pre_topc(A_403) | v2_struct_0(A_403))), inference(resolution, [status(thm)], [c_46, c_593])).
% 5.16/1.84  tff(c_620, plain, (![A_403]: (v5_pre_topc(k10_tmap_1(A_403, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_403, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_403, '#skF_3', '#skF_4') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_403) | ~m1_pre_topc('#skF_3', A_403) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_403) | ~v2_pre_topc(A_403) | v2_struct_0(A_403))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_603])).
% 5.16/1.84  tff(c_621, plain, (![A_403]: (v5_pre_topc(k10_tmap_1(A_403, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_403, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_403, '#skF_3', '#skF_4') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_403) | ~m1_pre_topc('#skF_3', A_403) | ~l1_pre_topc(A_403) | ~v2_pre_topc(A_403) | v2_struct_0(A_403))), inference(negUnitSimplification, [status(thm)], [c_62, c_620])).
% 5.16/1.84  tff(c_627, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_621])).
% 5.16/1.84  tff(c_36, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_75, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_36])).
% 5.16/1.84  tff(c_34, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_296])).
% 5.16/1.84  tff(c_76, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_34])).
% 5.16/1.84  tff(c_685, plain, (![B_438, F_441, E_436, C_437, D_440, A_439]: (r2_funct_2(u1_struct_0(k2_tsep_1(A_439, C_437, D_440)), u1_struct_0(B_438), k3_tmap_1(A_439, B_438, C_437, k2_tsep_1(A_439, C_437, D_440), E_436), k3_tmap_1(A_439, B_438, D_440, k2_tsep_1(A_439, C_437, D_440), F_441)) | ~r2_funct_2(u1_struct_0(D_440), u1_struct_0(B_438), k3_tmap_1(A_439, B_438, k1_tsep_1(A_439, C_437, D_440), D_440, k10_tmap_1(A_439, B_438, C_437, D_440, E_436, F_441)), F_441) | ~r2_funct_2(u1_struct_0(C_437), u1_struct_0(B_438), k3_tmap_1(A_439, B_438, k1_tsep_1(A_439, C_437, D_440), C_437, k10_tmap_1(A_439, B_438, C_437, D_440, E_436, F_441)), E_436) | ~m1_subset_1(F_441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_440), u1_struct_0(B_438)))) | ~v1_funct_2(F_441, u1_struct_0(D_440), u1_struct_0(B_438)) | ~v1_funct_1(F_441) | ~m1_subset_1(E_436, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_437), u1_struct_0(B_438)))) | ~v1_funct_2(E_436, u1_struct_0(C_437), u1_struct_0(B_438)) | ~v1_funct_1(E_436) | r1_tsep_1(C_437, D_440) | ~m1_pre_topc(D_440, A_439) | v2_struct_0(D_440) | ~m1_pre_topc(C_437, A_439) | v2_struct_0(C_437) | ~l1_pre_topc(B_438) | ~v2_pre_topc(B_438) | v2_struct_0(B_438) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439) | v2_struct_0(A_439))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.16/1.84  tff(c_687, plain, (![B_438, E_436, F_441]: (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_438), k3_tmap_1('#skF_1', B_438, '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), E_436), k3_tmap_1('#skF_1', B_438, '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), F_441)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_438), k3_tmap_1('#skF_1', B_438, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_438, '#skF_3', '#skF_4', E_436, F_441)), F_441) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_438), k3_tmap_1('#skF_1', B_438, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_438, '#skF_3', '#skF_4', E_436, F_441)), E_436) | ~m1_subset_1(F_441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_438)))) | ~v1_funct_2(F_441, u1_struct_0('#skF_4'), u1_struct_0(B_438)) | ~v1_funct_1(F_441) | ~m1_subset_1(E_436, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_438)))) | ~v1_funct_2(E_436, u1_struct_0('#skF_3'), u1_struct_0(B_438)) | ~v1_funct_1(E_436) | r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_438) | ~v2_pre_topc(B_438) | v2_struct_0(B_438) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_685])).
% 5.16/1.84  tff(c_689, plain, (![B_438, E_436, F_441]: (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_438), k3_tmap_1('#skF_1', B_438, '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), E_436), k3_tmap_1('#skF_1', B_438, '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), F_441)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_438), k3_tmap_1('#skF_1', B_438, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_438, '#skF_3', '#skF_4', E_436, F_441)), F_441) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_438), k3_tmap_1('#skF_1', B_438, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_438, '#skF_3', '#skF_4', E_436, F_441)), E_436) | ~m1_subset_1(F_441, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_438)))) | ~v1_funct_2(F_441, u1_struct_0('#skF_4'), u1_struct_0(B_438)) | ~v1_funct_1(F_441) | ~m1_subset_1(E_436, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_438)))) | ~v1_funct_2(E_436, u1_struct_0('#skF_3'), u1_struct_0(B_438)) | ~v1_funct_1(E_436) | r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_438) | ~v2_pre_topc(B_438) | v2_struct_0(B_438) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_54, c_687])).
% 5.16/1.84  tff(c_802, plain, (![B_466, E_467, F_468]: (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_466), k3_tmap_1('#skF_1', B_466, '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), E_467), k3_tmap_1('#skF_1', B_466, '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), F_468)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_466), k3_tmap_1('#skF_1', B_466, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_466, '#skF_3', '#skF_4', E_467, F_468)), F_468) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_466), k3_tmap_1('#skF_1', B_466, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_466, '#skF_3', '#skF_4', E_467, F_468)), E_467) | ~m1_subset_1(F_468, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_466)))) | ~v1_funct_2(F_468, u1_struct_0('#skF_4'), u1_struct_0(B_466)) | ~v1_funct_1(F_468) | ~m1_subset_1(E_467, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_466)))) | ~v1_funct_2(E_467, u1_struct_0('#skF_3'), u1_struct_0(B_466)) | ~v1_funct_1(E_467) | ~l1_pre_topc(B_466) | ~v2_pre_topc(B_466) | v2_struct_0(B_466))), inference(negUnitSimplification, [status(thm)], [c_74, c_62, c_58, c_627, c_689])).
% 5.16/1.84  tff(c_804, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6')) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_76, c_802])).
% 5.16/1.84  tff(c_807, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_52, c_50, c_46, c_44, c_42, c_38, c_75, c_804])).
% 5.16/1.84  tff(c_808, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_68, c_807])).
% 5.16/1.84  tff(c_16, plain, (![D_126, E_130, A_70, B_102, F_132, C_118]: (v5_pre_topc(k10_tmap_1(A_70, B_102, C_118, D_126, E_130, F_132), k1_tsep_1(A_70, C_118, D_126), B_102) | ~r4_tsep_1(A_70, C_118, D_126) | ~r2_funct_2(u1_struct_0(k2_tsep_1(A_70, C_118, D_126)), u1_struct_0(B_102), k3_tmap_1(A_70, B_102, C_118, k2_tsep_1(A_70, C_118, D_126), E_130), k3_tmap_1(A_70, B_102, D_126, k2_tsep_1(A_70, C_118, D_126), F_132)) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_126), u1_struct_0(B_102)))) | ~v5_pre_topc(F_132, D_126, B_102) | ~v1_funct_2(F_132, u1_struct_0(D_126), u1_struct_0(B_102)) | ~v1_funct_1(F_132) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_118), u1_struct_0(B_102)))) | ~v5_pre_topc(E_130, C_118, B_102) | ~v1_funct_2(E_130, u1_struct_0(C_118), u1_struct_0(B_102)) | ~v1_funct_1(E_130) | r1_tsep_1(C_118, D_126) | ~m1_pre_topc(D_126, A_70) | v2_struct_0(D_126) | ~m1_pre_topc(C_118, A_70) | v2_struct_0(C_118) | ~l1_pre_topc(B_102) | ~v2_pre_topc(B_102) | v2_struct_0(B_102) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.16/1.84  tff(c_811, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_808, c_16])).
% 5.16/1.84  tff(c_818, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_52, c_50, c_48, c_46, c_44, c_42, c_40, c_38, c_32, c_54, c_811])).
% 5.16/1.84  tff(c_820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_627, c_346, c_818])).
% 5.16/1.84  tff(c_823, plain, (![A_469]: (v5_pre_topc(k10_tmap_1(A_469, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_469, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_469, '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_469) | ~m1_pre_topc('#skF_3', A_469) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(splitRight, [status(thm)], [c_621])).
% 5.16/1.84  tff(c_826, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_54, c_823])).
% 5.16/1.84  tff(c_828, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_60, c_56, c_32, c_826])).
% 5.16/1.84  tff(c_830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_346, c_828])).
% 5.16/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/1.84  
% 5.16/1.84  Inference rules
% 5.16/1.84  ----------------------
% 5.16/1.84  #Ref     : 0
% 5.16/1.84  #Sup     : 111
% 5.16/1.84  #Fact    : 0
% 5.16/1.84  #Define  : 0
% 5.16/1.84  #Split   : 9
% 5.16/1.84  #Chain   : 0
% 5.16/1.84  #Close   : 0
% 5.16/1.84  
% 5.16/1.84  Ordering : KBO
% 5.16/1.84  
% 5.16/1.84  Simplification rules
% 5.16/1.84  ----------------------
% 5.16/1.84  #Subsume      : 19
% 5.16/1.84  #Demod        : 319
% 5.16/1.84  #Tautology    : 3
% 5.16/1.84  #SimpNegUnit  : 99
% 5.16/1.84  #BackRed      : 0
% 5.16/1.84  
% 5.16/1.84  #Partial instantiations: 0
% 5.16/1.84  #Strategies tried      : 1
% 5.16/1.84  
% 5.16/1.84  Timing (in seconds)
% 5.16/1.84  ----------------------
% 5.16/1.84  Preprocessing        : 0.43
% 5.16/1.84  Parsing              : 0.22
% 5.16/1.84  CNF conversion       : 0.07
% 5.16/1.84  Main loop            : 0.61
% 5.16/1.84  Inferencing          : 0.19
% 5.16/1.84  Reduction            : 0.18
% 5.16/1.84  Demodulation         : 0.13
% 5.16/1.84  BG Simplification    : 0.03
% 5.16/1.84  Subsumption          : 0.19
% 5.16/1.84  Abstraction          : 0.02
% 5.16/1.84  MUC search           : 0.00
% 5.16/1.84  Cooper               : 0.00
% 5.16/1.84  Total                : 1.10
% 5.16/1.84  Index Insertion      : 0.00
% 5.16/1.84  Index Deletion       : 0.00
% 5.16/1.84  Index Matching       : 0.00
% 5.16/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
