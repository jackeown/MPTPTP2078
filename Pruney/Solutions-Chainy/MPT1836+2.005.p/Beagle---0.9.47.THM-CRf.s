%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:13 EST 2020

% Result     : Theorem 5.10s
% Output     : CNFRefutation 5.10s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 435 expanded)
%              Number of leaves         :   34 ( 193 expanded)
%              Depth                    :   18
%              Number of atoms          :  669 (5283 expanded)
%              Number of equality atoms :    2 ( 163 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_borsuk_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_317,negated_conjecture,(
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
                           => ( ( A = k1_tsep_1(A,C,D)
                                & r2_funct_2(u1_struct_0(C),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),C,k10_tmap_1(A,B,C,D,E,F)),E)
                                & r2_funct_2(u1_struct_0(D),u1_struct_0(B),k3_tmap_1(A,B,k1_tsep_1(A,C,D),D,k10_tmap_1(A,B,C,D,E,F)),F) )
                             => ( v1_funct_1(k10_tmap_1(A,B,C,D,E,F))
                                & v1_funct_2(k10_tmap_1(A,B,C,D,E,F),u1_struct_0(A),u1_struct_0(B))
                                & v5_pre_topc(k10_tmap_1(A,B,C,D,E,F),A,B)
                                & m1_subset_1(k10_tmap_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_tmap_1)).

tff(f_253,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_borsuk_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_borsuk_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tsep_1)).

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

tff(c_78,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_76,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_74,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_64,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_58,plain,(
    v1_borsuk_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_30,plain,(
    ! [A_196,B_200,C_202] :
      ( r4_tsep_1(A_196,B_200,C_202)
      | ~ m1_pre_topc(C_202,A_196)
      | ~ v1_borsuk_1(C_202,A_196)
      | ~ m1_pre_topc(B_200,A_196)
      | ~ v1_borsuk_1(B_200,A_196)
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_46,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_44,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_38,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_198,plain,(
    ! [E_305,B_307,F_304,C_308,D_306,A_309] :
      ( m1_subset_1(k10_tmap_1(A_309,B_307,C_308,D_306,E_305,F_304),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_309,C_308,D_306)),u1_struct_0(B_307))))
      | ~ m1_subset_1(F_304,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_306),u1_struct_0(B_307))))
      | ~ v1_funct_2(F_304,u1_struct_0(D_306),u1_struct_0(B_307))
      | ~ v1_funct_1(F_304)
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_308),u1_struct_0(B_307))))
      | ~ v1_funct_2(E_305,u1_struct_0(C_308),u1_struct_0(B_307))
      | ~ v1_funct_1(E_305)
      | ~ m1_pre_topc(D_306,A_309)
      | v2_struct_0(D_306)
      | ~ m1_pre_topc(C_308,A_309)
      | v2_struct_0(C_308)
      | ~ l1_pre_topc(B_307)
      | ~ v2_pre_topc(B_307)
      | v2_struct_0(B_307)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_209,plain,(
    ! [B_307,E_305,F_304] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_307,'#skF_3','#skF_4',E_305,F_304),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_307))))
      | ~ m1_subset_1(F_304,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_307))))
      | ~ v1_funct_2(F_304,u1_struct_0('#skF_4'),u1_struct_0(B_307))
      | ~ v1_funct_1(F_304)
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_307))))
      | ~ v1_funct_2(E_305,u1_struct_0('#skF_3'),u1_struct_0(B_307))
      | ~ v1_funct_1(E_305)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_307)
      | ~ v2_pre_topc(B_307)
      | v2_struct_0(B_307)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_198])).

tff(c_220,plain,(
    ! [B_307,E_305,F_304] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_307,'#skF_3','#skF_4',E_305,F_304),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_307))))
      | ~ m1_subset_1(F_304,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_307))))
      | ~ v1_funct_2(F_304,u1_struct_0('#skF_4'),u1_struct_0(B_307))
      | ~ v1_funct_1(F_304)
      | ~ m1_subset_1(E_305,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_307))))
      | ~ v1_funct_2(E_305,u1_struct_0('#skF_3'),u1_struct_0(B_307))
      | ~ v1_funct_1(E_305)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_307)
      | ~ v2_pre_topc(B_307)
      | v2_struct_0(B_307)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_56,c_209])).

tff(c_229,plain,(
    ! [B_311,E_312,F_313] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_311,'#skF_3','#skF_4',E_312,F_313),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_311))))
      | ~ m1_subset_1(F_313,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_311))))
      | ~ v1_funct_2(F_313,u1_struct_0('#skF_4'),u1_struct_0(B_311))
      | ~ v1_funct_1(F_313)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_311))))
      | ~ v1_funct_2(E_312,u1_struct_0('#skF_3'),u1_struct_0(B_311))
      | ~ v1_funct_1(E_312)
      | ~ l1_pre_topc(B_311)
      | ~ v2_pre_topc(B_311)
      | v2_struct_0(B_311) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_60,c_220])).

tff(c_87,plain,(
    ! [A_268,D_265,B_266,C_267,E_264,F_263] :
      ( v1_funct_1(k10_tmap_1(A_268,B_266,C_267,D_265,E_264,F_263))
      | ~ m1_subset_1(F_263,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_265),u1_struct_0(B_266))))
      | ~ v1_funct_2(F_263,u1_struct_0(D_265),u1_struct_0(B_266))
      | ~ v1_funct_1(F_263)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_267),u1_struct_0(B_266))))
      | ~ v1_funct_2(E_264,u1_struct_0(C_267),u1_struct_0(B_266))
      | ~ v1_funct_1(E_264)
      | ~ m1_pre_topc(D_265,A_268)
      | v2_struct_0(D_265)
      | ~ m1_pre_topc(C_267,A_268)
      | v2_struct_0(C_267)
      | ~ l1_pre_topc(B_266)
      | ~ v2_pre_topc(B_266)
      | v2_struct_0(B_266)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_91,plain,(
    ! [A_268,C_267,E_264] :
      ( v1_funct_1(k10_tmap_1(A_268,'#skF_2',C_267,'#skF_4',E_264,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_267),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_264,u1_struct_0(C_267),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_264)
      | ~ m1_pre_topc('#skF_4',A_268)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_267,A_268)
      | v2_struct_0(C_267)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(resolution,[status(thm)],[c_40,c_87])).

tff(c_98,plain,(
    ! [A_268,C_267,E_264] :
      ( v1_funct_1(k10_tmap_1(A_268,'#skF_2',C_267,'#skF_4',E_264,'#skF_6'))
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_267),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_264,u1_struct_0(C_267),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_264)
      | ~ m1_pre_topc('#skF_4',A_268)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_267,A_268)
      | v2_struct_0(C_267)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_46,c_44,c_91])).

tff(c_115,plain,(
    ! [A_274,C_275,E_276] :
      ( v1_funct_1(k10_tmap_1(A_274,'#skF_2',C_275,'#skF_4',E_276,'#skF_6'))
      | ~ m1_subset_1(E_276,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_275),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_276,u1_struct_0(C_275),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_276)
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ m1_pre_topc(C_275,A_274)
      | v2_struct_0(C_275)
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60,c_98])).

tff(c_117,plain,(
    ! [A_274] :
      ( v1_funct_1(k10_tmap_1(A_274,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ m1_pre_topc('#skF_3',A_274)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(resolution,[status(thm)],[c_48,c_115])).

tff(c_122,plain,(
    ! [A_274] :
      ( v1_funct_1(k10_tmap_1(A_274,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_274)
      | ~ m1_pre_topc('#skF_3',A_274)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_274)
      | ~ v2_pre_topc(A_274)
      | v2_struct_0(A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_117])).

tff(c_129,plain,(
    ! [A_278] :
      ( v1_funct_1(k10_tmap_1(A_278,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_278)
      | ~ m1_pre_topc('#skF_3',A_278)
      | ~ l1_pre_topc(A_278)
      | ~ v2_pre_topc(A_278)
      | v2_struct_0(A_278) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_122])).

tff(c_32,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_86,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_132,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_129,c_86])).

tff(c_135,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_56,c_132])).

tff(c_137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_135])).

tff(c_138,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_140,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_240,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_229,c_140])).

tff(c_254,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_52,c_48,c_46,c_44,c_40,c_240])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_254])).

tff(c_257,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_259,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_299,plain,(
    ! [B_327,A_329,C_328,D_326,E_325,F_324] :
      ( v1_funct_2(k10_tmap_1(A_329,B_327,C_328,D_326,E_325,F_324),u1_struct_0(k1_tsep_1(A_329,C_328,D_326)),u1_struct_0(B_327))
      | ~ m1_subset_1(F_324,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_326),u1_struct_0(B_327))))
      | ~ v1_funct_2(F_324,u1_struct_0(D_326),u1_struct_0(B_327))
      | ~ v1_funct_1(F_324)
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_328),u1_struct_0(B_327))))
      | ~ v1_funct_2(E_325,u1_struct_0(C_328),u1_struct_0(B_327))
      | ~ v1_funct_1(E_325)
      | ~ m1_pre_topc(D_326,A_329)
      | v2_struct_0(D_326)
      | ~ m1_pre_topc(C_328,A_329)
      | v2_struct_0(C_328)
      | ~ l1_pre_topc(B_327)
      | ~ v2_pre_topc(B_327)
      | v2_struct_0(B_327)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_302,plain,(
    ! [B_327,E_325,F_324] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_327,'#skF_3','#skF_4',E_325,F_324),u1_struct_0('#skF_1'),u1_struct_0(B_327))
      | ~ m1_subset_1(F_324,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_327))))
      | ~ v1_funct_2(F_324,u1_struct_0('#skF_4'),u1_struct_0(B_327))
      | ~ v1_funct_1(F_324)
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_327))))
      | ~ v1_funct_2(E_325,u1_struct_0('#skF_3'),u1_struct_0(B_327))
      | ~ v1_funct_1(E_325)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_327)
      | ~ v2_pre_topc(B_327)
      | v2_struct_0(B_327)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_299])).

tff(c_304,plain,(
    ! [B_327,E_325,F_324] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_327,'#skF_3','#skF_4',E_325,F_324),u1_struct_0('#skF_1'),u1_struct_0(B_327))
      | ~ m1_subset_1(F_324,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_327))))
      | ~ v1_funct_2(F_324,u1_struct_0('#skF_4'),u1_struct_0(B_327))
      | ~ v1_funct_1(F_324)
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_327))))
      | ~ v1_funct_2(E_325,u1_struct_0('#skF_3'),u1_struct_0(B_327))
      | ~ v1_funct_1(E_325)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_327)
      | ~ v2_pre_topc(B_327)
      | v2_struct_0(B_327)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_56,c_302])).

tff(c_328,plain,(
    ! [B_336,E_337,F_338] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_336,'#skF_3','#skF_4',E_337,F_338),u1_struct_0('#skF_1'),u1_struct_0(B_336))
      | ~ m1_subset_1(F_338,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_336))))
      | ~ v1_funct_2(F_338,u1_struct_0('#skF_4'),u1_struct_0(B_336))
      | ~ v1_funct_1(F_338)
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_336))))
      | ~ v1_funct_2(E_337,u1_struct_0('#skF_3'),u1_struct_0(B_336))
      | ~ v1_funct_1(E_337)
      | ~ l1_pre_topc(B_336)
      | ~ v2_pre_topc(B_336)
      | v2_struct_0(B_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_60,c_304])).

tff(c_330,plain,(
    ! [E_337] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_337,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_337,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_337)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_328])).

tff(c_333,plain,(
    ! [E_337] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_337,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_337,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_337,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_337)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_46,c_44,c_330])).

tff(c_335,plain,(
    ! [E_339] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_339,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_339,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_339) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_333])).

tff(c_338,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_335])).

tff(c_341,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_338])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_259,c_341])).

tff(c_344,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_50,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_42,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_528,plain,(
    ! [B_394,E_397,C_396,D_393,F_392,A_395] :
      ( v5_pre_topc(k10_tmap_1(A_395,B_394,C_396,D_393,E_397,F_392),k1_tsep_1(A_395,C_396,D_393),B_394)
      | ~ r4_tsep_1(A_395,C_396,D_393)
      | ~ m1_subset_1(F_392,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_393),u1_struct_0(B_394))))
      | ~ v5_pre_topc(F_392,D_393,B_394)
      | ~ v1_funct_2(F_392,u1_struct_0(D_393),u1_struct_0(B_394))
      | ~ v1_funct_1(F_392)
      | ~ m1_subset_1(E_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396),u1_struct_0(B_394))))
      | ~ v5_pre_topc(E_397,C_396,B_394)
      | ~ v1_funct_2(E_397,u1_struct_0(C_396),u1_struct_0(B_394))
      | ~ v1_funct_1(E_397)
      | ~ r1_tsep_1(C_396,D_393)
      | ~ m1_pre_topc(D_393,A_395)
      | v2_struct_0(D_393)
      | ~ m1_pre_topc(C_396,A_395)
      | v2_struct_0(C_396)
      | ~ l1_pre_topc(B_394)
      | ~ v2_pre_topc(B_394)
      | v2_struct_0(B_394)
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_538,plain,(
    ! [A_395,C_396,E_397] :
      ( v5_pre_topc(k10_tmap_1(A_395,'#skF_2',C_396,'#skF_4',E_397,'#skF_6'),k1_tsep_1(A_395,C_396,'#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_395,C_396,'#skF_4')
      | ~ v5_pre_topc('#skF_6','#skF_4','#skF_2')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(E_397,C_396,'#skF_2')
      | ~ v1_funct_2(E_397,u1_struct_0(C_396),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_397)
      | ~ r1_tsep_1(C_396,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_395)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_396,A_395)
      | v2_struct_0(C_396)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(resolution,[status(thm)],[c_40,c_528])).

tff(c_553,plain,(
    ! [A_395,C_396,E_397] :
      ( v5_pre_topc(k10_tmap_1(A_395,'#skF_2',C_396,'#skF_4',E_397,'#skF_6'),k1_tsep_1(A_395,C_396,'#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_395,C_396,'#skF_4')
      | ~ m1_subset_1(E_397,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(E_397,C_396,'#skF_2')
      | ~ v1_funct_2(E_397,u1_struct_0(C_396),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_397)
      | ~ r1_tsep_1(C_396,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_395)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_396,A_395)
      | v2_struct_0(C_396)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_395)
      | ~ v2_pre_topc(A_395)
      | v2_struct_0(A_395) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_46,c_44,c_42,c_538])).

tff(c_590,plain,(
    ! [A_401,C_402,E_403] :
      ( v5_pre_topc(k10_tmap_1(A_401,'#skF_2',C_402,'#skF_4',E_403,'#skF_6'),k1_tsep_1(A_401,C_402,'#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_401,C_402,'#skF_4')
      | ~ m1_subset_1(E_403,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_402),u1_struct_0('#skF_2'))))
      | ~ v5_pre_topc(E_403,C_402,'#skF_2')
      | ~ v1_funct_2(E_403,u1_struct_0(C_402),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_403)
      | ~ r1_tsep_1(C_402,'#skF_4')
      | ~ m1_pre_topc('#skF_4',A_401)
      | ~ m1_pre_topc(C_402,A_401)
      | v2_struct_0(C_402)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_60,c_553])).

tff(c_600,plain,(
    ! [A_401] :
      ( v5_pre_topc(k10_tmap_1(A_401,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_401,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_401,'#skF_3','#skF_4')
      | ~ v5_pre_topc('#skF_5','#skF_3','#skF_2')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ r1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_401)
      | ~ m1_pre_topc('#skF_3',A_401)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(resolution,[status(thm)],[c_48,c_590])).

tff(c_617,plain,(
    ! [A_401] :
      ( v5_pre_topc(k10_tmap_1(A_401,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_401,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_401,'#skF_3','#skF_4')
      | ~ r1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_401)
      | ~ m1_pre_topc('#skF_3',A_401)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_600])).

tff(c_618,plain,(
    ! [A_401] :
      ( v5_pre_topc(k10_tmap_1(A_401,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_401,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_401,'#skF_3','#skF_4')
      | ~ r1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_401)
      | ~ m1_pre_topc('#skF_3',A_401)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_617])).

tff(c_624,plain,(
    ~ r1_tsep_1('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_36,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_79,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36])).

tff(c_34,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_317])).

tff(c_80,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34])).

tff(c_650,plain,(
    ! [C_435,F_439,A_437,B_436,E_434,D_438] :
      ( r2_funct_2(u1_struct_0(k2_tsep_1(A_437,C_435,D_438)),u1_struct_0(B_436),k3_tmap_1(A_437,B_436,C_435,k2_tsep_1(A_437,C_435,D_438),E_434),k3_tmap_1(A_437,B_436,D_438,k2_tsep_1(A_437,C_435,D_438),F_439))
      | ~ r2_funct_2(u1_struct_0(D_438),u1_struct_0(B_436),k3_tmap_1(A_437,B_436,k1_tsep_1(A_437,C_435,D_438),D_438,k10_tmap_1(A_437,B_436,C_435,D_438,E_434,F_439)),F_439)
      | ~ r2_funct_2(u1_struct_0(C_435),u1_struct_0(B_436),k3_tmap_1(A_437,B_436,k1_tsep_1(A_437,C_435,D_438),C_435,k10_tmap_1(A_437,B_436,C_435,D_438,E_434,F_439)),E_434)
      | ~ m1_subset_1(F_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_438),u1_struct_0(B_436))))
      | ~ v1_funct_2(F_439,u1_struct_0(D_438),u1_struct_0(B_436))
      | ~ v1_funct_1(F_439)
      | ~ m1_subset_1(E_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_435),u1_struct_0(B_436))))
      | ~ v1_funct_2(E_434,u1_struct_0(C_435),u1_struct_0(B_436))
      | ~ v1_funct_1(E_434)
      | r1_tsep_1(C_435,D_438)
      | ~ m1_pre_topc(D_438,A_437)
      | v2_struct_0(D_438)
      | ~ m1_pre_topc(C_435,A_437)
      | v2_struct_0(C_435)
      | ~ l1_pre_topc(B_436)
      | ~ v2_pre_topc(B_436)
      | v2_struct_0(B_436)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437)
      | v2_struct_0(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_652,plain,(
    ! [B_436,E_434,F_439] :
      ( r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_436),k3_tmap_1('#skF_1',B_436,'#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),E_434),k3_tmap_1('#skF_1',B_436,'#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),F_439))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_436),k3_tmap_1('#skF_1',B_436,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_436,'#skF_3','#skF_4',E_434,F_439)),F_439)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_436),k3_tmap_1('#skF_1',B_436,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1',B_436,'#skF_3','#skF_4',E_434,F_439)),E_434)
      | ~ m1_subset_1(F_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_436))))
      | ~ v1_funct_2(F_439,u1_struct_0('#skF_4'),u1_struct_0(B_436))
      | ~ v1_funct_1(F_439)
      | ~ m1_subset_1(E_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_436))))
      | ~ v1_funct_2(E_434,u1_struct_0('#skF_3'),u1_struct_0(B_436))
      | ~ v1_funct_1(E_434)
      | r1_tsep_1('#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_436)
      | ~ v2_pre_topc(B_436)
      | v2_struct_0(B_436)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_650])).

tff(c_654,plain,(
    ! [B_436,E_434,F_439] :
      ( r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_436),k3_tmap_1('#skF_1',B_436,'#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),E_434),k3_tmap_1('#skF_1',B_436,'#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),F_439))
      | ~ r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0(B_436),k3_tmap_1('#skF_1',B_436,'#skF_1','#skF_4',k10_tmap_1('#skF_1',B_436,'#skF_3','#skF_4',E_434,F_439)),F_439)
      | ~ r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0(B_436),k3_tmap_1('#skF_1',B_436,'#skF_1','#skF_3',k10_tmap_1('#skF_1',B_436,'#skF_3','#skF_4',E_434,F_439)),E_434)
      | ~ m1_subset_1(F_439,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_436))))
      | ~ v1_funct_2(F_439,u1_struct_0('#skF_4'),u1_struct_0(B_436))
      | ~ v1_funct_1(F_439)
      | ~ m1_subset_1(E_434,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_436))))
      | ~ v1_funct_2(E_434,u1_struct_0('#skF_3'),u1_struct_0(B_436))
      | ~ v1_funct_1(E_434)
      | r1_tsep_1('#skF_3','#skF_4')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_436)
      | ~ v2_pre_topc(B_436)
      | v2_struct_0(B_436)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_56,c_38,c_652])).

tff(c_767,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_78,c_66,c_60,c_624,c_654])).

tff(c_769,plain,
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
    inference(resolution,[status(thm)],[c_80,c_767])).

tff(c_772,plain,
    ( r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_54,c_52,c_48,c_46,c_44,c_40,c_79,c_769])).

tff(c_773,plain,(
    r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_3',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_5'),k3_tmap_1('#skF_1','#skF_2','#skF_4',k2_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_772])).

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

tff(c_776,plain,
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
    inference(resolution,[status(thm)],[c_773,c_16])).

tff(c_783,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | r1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_62,c_56,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_776])).

tff(c_784,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_60,c_624,c_344,c_783])).

tff(c_795,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_784])).

tff(c_798,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_62,c_58,c_56,c_795])).

tff(c_800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_798])).

tff(c_804,plain,(
    ! [A_469] :
      ( v5_pre_topc(k10_tmap_1(A_469,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_tsep_1(A_469,'#skF_3','#skF_4'),'#skF_2')
      | ~ r4_tsep_1(A_469,'#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4',A_469)
      | ~ m1_pre_topc('#skF_3',A_469)
      | ~ l1_pre_topc(A_469)
      | ~ v2_pre_topc(A_469)
      | v2_struct_0(A_469) ) ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_807,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_804])).

tff(c_809,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_62,c_56,c_807])).

tff(c_810,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_344,c_809])).

tff(c_813,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_borsuk_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_borsuk_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_810])).

tff(c_816,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_64,c_62,c_58,c_56,c_813])).

tff(c_818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_816])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:22:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.10/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.87  
% 5.10/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.88  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_borsuk_1 > r1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k2_tsep_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.10/1.88  
% 5.10/1.88  %Foreground sorts:
% 5.10/1.88  
% 5.10/1.88  
% 5.10/1.88  %Background operators:
% 5.10/1.88  
% 5.10/1.88  
% 5.10/1.88  %Foreground operators:
% 5.10/1.88  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.10/1.88  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.10/1.88  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 5.10/1.88  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.10/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.10/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.10/1.88  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.10/1.88  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 5.10/1.88  tff('#skF_5', type, '#skF_5': $i).
% 5.10/1.88  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.10/1.88  tff('#skF_6', type, '#skF_6': $i).
% 5.10/1.88  tff('#skF_2', type, '#skF_2': $i).
% 5.10/1.88  tff('#skF_3', type, '#skF_3': $i).
% 5.10/1.88  tff('#skF_1', type, '#skF_1': $i).
% 5.10/1.88  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.10/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.10/1.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.10/1.88  tff('#skF_4', type, '#skF_4': $i).
% 5.10/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.10/1.88  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.10/1.88  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.10/1.88  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 5.10/1.88  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.10/1.88  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 5.10/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.10/1.88  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 5.10/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.10/1.88  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 5.10/1.88  
% 5.10/1.91  tff(f_317, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_borsuk_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_borsuk_1(D, A)) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((A = k1_tsep_1(A, C, D)) & r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E)) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_tmap_1)).
% 5.10/1.91  tff(f_253, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_borsuk_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((v1_borsuk_1(C, A) & m1_pre_topc(C, A)) => r4_tsep_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tsep_1)).
% 5.10/1.91  tff(f_67, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 5.10/1.91  tff(f_234, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (r4_tsep_1(A, C, D) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_tmap_1)).
% 5.10/1.91  tff(f_117, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) <=> r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_tmap_1)).
% 5.10/1.91  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (~r1_tsep_1(C, D) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((r2_funct_2(u1_struct_0(k2_tsep_1(A, C, D)), u1_struct_0(B), k3_tmap_1(A, B, C, k2_tsep_1(A, C, D), E), k3_tmap_1(A, B, D, k2_tsep_1(A, C, D), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), k1_tsep_1(A, C, D), B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_tmap_1)).
% 5.10/1.91  tff(c_78, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_76, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_74, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_64, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_58, plain, (v1_borsuk_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_30, plain, (![A_196, B_200, C_202]: (r4_tsep_1(A_196, B_200, C_202) | ~m1_pre_topc(C_202, A_196) | ~v1_borsuk_1(C_202, A_196) | ~m1_pre_topc(B_200, A_196) | ~v1_borsuk_1(B_200, A_196) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(cnfTransformation, [status(thm)], [f_253])).
% 5.10/1.91  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_46, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_44, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_38, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_198, plain, (![E_305, B_307, F_304, C_308, D_306, A_309]: (m1_subset_1(k10_tmap_1(A_309, B_307, C_308, D_306, E_305, F_304), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_309, C_308, D_306)), u1_struct_0(B_307)))) | ~m1_subset_1(F_304, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_306), u1_struct_0(B_307)))) | ~v1_funct_2(F_304, u1_struct_0(D_306), u1_struct_0(B_307)) | ~v1_funct_1(F_304) | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_308), u1_struct_0(B_307)))) | ~v1_funct_2(E_305, u1_struct_0(C_308), u1_struct_0(B_307)) | ~v1_funct_1(E_305) | ~m1_pre_topc(D_306, A_309) | v2_struct_0(D_306) | ~m1_pre_topc(C_308, A_309) | v2_struct_0(C_308) | ~l1_pre_topc(B_307) | ~v2_pre_topc(B_307) | v2_struct_0(B_307) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.10/1.91  tff(c_209, plain, (![B_307, E_305, F_304]: (m1_subset_1(k10_tmap_1('#skF_1', B_307, '#skF_3', '#skF_4', E_305, F_304), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_307)))) | ~m1_subset_1(F_304, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_307)))) | ~v1_funct_2(F_304, u1_struct_0('#skF_4'), u1_struct_0(B_307)) | ~v1_funct_1(F_304) | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_307)))) | ~v1_funct_2(E_305, u1_struct_0('#skF_3'), u1_struct_0(B_307)) | ~v1_funct_1(E_305) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_307) | ~v2_pre_topc(B_307) | v2_struct_0(B_307) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_198])).
% 5.10/1.91  tff(c_220, plain, (![B_307, E_305, F_304]: (m1_subset_1(k10_tmap_1('#skF_1', B_307, '#skF_3', '#skF_4', E_305, F_304), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_307)))) | ~m1_subset_1(F_304, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_307)))) | ~v1_funct_2(F_304, u1_struct_0('#skF_4'), u1_struct_0(B_307)) | ~v1_funct_1(F_304) | ~m1_subset_1(E_305, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_307)))) | ~v1_funct_2(E_305, u1_struct_0('#skF_3'), u1_struct_0(B_307)) | ~v1_funct_1(E_305) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_307) | ~v2_pre_topc(B_307) | v2_struct_0(B_307) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_56, c_209])).
% 5.10/1.91  tff(c_229, plain, (![B_311, E_312, F_313]: (m1_subset_1(k10_tmap_1('#skF_1', B_311, '#skF_3', '#skF_4', E_312, F_313), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_311)))) | ~m1_subset_1(F_313, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_311)))) | ~v1_funct_2(F_313, u1_struct_0('#skF_4'), u1_struct_0(B_311)) | ~v1_funct_1(F_313) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_311)))) | ~v1_funct_2(E_312, u1_struct_0('#skF_3'), u1_struct_0(B_311)) | ~v1_funct_1(E_312) | ~l1_pre_topc(B_311) | ~v2_pre_topc(B_311) | v2_struct_0(B_311))), inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_60, c_220])).
% 5.10/1.91  tff(c_87, plain, (![A_268, D_265, B_266, C_267, E_264, F_263]: (v1_funct_1(k10_tmap_1(A_268, B_266, C_267, D_265, E_264, F_263)) | ~m1_subset_1(F_263, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_265), u1_struct_0(B_266)))) | ~v1_funct_2(F_263, u1_struct_0(D_265), u1_struct_0(B_266)) | ~v1_funct_1(F_263) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_267), u1_struct_0(B_266)))) | ~v1_funct_2(E_264, u1_struct_0(C_267), u1_struct_0(B_266)) | ~v1_funct_1(E_264) | ~m1_pre_topc(D_265, A_268) | v2_struct_0(D_265) | ~m1_pre_topc(C_267, A_268) | v2_struct_0(C_267) | ~l1_pre_topc(B_266) | ~v2_pre_topc(B_266) | v2_struct_0(B_266) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.10/1.91  tff(c_91, plain, (![A_268, C_267, E_264]: (v1_funct_1(k10_tmap_1(A_268, '#skF_2', C_267, '#skF_4', E_264, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_267), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_264, u1_struct_0(C_267), u1_struct_0('#skF_2')) | ~v1_funct_1(E_264) | ~m1_pre_topc('#skF_4', A_268) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_267, A_268) | v2_struct_0(C_267) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(resolution, [status(thm)], [c_40, c_87])).
% 5.10/1.91  tff(c_98, plain, (![A_268, C_267, E_264]: (v1_funct_1(k10_tmap_1(A_268, '#skF_2', C_267, '#skF_4', E_264, '#skF_6')) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_267), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_264, u1_struct_0(C_267), u1_struct_0('#skF_2')) | ~v1_funct_1(E_264) | ~m1_pre_topc('#skF_4', A_268) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_267, A_268) | v2_struct_0(C_267) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_46, c_44, c_91])).
% 5.10/1.91  tff(c_115, plain, (![A_274, C_275, E_276]: (v1_funct_1(k10_tmap_1(A_274, '#skF_2', C_275, '#skF_4', E_276, '#skF_6')) | ~m1_subset_1(E_276, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_275), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_276, u1_struct_0(C_275), u1_struct_0('#skF_2')) | ~v1_funct_1(E_276) | ~m1_pre_topc('#skF_4', A_274) | ~m1_pre_topc(C_275, A_274) | v2_struct_0(C_275) | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(negUnitSimplification, [status(thm)], [c_72, c_60, c_98])).
% 5.10/1.91  tff(c_117, plain, (![A_274]: (v1_funct_1(k10_tmap_1(A_274, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_274) | ~m1_pre_topc('#skF_3', A_274) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(resolution, [status(thm)], [c_48, c_115])).
% 5.10/1.91  tff(c_122, plain, (![A_274]: (v1_funct_1(k10_tmap_1(A_274, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_274) | ~m1_pre_topc('#skF_3', A_274) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_274) | ~v2_pre_topc(A_274) | v2_struct_0(A_274))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_117])).
% 5.10/1.91  tff(c_129, plain, (![A_278]: (v1_funct_1(k10_tmap_1(A_278, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_278) | ~m1_pre_topc('#skF_3', A_278) | ~l1_pre_topc(A_278) | ~v2_pre_topc(A_278) | v2_struct_0(A_278))), inference(negUnitSimplification, [status(thm)], [c_66, c_122])).
% 5.10/1.91  tff(c_32, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_86, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_32])).
% 5.10/1.91  tff(c_132, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_129, c_86])).
% 5.10/1.91  tff(c_135, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_56, c_132])).
% 5.10/1.91  tff(c_137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_135])).
% 5.10/1.91  tff(c_138, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_32])).
% 5.10/1.91  tff(c_140, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_138])).
% 5.10/1.91  tff(c_240, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_229, c_140])).
% 5.10/1.91  tff(c_254, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_52, c_48, c_46, c_44, c_40, c_240])).
% 5.10/1.91  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_254])).
% 5.10/1.91  tff(c_257, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_138])).
% 5.10/1.91  tff(c_259, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_257])).
% 5.10/1.91  tff(c_299, plain, (![B_327, A_329, C_328, D_326, E_325, F_324]: (v1_funct_2(k10_tmap_1(A_329, B_327, C_328, D_326, E_325, F_324), u1_struct_0(k1_tsep_1(A_329, C_328, D_326)), u1_struct_0(B_327)) | ~m1_subset_1(F_324, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_326), u1_struct_0(B_327)))) | ~v1_funct_2(F_324, u1_struct_0(D_326), u1_struct_0(B_327)) | ~v1_funct_1(F_324) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_328), u1_struct_0(B_327)))) | ~v1_funct_2(E_325, u1_struct_0(C_328), u1_struct_0(B_327)) | ~v1_funct_1(E_325) | ~m1_pre_topc(D_326, A_329) | v2_struct_0(D_326) | ~m1_pre_topc(C_328, A_329) | v2_struct_0(C_328) | ~l1_pre_topc(B_327) | ~v2_pre_topc(B_327) | v2_struct_0(B_327) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329) | v2_struct_0(A_329))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.10/1.91  tff(c_302, plain, (![B_327, E_325, F_324]: (v1_funct_2(k10_tmap_1('#skF_1', B_327, '#skF_3', '#skF_4', E_325, F_324), u1_struct_0('#skF_1'), u1_struct_0(B_327)) | ~m1_subset_1(F_324, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_327)))) | ~v1_funct_2(F_324, u1_struct_0('#skF_4'), u1_struct_0(B_327)) | ~v1_funct_1(F_324) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_327)))) | ~v1_funct_2(E_325, u1_struct_0('#skF_3'), u1_struct_0(B_327)) | ~v1_funct_1(E_325) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_327) | ~v2_pre_topc(B_327) | v2_struct_0(B_327) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_299])).
% 5.10/1.91  tff(c_304, plain, (![B_327, E_325, F_324]: (v1_funct_2(k10_tmap_1('#skF_1', B_327, '#skF_3', '#skF_4', E_325, F_324), u1_struct_0('#skF_1'), u1_struct_0(B_327)) | ~m1_subset_1(F_324, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_327)))) | ~v1_funct_2(F_324, u1_struct_0('#skF_4'), u1_struct_0(B_327)) | ~v1_funct_1(F_324) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_327)))) | ~v1_funct_2(E_325, u1_struct_0('#skF_3'), u1_struct_0(B_327)) | ~v1_funct_1(E_325) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_327) | ~v2_pre_topc(B_327) | v2_struct_0(B_327) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_56, c_302])).
% 5.10/1.91  tff(c_328, plain, (![B_336, E_337, F_338]: (v1_funct_2(k10_tmap_1('#skF_1', B_336, '#skF_3', '#skF_4', E_337, F_338), u1_struct_0('#skF_1'), u1_struct_0(B_336)) | ~m1_subset_1(F_338, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_336)))) | ~v1_funct_2(F_338, u1_struct_0('#skF_4'), u1_struct_0(B_336)) | ~v1_funct_1(F_338) | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_336)))) | ~v1_funct_2(E_337, u1_struct_0('#skF_3'), u1_struct_0(B_336)) | ~v1_funct_1(E_337) | ~l1_pre_topc(B_336) | ~v2_pre_topc(B_336) | v2_struct_0(B_336))), inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_60, c_304])).
% 5.10/1.91  tff(c_330, plain, (![E_337]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_337, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_337, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_337) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_328])).
% 5.10/1.91  tff(c_333, plain, (![E_337]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_337, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_337, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_337, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_337) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_46, c_44, c_330])).
% 5.10/1.91  tff(c_335, plain, (![E_339]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_339, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_339, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_339))), inference(negUnitSimplification, [status(thm)], [c_72, c_333])).
% 5.10/1.91  tff(c_338, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_335])).
% 5.10/1.91  tff(c_341, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_338])).
% 5.10/1.91  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_259, c_341])).
% 5.10/1.91  tff(c_344, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_257])).
% 5.10/1.91  tff(c_50, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_42, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_528, plain, (![B_394, E_397, C_396, D_393, F_392, A_395]: (v5_pre_topc(k10_tmap_1(A_395, B_394, C_396, D_393, E_397, F_392), k1_tsep_1(A_395, C_396, D_393), B_394) | ~r4_tsep_1(A_395, C_396, D_393) | ~m1_subset_1(F_392, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_393), u1_struct_0(B_394)))) | ~v5_pre_topc(F_392, D_393, B_394) | ~v1_funct_2(F_392, u1_struct_0(D_393), u1_struct_0(B_394)) | ~v1_funct_1(F_392) | ~m1_subset_1(E_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396), u1_struct_0(B_394)))) | ~v5_pre_topc(E_397, C_396, B_394) | ~v1_funct_2(E_397, u1_struct_0(C_396), u1_struct_0(B_394)) | ~v1_funct_1(E_397) | ~r1_tsep_1(C_396, D_393) | ~m1_pre_topc(D_393, A_395) | v2_struct_0(D_393) | ~m1_pre_topc(C_396, A_395) | v2_struct_0(C_396) | ~l1_pre_topc(B_394) | ~v2_pre_topc(B_394) | v2_struct_0(B_394) | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(cnfTransformation, [status(thm)], [f_234])).
% 5.10/1.91  tff(c_538, plain, (![A_395, C_396, E_397]: (v5_pre_topc(k10_tmap_1(A_395, '#skF_2', C_396, '#skF_4', E_397, '#skF_6'), k1_tsep_1(A_395, C_396, '#skF_4'), '#skF_2') | ~r4_tsep_1(A_395, C_396, '#skF_4') | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396), u1_struct_0('#skF_2')))) | ~v5_pre_topc(E_397, C_396, '#skF_2') | ~v1_funct_2(E_397, u1_struct_0(C_396), u1_struct_0('#skF_2')) | ~v1_funct_1(E_397) | ~r1_tsep_1(C_396, '#skF_4') | ~m1_pre_topc('#skF_4', A_395) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_396, A_395) | v2_struct_0(C_396) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(resolution, [status(thm)], [c_40, c_528])).
% 5.10/1.91  tff(c_553, plain, (![A_395, C_396, E_397]: (v5_pre_topc(k10_tmap_1(A_395, '#skF_2', C_396, '#skF_4', E_397, '#skF_6'), k1_tsep_1(A_395, C_396, '#skF_4'), '#skF_2') | ~r4_tsep_1(A_395, C_396, '#skF_4') | ~m1_subset_1(E_397, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_396), u1_struct_0('#skF_2')))) | ~v5_pre_topc(E_397, C_396, '#skF_2') | ~v1_funct_2(E_397, u1_struct_0(C_396), u1_struct_0('#skF_2')) | ~v1_funct_1(E_397) | ~r1_tsep_1(C_396, '#skF_4') | ~m1_pre_topc('#skF_4', A_395) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_396, A_395) | v2_struct_0(C_396) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_395) | ~v2_pre_topc(A_395) | v2_struct_0(A_395))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_46, c_44, c_42, c_538])).
% 5.10/1.91  tff(c_590, plain, (![A_401, C_402, E_403]: (v5_pre_topc(k10_tmap_1(A_401, '#skF_2', C_402, '#skF_4', E_403, '#skF_6'), k1_tsep_1(A_401, C_402, '#skF_4'), '#skF_2') | ~r4_tsep_1(A_401, C_402, '#skF_4') | ~m1_subset_1(E_403, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_402), u1_struct_0('#skF_2')))) | ~v5_pre_topc(E_403, C_402, '#skF_2') | ~v1_funct_2(E_403, u1_struct_0(C_402), u1_struct_0('#skF_2')) | ~v1_funct_1(E_403) | ~r1_tsep_1(C_402, '#skF_4') | ~m1_pre_topc('#skF_4', A_401) | ~m1_pre_topc(C_402, A_401) | v2_struct_0(C_402) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(negUnitSimplification, [status(thm)], [c_72, c_60, c_553])).
% 5.10/1.91  tff(c_600, plain, (![A_401]: (v5_pre_topc(k10_tmap_1(A_401, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_401, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_401, '#skF_3', '#skF_4') | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_401) | ~m1_pre_topc('#skF_3', A_401) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(resolution, [status(thm)], [c_48, c_590])).
% 5.10/1.91  tff(c_617, plain, (![A_401]: (v5_pre_topc(k10_tmap_1(A_401, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_401, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_401, '#skF_3', '#skF_4') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_401) | ~m1_pre_topc('#skF_3', A_401) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_600])).
% 5.10/1.91  tff(c_618, plain, (![A_401]: (v5_pre_topc(k10_tmap_1(A_401, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_401, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_401, '#skF_3', '#skF_4') | ~r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_401) | ~m1_pre_topc('#skF_3', A_401) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(negUnitSimplification, [status(thm)], [c_66, c_617])).
% 5.10/1.91  tff(c_624, plain, (~r1_tsep_1('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_618])).
% 5.10/1.91  tff(c_36, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_79, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36])).
% 5.10/1.91  tff(c_34, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_317])).
% 5.10/1.91  tff(c_80, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34])).
% 5.10/1.91  tff(c_650, plain, (![C_435, F_439, A_437, B_436, E_434, D_438]: (r2_funct_2(u1_struct_0(k2_tsep_1(A_437, C_435, D_438)), u1_struct_0(B_436), k3_tmap_1(A_437, B_436, C_435, k2_tsep_1(A_437, C_435, D_438), E_434), k3_tmap_1(A_437, B_436, D_438, k2_tsep_1(A_437, C_435, D_438), F_439)) | ~r2_funct_2(u1_struct_0(D_438), u1_struct_0(B_436), k3_tmap_1(A_437, B_436, k1_tsep_1(A_437, C_435, D_438), D_438, k10_tmap_1(A_437, B_436, C_435, D_438, E_434, F_439)), F_439) | ~r2_funct_2(u1_struct_0(C_435), u1_struct_0(B_436), k3_tmap_1(A_437, B_436, k1_tsep_1(A_437, C_435, D_438), C_435, k10_tmap_1(A_437, B_436, C_435, D_438, E_434, F_439)), E_434) | ~m1_subset_1(F_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_438), u1_struct_0(B_436)))) | ~v1_funct_2(F_439, u1_struct_0(D_438), u1_struct_0(B_436)) | ~v1_funct_1(F_439) | ~m1_subset_1(E_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_435), u1_struct_0(B_436)))) | ~v1_funct_2(E_434, u1_struct_0(C_435), u1_struct_0(B_436)) | ~v1_funct_1(E_434) | r1_tsep_1(C_435, D_438) | ~m1_pre_topc(D_438, A_437) | v2_struct_0(D_438) | ~m1_pre_topc(C_435, A_437) | v2_struct_0(C_435) | ~l1_pre_topc(B_436) | ~v2_pre_topc(B_436) | v2_struct_0(B_436) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437) | v2_struct_0(A_437))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.10/1.91  tff(c_652, plain, (![B_436, E_434, F_439]: (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_436), k3_tmap_1('#skF_1', B_436, '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), E_434), k3_tmap_1('#skF_1', B_436, '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), F_439)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_436), k3_tmap_1('#skF_1', B_436, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_436, '#skF_3', '#skF_4', E_434, F_439)), F_439) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_436), k3_tmap_1('#skF_1', B_436, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', B_436, '#skF_3', '#skF_4', E_434, F_439)), E_434) | ~m1_subset_1(F_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_436)))) | ~v1_funct_2(F_439, u1_struct_0('#skF_4'), u1_struct_0(B_436)) | ~v1_funct_1(F_439) | ~m1_subset_1(E_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_436)))) | ~v1_funct_2(E_434, u1_struct_0('#skF_3'), u1_struct_0(B_436)) | ~v1_funct_1(E_434) | r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_436) | ~v2_pre_topc(B_436) | v2_struct_0(B_436) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_650])).
% 5.10/1.91  tff(c_654, plain, (![B_436, E_434, F_439]: (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_436), k3_tmap_1('#skF_1', B_436, '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), E_434), k3_tmap_1('#skF_1', B_436, '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), F_439)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_436), k3_tmap_1('#skF_1', B_436, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_436, '#skF_3', '#skF_4', E_434, F_439)), F_439) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_436), k3_tmap_1('#skF_1', B_436, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_436, '#skF_3', '#skF_4', E_434, F_439)), E_434) | ~m1_subset_1(F_439, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_436)))) | ~v1_funct_2(F_439, u1_struct_0('#skF_4'), u1_struct_0(B_436)) | ~v1_funct_1(F_439) | ~m1_subset_1(E_434, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_436)))) | ~v1_funct_2(E_434, u1_struct_0('#skF_3'), u1_struct_0(B_436)) | ~v1_funct_1(E_434) | r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_436) | ~v2_pre_topc(B_436) | v2_struct_0(B_436) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_56, c_38, c_652])).
% 5.10/1.91  tff(c_767, plain, (![B_466, E_467, F_468]: (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_466), k3_tmap_1('#skF_1', B_466, '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), E_467), k3_tmap_1('#skF_1', B_466, '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), F_468)) | ~r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0(B_466), k3_tmap_1('#skF_1', B_466, '#skF_1', '#skF_4', k10_tmap_1('#skF_1', B_466, '#skF_3', '#skF_4', E_467, F_468)), F_468) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0(B_466), k3_tmap_1('#skF_1', B_466, '#skF_1', '#skF_3', k10_tmap_1('#skF_1', B_466, '#skF_3', '#skF_4', E_467, F_468)), E_467) | ~m1_subset_1(F_468, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_466)))) | ~v1_funct_2(F_468, u1_struct_0('#skF_4'), u1_struct_0(B_466)) | ~v1_funct_1(F_468) | ~m1_subset_1(E_467, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_466)))) | ~v1_funct_2(E_467, u1_struct_0('#skF_3'), u1_struct_0(B_466)) | ~v1_funct_1(E_467) | ~l1_pre_topc(B_466) | ~v2_pre_topc(B_466) | v2_struct_0(B_466))), inference(negUnitSimplification, [status(thm)], [c_78, c_66, c_60, c_624, c_654])).
% 5.10/1.91  tff(c_769, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6')) | ~r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_80, c_767])).
% 5.10/1.91  tff(c_772, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_54, c_52, c_48, c_46, c_44, c_40, c_79, c_769])).
% 5.10/1.91  tff(c_773, plain, (r2_funct_2(u1_struct_0(k2_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_3', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_5'), k3_tmap_1('#skF_1', '#skF_2', '#skF_4', k2_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_772])).
% 5.10/1.91  tff(c_16, plain, (![D_126, E_130, A_70, B_102, F_132, C_118]: (v5_pre_topc(k10_tmap_1(A_70, B_102, C_118, D_126, E_130, F_132), k1_tsep_1(A_70, C_118, D_126), B_102) | ~r4_tsep_1(A_70, C_118, D_126) | ~r2_funct_2(u1_struct_0(k2_tsep_1(A_70, C_118, D_126)), u1_struct_0(B_102), k3_tmap_1(A_70, B_102, C_118, k2_tsep_1(A_70, C_118, D_126), E_130), k3_tmap_1(A_70, B_102, D_126, k2_tsep_1(A_70, C_118, D_126), F_132)) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_126), u1_struct_0(B_102)))) | ~v5_pre_topc(F_132, D_126, B_102) | ~v1_funct_2(F_132, u1_struct_0(D_126), u1_struct_0(B_102)) | ~v1_funct_1(F_132) | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_118), u1_struct_0(B_102)))) | ~v5_pre_topc(E_130, C_118, B_102) | ~v1_funct_2(E_130, u1_struct_0(C_118), u1_struct_0(B_102)) | ~v1_funct_1(E_130) | r1_tsep_1(C_118, D_126) | ~m1_pre_topc(D_126, A_70) | v2_struct_0(D_126) | ~m1_pre_topc(C_118, A_70) | v2_struct_0(C_118) | ~l1_pre_topc(B_102) | ~v2_pre_topc(B_102) | v2_struct_0(B_102) | ~l1_pre_topc(A_70) | ~v2_pre_topc(A_70) | v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_177])).
% 5.10/1.91  tff(c_776, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_6', '#skF_4', '#skF_2') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | r1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_773, c_16])).
% 5.10/1.91  tff(c_783, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | r1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_62, c_56, c_54, c_52, c_50, c_48, c_46, c_44, c_42, c_40, c_38, c_776])).
% 5.10/1.91  tff(c_784, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_60, c_624, c_344, c_783])).
% 5.10/1.91  tff(c_795, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_borsuk_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_784])).
% 5.10/1.91  tff(c_798, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_62, c_58, c_56, c_795])).
% 5.10/1.91  tff(c_800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_798])).
% 5.10/1.91  tff(c_804, plain, (![A_469]: (v5_pre_topc(k10_tmap_1(A_469, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_tsep_1(A_469, '#skF_3', '#skF_4'), '#skF_2') | ~r4_tsep_1(A_469, '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', A_469) | ~m1_pre_topc('#skF_3', A_469) | ~l1_pre_topc(A_469) | ~v2_pre_topc(A_469) | v2_struct_0(A_469))), inference(splitRight, [status(thm)], [c_618])).
% 5.10/1.91  tff(c_807, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_38, c_804])).
% 5.10/1.91  tff(c_809, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_62, c_56, c_807])).
% 5.10/1.91  tff(c_810, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_78, c_344, c_809])).
% 5.10/1.91  tff(c_813, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_borsuk_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_810])).
% 5.10/1.91  tff(c_816, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_64, c_62, c_58, c_56, c_813])).
% 5.10/1.91  tff(c_818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_816])).
% 5.10/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.10/1.91  
% 5.10/1.91  Inference rules
% 5.10/1.91  ----------------------
% 5.10/1.91  #Ref     : 0
% 5.10/1.91  #Sup     : 107
% 5.10/1.91  #Fact    : 0
% 5.10/1.91  #Define  : 0
% 5.10/1.91  #Split   : 10
% 5.10/1.91  #Chain   : 0
% 5.10/1.91  #Close   : 0
% 5.10/1.91  
% 5.10/1.91  Ordering : KBO
% 5.10/1.91  
% 5.10/1.91  Simplification rules
% 5.10/1.91  ----------------------
% 5.10/1.91  #Subsume      : 19
% 5.10/1.91  #Demod        : 343
% 5.10/1.91  #Tautology    : 5
% 5.10/1.91  #SimpNegUnit  : 97
% 5.10/1.91  #BackRed      : 0
% 5.10/1.91  
% 5.10/1.91  #Partial instantiations: 0
% 5.10/1.91  #Strategies tried      : 1
% 5.10/1.91  
% 5.10/1.91  Timing (in seconds)
% 5.10/1.91  ----------------------
% 5.10/1.91  Preprocessing        : 0.48
% 5.10/1.91  Parsing              : 0.23
% 5.10/1.91  CNF conversion       : 0.09
% 5.10/1.91  Main loop            : 0.69
% 5.10/1.91  Inferencing          : 0.24
% 5.10/1.91  Reduction            : 0.22
% 5.10/1.91  Demodulation         : 0.16
% 5.10/1.91  BG Simplification    : 0.04
% 5.10/1.91  Subsumption          : 0.18
% 5.10/1.91  Abstraction          : 0.03
% 5.10/1.91  MUC search           : 0.00
% 5.10/1.91  Cooper               : 0.00
% 5.10/1.91  Total                : 1.23
% 5.10/1.91  Index Insertion      : 0.00
% 5.10/1.91  Index Deletion       : 0.00
% 5.10/1.91  Index Matching       : 0.00
% 5.10/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
