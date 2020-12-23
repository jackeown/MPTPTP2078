%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:14 EST 2020

% Result     : Theorem 8.62s
% Output     : CNFRefutation 8.74s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 806 expanded)
%              Number of leaves         :   33 ( 310 expanded)
%              Depth                    :   12
%              Number of atoms          :  754 (8606 expanded)
%              Number of equality atoms :   14 ( 372 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_260,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_tmap_1)).

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

tff(f_177,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

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

tff(f_196,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( v1_tsep_1(C,A)
                & m1_pre_topc(C,A) )
             => r4_tsep_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tsep_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_tmap_1)).

tff(c_86,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_84,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_82,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_66,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_60,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_58,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_90,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_88,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_76,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_70,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_52,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_892,plain,(
    ! [D_307,F_308,E_312,C_310,B_309,A_311] :
      ( m1_subset_1(k10_tmap_1(A_311,B_309,C_310,D_307,E_312,F_308),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_311,C_310,D_307)),u1_struct_0(B_309))))
      | ~ m1_subset_1(F_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_307),u1_struct_0(B_309))))
      | ~ v1_funct_2(F_308,u1_struct_0(D_307),u1_struct_0(B_309))
      | ~ v1_funct_1(F_308)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_310),u1_struct_0(B_309))))
      | ~ v1_funct_2(E_312,u1_struct_0(C_310),u1_struct_0(B_309))
      | ~ v1_funct_1(E_312)
      | ~ m1_pre_topc(D_307,A_311)
      | v2_struct_0(D_307)
      | ~ m1_pre_topc(C_310,A_311)
      | v2_struct_0(C_310)
      | ~ l1_pre_topc(B_309)
      | ~ v2_pre_topc(B_309)
      | v2_struct_0(B_309)
      | ~ l1_pre_topc(A_311)
      | ~ v2_pre_topc(A_311)
      | v2_struct_0(A_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_921,plain,(
    ! [B_309,E_312,F_308] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_309,'#skF_3','#skF_4',E_312,F_308),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_309))))
      | ~ m1_subset_1(F_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_309))))
      | ~ v1_funct_2(F_308,u1_struct_0('#skF_4'),u1_struct_0(B_309))
      | ~ v1_funct_1(F_308)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_309))))
      | ~ v1_funct_2(E_312,u1_struct_0('#skF_3'),u1_struct_0(B_309))
      | ~ v1_funct_1(E_312)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_309)
      | ~ v2_pre_topc(B_309)
      | v2_struct_0(B_309)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_892])).

tff(c_941,plain,(
    ! [B_309,E_312,F_308] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_309,'#skF_3','#skF_4',E_312,F_308),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_309))))
      | ~ m1_subset_1(F_308,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_309))))
      | ~ v1_funct_2(F_308,u1_struct_0('#skF_4'),u1_struct_0(B_309))
      | ~ v1_funct_1(F_308)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_309))))
      | ~ v1_funct_2(E_312,u1_struct_0('#skF_3'),u1_struct_0(B_309))
      | ~ v1_funct_1(E_312)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_309)
      | ~ v2_pre_topc(B_309)
      | v2_struct_0(B_309)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_76,c_70,c_921])).

tff(c_943,plain,(
    ! [B_313,E_314,F_315] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_313,'#skF_3','#skF_4',E_314,F_315),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_313))))
      | ~ m1_subset_1(F_315,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_313))))
      | ~ v1_funct_2(F_315,u1_struct_0('#skF_4'),u1_struct_0(B_313))
      | ~ v1_funct_1(F_315)
      | ~ m1_subset_1(E_314,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_313))))
      | ~ v1_funct_2(E_314,u1_struct_0('#skF_3'),u1_struct_0(B_313))
      | ~ v1_funct_1(E_314)
      | ~ l1_pre_topc(B_313)
      | ~ v2_pre_topc(B_313)
      | v2_struct_0(B_313) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_74,c_941])).

tff(c_176,plain,(
    ! [E_151,B_148,A_150,D_146,C_149,F_147] :
      ( v1_funct_1(k10_tmap_1(A_150,B_148,C_149,D_146,E_151,F_147))
      | ~ m1_subset_1(F_147,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_146),u1_struct_0(B_148))))
      | ~ v1_funct_2(F_147,u1_struct_0(D_146),u1_struct_0(B_148))
      | ~ v1_funct_1(F_147)
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149),u1_struct_0(B_148))))
      | ~ v1_funct_2(E_151,u1_struct_0(C_149),u1_struct_0(B_148))
      | ~ v1_funct_1(E_151)
      | ~ m1_pre_topc(D_146,A_150)
      | v2_struct_0(D_146)
      | ~ m1_pre_topc(C_149,A_150)
      | v2_struct_0(C_149)
      | ~ l1_pre_topc(B_148)
      | ~ v2_pre_topc(B_148)
      | v2_struct_0(B_148)
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_182,plain,(
    ! [A_150,C_149,E_151] :
      ( v1_funct_1(k10_tmap_1(A_150,'#skF_2',C_149,'#skF_4',E_151,'#skF_6'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_151,u1_struct_0(C_149),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_151)
      | ~ m1_pre_topc('#skF_4',A_150)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_149,A_150)
      | v2_struct_0(C_149)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_54,c_176])).

tff(c_190,plain,(
    ! [A_150,C_149,E_151] :
      ( v1_funct_1(k10_tmap_1(A_150,'#skF_2',C_149,'#skF_4',E_151,'#skF_6'))
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_151,u1_struct_0(C_149),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_151)
      | ~ m1_pre_topc('#skF_4',A_150)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(C_149,A_150)
      | v2_struct_0(C_149)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_150)
      | ~ v2_pre_topc(A_150)
      | v2_struct_0(A_150) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_60,c_58,c_182])).

tff(c_214,plain,(
    ! [A_157,C_158,E_159] :
      ( v1_funct_1(k10_tmap_1(A_157,'#skF_2',C_158,'#skF_4',E_159,'#skF_6'))
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_158),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_159,u1_struct_0(C_158),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_159)
      | ~ m1_pre_topc('#skF_4',A_157)
      | ~ m1_pre_topc(C_158,A_157)
      | v2_struct_0(C_158)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_74,c_190])).

tff(c_219,plain,(
    ! [A_157] :
      ( v1_funct_1(k10_tmap_1(A_157,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_157)
      | ~ m1_pre_topc('#skF_3',A_157)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_62,c_214])).

tff(c_228,plain,(
    ! [A_157] :
      ( v1_funct_1(k10_tmap_1(A_157,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_157)
      | ~ m1_pre_topc('#skF_3',A_157)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_219])).

tff(c_235,plain,(
    ! [A_161] :
      ( v1_funct_1(k10_tmap_1(A_161,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_161)
      | ~ m1_pre_topc('#skF_3',A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_228])).

tff(c_46,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_135,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_238,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_235,c_135])).

tff(c_241,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_76,c_70,c_238])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_241])).

tff(c_244,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_246,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_984,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_943,c_246])).

tff(c_1024,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_68,c_66,c_62,c_60,c_58,c_54,c_984])).

tff(c_1026,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1024])).

tff(c_1027,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_1034,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1027])).

tff(c_1302,plain,(
    ! [C_413,D_410,A_414,E_415,F_411,B_412] :
      ( v1_funct_2(k10_tmap_1(A_414,B_412,C_413,D_410,E_415,F_411),u1_struct_0(k1_tsep_1(A_414,C_413,D_410)),u1_struct_0(B_412))
      | ~ m1_subset_1(F_411,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_410),u1_struct_0(B_412))))
      | ~ v1_funct_2(F_411,u1_struct_0(D_410),u1_struct_0(B_412))
      | ~ v1_funct_1(F_411)
      | ~ m1_subset_1(E_415,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_413),u1_struct_0(B_412))))
      | ~ v1_funct_2(E_415,u1_struct_0(C_413),u1_struct_0(B_412))
      | ~ v1_funct_1(E_415)
      | ~ m1_pre_topc(D_410,A_414)
      | v2_struct_0(D_410)
      | ~ m1_pre_topc(C_413,A_414)
      | v2_struct_0(C_413)
      | ~ l1_pre_topc(B_412)
      | ~ v2_pre_topc(B_412)
      | v2_struct_0(B_412)
      | ~ l1_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1305,plain,(
    ! [B_412,E_415,F_411] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_412,'#skF_3','#skF_4',E_415,F_411),u1_struct_0('#skF_1'),u1_struct_0(B_412))
      | ~ m1_subset_1(F_411,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_412))))
      | ~ v1_funct_2(F_411,u1_struct_0('#skF_4'),u1_struct_0(B_412))
      | ~ v1_funct_1(F_411)
      | ~ m1_subset_1(E_415,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_412))))
      | ~ v1_funct_2(E_415,u1_struct_0('#skF_3'),u1_struct_0(B_412))
      | ~ v1_funct_1(E_415)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_412)
      | ~ v2_pre_topc(B_412)
      | v2_struct_0(B_412)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1302])).

tff(c_1307,plain,(
    ! [B_412,E_415,F_411] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_412,'#skF_3','#skF_4',E_415,F_411),u1_struct_0('#skF_1'),u1_struct_0(B_412))
      | ~ m1_subset_1(F_411,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_412))))
      | ~ v1_funct_2(F_411,u1_struct_0('#skF_4'),u1_struct_0(B_412))
      | ~ v1_funct_1(F_411)
      | ~ m1_subset_1(E_415,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_412))))
      | ~ v1_funct_2(E_415,u1_struct_0('#skF_3'),u1_struct_0(B_412))
      | ~ v1_funct_1(E_415)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_412)
      | ~ v2_pre_topc(B_412)
      | v2_struct_0(B_412)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_76,c_70,c_1305])).

tff(c_1320,plain,(
    ! [B_418,E_419,F_420] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_418,'#skF_3','#skF_4',E_419,F_420),u1_struct_0('#skF_1'),u1_struct_0(B_418))
      | ~ m1_subset_1(F_420,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_418))))
      | ~ v1_funct_2(F_420,u1_struct_0('#skF_4'),u1_struct_0(B_418))
      | ~ v1_funct_1(F_420)
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_418))))
      | ~ v1_funct_2(E_419,u1_struct_0('#skF_3'),u1_struct_0(B_418))
      | ~ v1_funct_1(E_419)
      | ~ l1_pre_topc(B_418)
      | ~ v2_pre_topc(B_418)
      | v2_struct_0(B_418) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_74,c_1307])).

tff(c_1325,plain,(
    ! [E_419] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_419,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_419,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_419)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_1320])).

tff(c_1329,plain,(
    ! [E_419] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_419,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_419,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_419,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_419)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_60,c_58,c_1325])).

tff(c_1331,plain,(
    ! [E_421] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_421,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_421,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_421,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_421) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1329])).

tff(c_1338,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1331])).

tff(c_1345,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1338])).

tff(c_1347,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1034,c_1345])).

tff(c_1348,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1027])).

tff(c_245,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1349,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1027])).

tff(c_1028,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_42,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_1379,plain,(
    ! [E_435,A_432,C_431,D_434,B_433] :
      ( v1_funct_2(k3_tmap_1(A_432,B_433,C_431,D_434,E_435),u1_struct_0(D_434),u1_struct_0(B_433))
      | ~ m1_subset_1(E_435,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_431),u1_struct_0(B_433))))
      | ~ v1_funct_2(E_435,u1_struct_0(C_431),u1_struct_0(B_433))
      | ~ v1_funct_1(E_435)
      | ~ m1_pre_topc(D_434,A_432)
      | ~ m1_pre_topc(C_431,A_432)
      | ~ l1_pre_topc(B_433)
      | ~ v2_pre_topc(B_433)
      | v2_struct_0(B_433)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1381,plain,(
    ! [A_432,D_434] :
      ( v1_funct_2(k3_tmap_1(A_432,'#skF_2','#skF_1',D_434,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_434),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_434,A_432)
      | ~ m1_pre_topc('#skF_1',A_432)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(resolution,[status(thm)],[c_1028,c_1379])).

tff(c_1388,plain,(
    ! [A_432,D_434] :
      ( v1_funct_2(k3_tmap_1(A_432,'#skF_2','#skF_1',D_434,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_434),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_434,A_432)
      | ~ m1_pre_topc('#skF_1',A_432)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_245,c_1349,c_1381])).

tff(c_1389,plain,(
    ! [A_432,D_434] :
      ( v1_funct_2(k3_tmap_1(A_432,'#skF_2','#skF_1',D_434,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_434),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_434,A_432)
      | ~ m1_pre_topc('#skF_1',A_432)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432)
      | v2_struct_0(A_432) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1388])).

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

tff(c_1358,plain,(
    ! [B_424,E_426,C_422,D_425,A_423] :
      ( v1_funct_1(k3_tmap_1(A_423,B_424,C_422,D_425,E_426))
      | ~ m1_subset_1(E_426,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_422),u1_struct_0(B_424))))
      | ~ v1_funct_2(E_426,u1_struct_0(C_422),u1_struct_0(B_424))
      | ~ v1_funct_1(E_426)
      | ~ m1_pre_topc(D_425,A_423)
      | ~ m1_pre_topc(C_422,A_423)
      | ~ l1_pre_topc(B_424)
      | ~ v2_pre_topc(B_424)
      | v2_struct_0(B_424)
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1360,plain,(
    ! [A_423,D_425] :
      ( v1_funct_1(k3_tmap_1(A_423,'#skF_2','#skF_1',D_425,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_425,A_423)
      | ~ m1_pre_topc('#skF_1',A_423)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(resolution,[status(thm)],[c_1028,c_1358])).

tff(c_1367,plain,(
    ! [A_423,D_425] :
      ( v1_funct_1(k3_tmap_1(A_423,'#skF_2','#skF_1',D_425,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_425,A_423)
      | ~ m1_pre_topc('#skF_1',A_423)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_245,c_1349,c_1360])).

tff(c_1368,plain,(
    ! [A_423,D_425] :
      ( v1_funct_1(k3_tmap_1(A_423,'#skF_2','#skF_1',D_425,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_425,A_423)
      | ~ m1_pre_topc('#skF_1',A_423)
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1367])).

tff(c_50,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_93,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50])).

tff(c_112,plain,(
    ! [D_119,C_120,A_121,B_122] :
      ( D_119 = C_120
      | ~ r2_funct_2(A_121,B_122,C_120,D_119)
      | ~ m1_subset_1(D_119,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_2(D_119,A_121,B_122)
      | ~ v1_funct_1(D_119)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122)))
      | ~ v1_funct_2(C_120,A_121,B_122)
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_114,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_93,c_112])).

tff(c_123,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_114])).

tff(c_1753,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_1763,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1368,c_1753])).

tff(c_1766,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_76,c_1763])).

tff(c_1767,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1766])).

tff(c_1770,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1767])).

tff(c_1774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1770])).

tff(c_1775,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_1779,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1775])).

tff(c_1782,plain,
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
    inference(resolution,[status(thm)],[c_12,c_1779])).

tff(c_1785,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_84,c_82,c_76,c_245,c_1349,c_1028,c_1782])).

tff(c_1786,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_1785])).

tff(c_1789,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1786])).

tff(c_1793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1789])).

tff(c_1794,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1775])).

tff(c_1837,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1794])).

tff(c_1850,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1389,c_1837])).

tff(c_1853,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_76,c_1850])).

tff(c_1854,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1853])).

tff(c_1857,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1854])).

tff(c_1861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1857])).

tff(c_1862,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1794])).

tff(c_64,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_48,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_94,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48])).

tff(c_116,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_94,c_112])).

tff(c_126,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_116])).

tff(c_1578,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_1581,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1368,c_1578])).

tff(c_1584,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_70,c_1581])).

tff(c_1585,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1584])).

tff(c_1588,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1585])).

tff(c_1592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1588])).

tff(c_1593,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_1616,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1593])).

tff(c_1619,plain,
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
    inference(resolution,[status(thm)],[c_12,c_1616])).

tff(c_1622,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_84,c_82,c_70,c_245,c_1349,c_1028,c_1619])).

tff(c_1623,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_1622])).

tff(c_1626,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1623])).

tff(c_1630,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1626])).

tff(c_1631,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1593])).

tff(c_1674,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1631])).

tff(c_1677,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1389,c_1674])).

tff(c_1680,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_70,c_1677])).

tff(c_1681,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1680])).

tff(c_1684,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1681])).

tff(c_1688,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1684])).

tff(c_1689,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1631])).

tff(c_56,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_78,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_72,plain,(
    v1_tsep_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_44,plain,(
    ! [A_48,B_52,C_54] :
      ( r4_tsep_1(A_48,B_52,C_54)
      | ~ m1_pre_topc(C_54,A_48)
      | ~ v1_tsep_1(C_54,A_48)
      | ~ m1_pre_topc(B_52,A_48)
      | ~ v1_tsep_1(B_52,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1462,plain,(
    ! [C_463,B_460,D_462,A_464,E_461] :
      ( v1_funct_1(k3_tmap_1(A_464,B_460,k1_tsep_1(A_464,C_463,D_462),C_463,E_461))
      | ~ v5_pre_topc(E_461,k1_tsep_1(A_464,C_463,D_462),B_460)
      | ~ m1_subset_1(E_461,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_464,C_463,D_462)),u1_struct_0(B_460))))
      | ~ v1_funct_2(E_461,u1_struct_0(k1_tsep_1(A_464,C_463,D_462)),u1_struct_0(B_460))
      | ~ v1_funct_1(E_461)
      | ~ r4_tsep_1(A_464,C_463,D_462)
      | ~ m1_pre_topc(D_462,A_464)
      | v2_struct_0(D_462)
      | ~ m1_pre_topc(C_463,A_464)
      | v2_struct_0(C_463)
      | ~ l1_pre_topc(B_460)
      | ~ v2_pre_topc(B_460)
      | v2_struct_0(B_460)
      | ~ l1_pre_topc(A_464)
      | ~ v2_pre_topc(A_464)
      | v2_struct_0(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1467,plain,(
    ! [B_460,E_461] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_460,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_461))
      | ~ v5_pre_topc(E_461,k1_tsep_1('#skF_1','#skF_3','#skF_4'),B_460)
      | ~ m1_subset_1(E_461,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_460))))
      | ~ v1_funct_2(E_461,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_460))
      | ~ v1_funct_1(E_461)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_460)
      | ~ v2_pre_topc(B_460)
      | v2_struct_0(B_460)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1462])).

tff(c_1470,plain,(
    ! [B_460,E_461] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_460,'#skF_1','#skF_3',E_461))
      | ~ v5_pre_topc(E_461,'#skF_1',B_460)
      | ~ m1_subset_1(E_461,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_460))))
      | ~ v1_funct_2(E_461,u1_struct_0('#skF_1'),u1_struct_0(B_460))
      | ~ v1_funct_1(E_461)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_460)
      | ~ v2_pre_topc(B_460)
      | v2_struct_0(B_460)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_76,c_70,c_52,c_52,c_52,c_1467])).

tff(c_1471,plain,(
    ! [B_460,E_461] :
      ( v1_funct_1(k3_tmap_1('#skF_1',B_460,'#skF_1','#skF_3',E_461))
      | ~ v5_pre_topc(E_461,'#skF_1',B_460)
      | ~ m1_subset_1(E_461,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_460))))
      | ~ v1_funct_2(E_461,u1_struct_0('#skF_1'),u1_struct_0(B_460))
      | ~ v1_funct_1(E_461)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ l1_pre_topc(B_460)
      | ~ v2_pre_topc(B_460)
      | v2_struct_0(B_460) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_74,c_1470])).

tff(c_1473,plain,(
    ~ r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1471])).

tff(c_1476,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_tsep_1('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ v1_tsep_1('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_1473])).

tff(c_1479,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_76,c_72,c_70,c_1476])).

tff(c_1481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1479])).

tff(c_1483,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1471])).

tff(c_2743,plain,(
    ! [E_601,B_600,C_603,A_604,D_602] :
      ( v5_pre_topc(E_601,k1_tsep_1(A_604,C_603,D_602),B_600)
      | ~ m1_subset_1(k3_tmap_1(A_604,B_600,k1_tsep_1(A_604,C_603,D_602),D_602,E_601),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_602),u1_struct_0(B_600))))
      | ~ v5_pre_topc(k3_tmap_1(A_604,B_600,k1_tsep_1(A_604,C_603,D_602),D_602,E_601),D_602,B_600)
      | ~ v1_funct_2(k3_tmap_1(A_604,B_600,k1_tsep_1(A_604,C_603,D_602),D_602,E_601),u1_struct_0(D_602),u1_struct_0(B_600))
      | ~ v1_funct_1(k3_tmap_1(A_604,B_600,k1_tsep_1(A_604,C_603,D_602),D_602,E_601))
      | ~ m1_subset_1(k3_tmap_1(A_604,B_600,k1_tsep_1(A_604,C_603,D_602),C_603,E_601),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_603),u1_struct_0(B_600))))
      | ~ v5_pre_topc(k3_tmap_1(A_604,B_600,k1_tsep_1(A_604,C_603,D_602),C_603,E_601),C_603,B_600)
      | ~ v1_funct_2(k3_tmap_1(A_604,B_600,k1_tsep_1(A_604,C_603,D_602),C_603,E_601),u1_struct_0(C_603),u1_struct_0(B_600))
      | ~ v1_funct_1(k3_tmap_1(A_604,B_600,k1_tsep_1(A_604,C_603,D_602),C_603,E_601))
      | ~ m1_subset_1(E_601,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_604,C_603,D_602)),u1_struct_0(B_600))))
      | ~ v1_funct_2(E_601,u1_struct_0(k1_tsep_1(A_604,C_603,D_602)),u1_struct_0(B_600))
      | ~ v1_funct_1(E_601)
      | ~ r4_tsep_1(A_604,C_603,D_602)
      | ~ m1_pre_topc(D_602,A_604)
      | v2_struct_0(D_602)
      | ~ m1_pre_topc(C_603,A_604)
      | v2_struct_0(C_603)
      | ~ l1_pre_topc(B_600)
      | ~ v2_pre_topc(B_600)
      | v2_struct_0(B_600)
      | ~ l1_pre_topc(A_604)
      | ~ v2_pre_topc(A_604)
      | v2_struct_0(A_604) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_2753,plain,(
    ! [E_601,B_600] :
      ( v5_pre_topc(E_601,k1_tsep_1('#skF_1','#skF_3','#skF_4'),B_600)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_600,'#skF_1','#skF_4',E_601),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_600))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_600,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_601),'#skF_4',B_600)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_600,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_601),u1_struct_0('#skF_4'),u1_struct_0(B_600))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_600,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_601))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_600,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_601),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_600))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_600,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_601),'#skF_3',B_600)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_600,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_601),u1_struct_0('#skF_3'),u1_struct_0(B_600))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_600,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_601))
      | ~ m1_subset_1(E_601,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_600))))
      | ~ v1_funct_2(E_601,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_600))
      | ~ v1_funct_1(E_601)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_600)
      | ~ v2_pre_topc(B_600)
      | v2_struct_0(B_600)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2743])).

tff(c_2758,plain,(
    ! [E_601,B_600] :
      ( v5_pre_topc(E_601,'#skF_1',B_600)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_600,'#skF_1','#skF_4',E_601),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_600))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_600,'#skF_1','#skF_4',E_601),'#skF_4',B_600)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_600,'#skF_1','#skF_4',E_601),u1_struct_0('#skF_4'),u1_struct_0(B_600))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_600,'#skF_1','#skF_4',E_601))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_600,'#skF_1','#skF_3',E_601),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_600))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_600,'#skF_1','#skF_3',E_601),'#skF_3',B_600)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_600,'#skF_1','#skF_3',E_601),u1_struct_0('#skF_3'),u1_struct_0(B_600))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_600,'#skF_1','#skF_3',E_601))
      | ~ m1_subset_1(E_601,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_600))))
      | ~ v1_funct_2(E_601,u1_struct_0('#skF_1'),u1_struct_0(B_600))
      | ~ v1_funct_1(E_601)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_600)
      | ~ v2_pre_topc(B_600)
      | v2_struct_0(B_600)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_76,c_70,c_1483,c_52,c_52,c_52,c_52,c_52,c_52,c_52,c_52,c_52,c_52,c_2753])).

tff(c_4352,plain,(
    ! [E_870,B_871] :
      ( v5_pre_topc(E_870,'#skF_1',B_871)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_871,'#skF_1','#skF_4',E_870),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_871))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_871,'#skF_1','#skF_4',E_870),'#skF_4',B_871)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_871,'#skF_1','#skF_4',E_870),u1_struct_0('#skF_4'),u1_struct_0(B_871))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_871,'#skF_1','#skF_4',E_870))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_871,'#skF_1','#skF_3',E_870),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_871))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_871,'#skF_1','#skF_3',E_870),'#skF_3',B_871)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_871,'#skF_1','#skF_3',E_870),u1_struct_0('#skF_3'),u1_struct_0(B_871))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_871,'#skF_1','#skF_3',E_870))
      | ~ m1_subset_1(E_870,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_871))))
      | ~ v1_funct_2(E_870,u1_struct_0('#skF_1'),u1_struct_0(B_871))
      | ~ v1_funct_1(E_870)
      | ~ l1_pre_topc(B_871)
      | ~ v2_pre_topc(B_871)
      | v2_struct_0(B_871) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_74,c_2758])).

tff(c_4358,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_4352])).

tff(c_4365,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_245,c_1349,c_1028,c_68,c_1862,c_66,c_1862,c_64,c_1862,c_62,c_60,c_1689,c_58,c_1689,c_56,c_1689,c_54,c_1689,c_4358])).

tff(c_4367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1348,c_4365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.62/2.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.74/3.02  
% 8.74/3.02  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.74/3.02  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.74/3.02  
% 8.74/3.02  %Foreground sorts:
% 8.74/3.02  
% 8.74/3.02  
% 8.74/3.02  %Background operators:
% 8.74/3.02  
% 8.74/3.02  
% 8.74/3.02  %Foreground operators:
% 8.74/3.02  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.74/3.02  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.74/3.02  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.74/3.02  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.74/3.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.74/3.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.74/3.02  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.74/3.02  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 8.74/3.02  tff('#skF_5', type, '#skF_5': $i).
% 8.74/3.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.74/3.02  tff('#skF_6', type, '#skF_6': $i).
% 8.74/3.02  tff('#skF_2', type, '#skF_2': $i).
% 8.74/3.02  tff('#skF_3', type, '#skF_3': $i).
% 8.74/3.02  tff('#skF_1', type, '#skF_1': $i).
% 8.74/3.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.74/3.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.74/3.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.74/3.02  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 8.74/3.02  tff('#skF_4', type, '#skF_4': $i).
% 8.74/3.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.74/3.02  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 8.74/3.02  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.74/3.02  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.74/3.02  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.74/3.02  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.74/3.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.74/3.02  
% 8.74/3.06  tff(f_260, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_tsep_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, A)) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((A = k1_tsep_1(A, C, D)) & r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E)) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_tmap_1)).
% 8.74/3.06  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 8.74/3.06  tff(f_177, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.74/3.06  tff(f_113, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 8.74/3.06  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 8.74/3.06  tff(f_196, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((v1_tsep_1(C, A) & m1_pre_topc(C, A)) => r4_tsep_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tsep_1)).
% 8.74/3.06  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_tmap_1)).
% 8.74/3.06  tff(c_86, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_84, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_82, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_66, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_60, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_58, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_92, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_74, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_90, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_88, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_76, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_70, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_52, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_892, plain, (![D_307, F_308, E_312, C_310, B_309, A_311]: (m1_subset_1(k10_tmap_1(A_311, B_309, C_310, D_307, E_312, F_308), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_311, C_310, D_307)), u1_struct_0(B_309)))) | ~m1_subset_1(F_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_307), u1_struct_0(B_309)))) | ~v1_funct_2(F_308, u1_struct_0(D_307), u1_struct_0(B_309)) | ~v1_funct_1(F_308) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_310), u1_struct_0(B_309)))) | ~v1_funct_2(E_312, u1_struct_0(C_310), u1_struct_0(B_309)) | ~v1_funct_1(E_312) | ~m1_pre_topc(D_307, A_311) | v2_struct_0(D_307) | ~m1_pre_topc(C_310, A_311) | v2_struct_0(C_310) | ~l1_pre_topc(B_309) | ~v2_pre_topc(B_309) | v2_struct_0(B_309) | ~l1_pre_topc(A_311) | ~v2_pre_topc(A_311) | v2_struct_0(A_311))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.74/3.06  tff(c_921, plain, (![B_309, E_312, F_308]: (m1_subset_1(k10_tmap_1('#skF_1', B_309, '#skF_3', '#skF_4', E_312, F_308), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_309)))) | ~m1_subset_1(F_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_309)))) | ~v1_funct_2(F_308, u1_struct_0('#skF_4'), u1_struct_0(B_309)) | ~v1_funct_1(F_308) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_309)))) | ~v1_funct_2(E_312, u1_struct_0('#skF_3'), u1_struct_0(B_309)) | ~v1_funct_1(E_312) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_309) | ~v2_pre_topc(B_309) | v2_struct_0(B_309) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_892])).
% 8.74/3.06  tff(c_941, plain, (![B_309, E_312, F_308]: (m1_subset_1(k10_tmap_1('#skF_1', B_309, '#skF_3', '#skF_4', E_312, F_308), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_309)))) | ~m1_subset_1(F_308, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_309)))) | ~v1_funct_2(F_308, u1_struct_0('#skF_4'), u1_struct_0(B_309)) | ~v1_funct_1(F_308) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_309)))) | ~v1_funct_2(E_312, u1_struct_0('#skF_3'), u1_struct_0(B_309)) | ~v1_funct_1(E_312) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_309) | ~v2_pre_topc(B_309) | v2_struct_0(B_309) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_76, c_70, c_921])).
% 8.74/3.06  tff(c_943, plain, (![B_313, E_314, F_315]: (m1_subset_1(k10_tmap_1('#skF_1', B_313, '#skF_3', '#skF_4', E_314, F_315), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_313)))) | ~m1_subset_1(F_315, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_313)))) | ~v1_funct_2(F_315, u1_struct_0('#skF_4'), u1_struct_0(B_313)) | ~v1_funct_1(F_315) | ~m1_subset_1(E_314, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_313)))) | ~v1_funct_2(E_314, u1_struct_0('#skF_3'), u1_struct_0(B_313)) | ~v1_funct_1(E_314) | ~l1_pre_topc(B_313) | ~v2_pre_topc(B_313) | v2_struct_0(B_313))), inference(negUnitSimplification, [status(thm)], [c_92, c_80, c_74, c_941])).
% 8.74/3.06  tff(c_176, plain, (![E_151, B_148, A_150, D_146, C_149, F_147]: (v1_funct_1(k10_tmap_1(A_150, B_148, C_149, D_146, E_151, F_147)) | ~m1_subset_1(F_147, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_146), u1_struct_0(B_148)))) | ~v1_funct_2(F_147, u1_struct_0(D_146), u1_struct_0(B_148)) | ~v1_funct_1(F_147) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0(B_148)))) | ~v1_funct_2(E_151, u1_struct_0(C_149), u1_struct_0(B_148)) | ~v1_funct_1(E_151) | ~m1_pre_topc(D_146, A_150) | v2_struct_0(D_146) | ~m1_pre_topc(C_149, A_150) | v2_struct_0(C_149) | ~l1_pre_topc(B_148) | ~v2_pre_topc(B_148) | v2_struct_0(B_148) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.74/3.06  tff(c_182, plain, (![A_150, C_149, E_151]: (v1_funct_1(k10_tmap_1(A_150, '#skF_2', C_149, '#skF_4', E_151, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_151, u1_struct_0(C_149), u1_struct_0('#skF_2')) | ~v1_funct_1(E_151) | ~m1_pre_topc('#skF_4', A_150) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_149, A_150) | v2_struct_0(C_149) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(resolution, [status(thm)], [c_54, c_176])).
% 8.74/3.06  tff(c_190, plain, (![A_150, C_149, E_151]: (v1_funct_1(k10_tmap_1(A_150, '#skF_2', C_149, '#skF_4', E_151, '#skF_6')) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_151, u1_struct_0(C_149), u1_struct_0('#skF_2')) | ~v1_funct_1(E_151) | ~m1_pre_topc('#skF_4', A_150) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_149, A_150) | v2_struct_0(C_149) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_60, c_58, c_182])).
% 8.74/3.06  tff(c_214, plain, (![A_157, C_158, E_159]: (v1_funct_1(k10_tmap_1(A_157, '#skF_2', C_158, '#skF_4', E_159, '#skF_6')) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_158), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_159, u1_struct_0(C_158), u1_struct_0('#skF_2')) | ~v1_funct_1(E_159) | ~m1_pre_topc('#skF_4', A_157) | ~m1_pre_topc(C_158, A_157) | v2_struct_0(C_158) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(negUnitSimplification, [status(thm)], [c_86, c_74, c_190])).
% 8.74/3.06  tff(c_219, plain, (![A_157]: (v1_funct_1(k10_tmap_1(A_157, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_157) | ~m1_pre_topc('#skF_3', A_157) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_62, c_214])).
% 8.74/3.06  tff(c_228, plain, (![A_157]: (v1_funct_1(k10_tmap_1(A_157, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_157) | ~m1_pre_topc('#skF_3', A_157) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_219])).
% 8.74/3.06  tff(c_235, plain, (![A_161]: (v1_funct_1(k10_tmap_1(A_161, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_161) | ~m1_pre_topc('#skF_3', A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_80, c_228])).
% 8.74/3.06  tff(c_46, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_135, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_46])).
% 8.74/3.06  tff(c_238, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_235, c_135])).
% 8.74/3.06  tff(c_241, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_76, c_70, c_238])).
% 8.74/3.06  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_241])).
% 8.74/3.06  tff(c_244, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_46])).
% 8.74/3.06  tff(c_246, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_244])).
% 8.74/3.06  tff(c_984, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_943, c_246])).
% 8.74/3.06  tff(c_1024, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_68, c_66, c_62, c_60, c_58, c_54, c_984])).
% 8.74/3.06  tff(c_1026, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_1024])).
% 8.74/3.06  tff(c_1027, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_244])).
% 8.74/3.06  tff(c_1034, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1027])).
% 8.74/3.06  tff(c_1302, plain, (![C_413, D_410, A_414, E_415, F_411, B_412]: (v1_funct_2(k10_tmap_1(A_414, B_412, C_413, D_410, E_415, F_411), u1_struct_0(k1_tsep_1(A_414, C_413, D_410)), u1_struct_0(B_412)) | ~m1_subset_1(F_411, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_410), u1_struct_0(B_412)))) | ~v1_funct_2(F_411, u1_struct_0(D_410), u1_struct_0(B_412)) | ~v1_funct_1(F_411) | ~m1_subset_1(E_415, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_413), u1_struct_0(B_412)))) | ~v1_funct_2(E_415, u1_struct_0(C_413), u1_struct_0(B_412)) | ~v1_funct_1(E_415) | ~m1_pre_topc(D_410, A_414) | v2_struct_0(D_410) | ~m1_pre_topc(C_413, A_414) | v2_struct_0(C_413) | ~l1_pre_topc(B_412) | ~v2_pre_topc(B_412) | v2_struct_0(B_412) | ~l1_pre_topc(A_414) | ~v2_pre_topc(A_414) | v2_struct_0(A_414))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.74/3.06  tff(c_1305, plain, (![B_412, E_415, F_411]: (v1_funct_2(k10_tmap_1('#skF_1', B_412, '#skF_3', '#skF_4', E_415, F_411), u1_struct_0('#skF_1'), u1_struct_0(B_412)) | ~m1_subset_1(F_411, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_412)))) | ~v1_funct_2(F_411, u1_struct_0('#skF_4'), u1_struct_0(B_412)) | ~v1_funct_1(F_411) | ~m1_subset_1(E_415, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_412)))) | ~v1_funct_2(E_415, u1_struct_0('#skF_3'), u1_struct_0(B_412)) | ~v1_funct_1(E_415) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_412) | ~v2_pre_topc(B_412) | v2_struct_0(B_412) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1302])).
% 8.74/3.06  tff(c_1307, plain, (![B_412, E_415, F_411]: (v1_funct_2(k10_tmap_1('#skF_1', B_412, '#skF_3', '#skF_4', E_415, F_411), u1_struct_0('#skF_1'), u1_struct_0(B_412)) | ~m1_subset_1(F_411, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_412)))) | ~v1_funct_2(F_411, u1_struct_0('#skF_4'), u1_struct_0(B_412)) | ~v1_funct_1(F_411) | ~m1_subset_1(E_415, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_412)))) | ~v1_funct_2(E_415, u1_struct_0('#skF_3'), u1_struct_0(B_412)) | ~v1_funct_1(E_415) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_412) | ~v2_pre_topc(B_412) | v2_struct_0(B_412) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_76, c_70, c_1305])).
% 8.74/3.06  tff(c_1320, plain, (![B_418, E_419, F_420]: (v1_funct_2(k10_tmap_1('#skF_1', B_418, '#skF_3', '#skF_4', E_419, F_420), u1_struct_0('#skF_1'), u1_struct_0(B_418)) | ~m1_subset_1(F_420, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_418)))) | ~v1_funct_2(F_420, u1_struct_0('#skF_4'), u1_struct_0(B_418)) | ~v1_funct_1(F_420) | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_418)))) | ~v1_funct_2(E_419, u1_struct_0('#skF_3'), u1_struct_0(B_418)) | ~v1_funct_1(E_419) | ~l1_pre_topc(B_418) | ~v2_pre_topc(B_418) | v2_struct_0(B_418))), inference(negUnitSimplification, [status(thm)], [c_92, c_80, c_74, c_1307])).
% 8.74/3.06  tff(c_1325, plain, (![E_419]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_419, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_419, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_419) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_1320])).
% 8.74/3.06  tff(c_1329, plain, (![E_419]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_419, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_419, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_419, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_419) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_60, c_58, c_1325])).
% 8.74/3.06  tff(c_1331, plain, (![E_421]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_421, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_421, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_421, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_421))), inference(negUnitSimplification, [status(thm)], [c_86, c_1329])).
% 8.74/3.06  tff(c_1338, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_1331])).
% 8.74/3.06  tff(c_1345, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1338])).
% 8.74/3.06  tff(c_1347, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1034, c_1345])).
% 8.74/3.06  tff(c_1348, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1027])).
% 8.74/3.06  tff(c_245, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_46])).
% 8.74/3.06  tff(c_1349, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_1027])).
% 8.74/3.06  tff(c_1028, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_244])).
% 8.74/3.06  tff(c_42, plain, (![A_47]: (m1_pre_topc(A_47, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.74/3.06  tff(c_1379, plain, (![E_435, A_432, C_431, D_434, B_433]: (v1_funct_2(k3_tmap_1(A_432, B_433, C_431, D_434, E_435), u1_struct_0(D_434), u1_struct_0(B_433)) | ~m1_subset_1(E_435, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_431), u1_struct_0(B_433)))) | ~v1_funct_2(E_435, u1_struct_0(C_431), u1_struct_0(B_433)) | ~v1_funct_1(E_435) | ~m1_pre_topc(D_434, A_432) | ~m1_pre_topc(C_431, A_432) | ~l1_pre_topc(B_433) | ~v2_pre_topc(B_433) | v2_struct_0(B_433) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432) | v2_struct_0(A_432))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.74/3.06  tff(c_1381, plain, (![A_432, D_434]: (v1_funct_2(k3_tmap_1(A_432, '#skF_2', '#skF_1', D_434, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_434), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_434, A_432) | ~m1_pre_topc('#skF_1', A_432) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432) | v2_struct_0(A_432))), inference(resolution, [status(thm)], [c_1028, c_1379])).
% 8.74/3.06  tff(c_1388, plain, (![A_432, D_434]: (v1_funct_2(k3_tmap_1(A_432, '#skF_2', '#skF_1', D_434, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_434), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_434, A_432) | ~m1_pre_topc('#skF_1', A_432) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432) | v2_struct_0(A_432))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_245, c_1349, c_1381])).
% 8.74/3.06  tff(c_1389, plain, (![A_432, D_434]: (v1_funct_2(k3_tmap_1(A_432, '#skF_2', '#skF_1', D_434, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_434), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_434, A_432) | ~m1_pre_topc('#skF_1', A_432) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432) | v2_struct_0(A_432))), inference(negUnitSimplification, [status(thm)], [c_86, c_1388])).
% 8.74/3.06  tff(c_12, plain, (![D_14, E_15, B_12, A_11, C_13]: (m1_subset_1(k3_tmap_1(A_11, B_12, C_13, D_14, E_15), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_14), u1_struct_0(B_12)))) | ~m1_subset_1(E_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13), u1_struct_0(B_12)))) | ~v1_funct_2(E_15, u1_struct_0(C_13), u1_struct_0(B_12)) | ~v1_funct_1(E_15) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(C_13, A_11) | ~l1_pre_topc(B_12) | ~v2_pre_topc(B_12) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.74/3.06  tff(c_1358, plain, (![B_424, E_426, C_422, D_425, A_423]: (v1_funct_1(k3_tmap_1(A_423, B_424, C_422, D_425, E_426)) | ~m1_subset_1(E_426, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_422), u1_struct_0(B_424)))) | ~v1_funct_2(E_426, u1_struct_0(C_422), u1_struct_0(B_424)) | ~v1_funct_1(E_426) | ~m1_pre_topc(D_425, A_423) | ~m1_pre_topc(C_422, A_423) | ~l1_pre_topc(B_424) | ~v2_pre_topc(B_424) | v2_struct_0(B_424) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.74/3.06  tff(c_1360, plain, (![A_423, D_425]: (v1_funct_1(k3_tmap_1(A_423, '#skF_2', '#skF_1', D_425, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_425, A_423) | ~m1_pre_topc('#skF_1', A_423) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423))), inference(resolution, [status(thm)], [c_1028, c_1358])).
% 8.74/3.06  tff(c_1367, plain, (![A_423, D_425]: (v1_funct_1(k3_tmap_1(A_423, '#skF_2', '#skF_1', D_425, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_425, A_423) | ~m1_pre_topc('#skF_1', A_423) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_245, c_1349, c_1360])).
% 8.74/3.06  tff(c_1368, plain, (![A_423, D_425]: (v1_funct_1(k3_tmap_1(A_423, '#skF_2', '#skF_1', D_425, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_425, A_423) | ~m1_pre_topc('#skF_1', A_423) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423))), inference(negUnitSimplification, [status(thm)], [c_86, c_1367])).
% 8.74/3.06  tff(c_50, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_93, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50])).
% 8.74/3.06  tff(c_112, plain, (![D_119, C_120, A_121, B_122]: (D_119=C_120 | ~r2_funct_2(A_121, B_122, C_120, D_119) | ~m1_subset_1(D_119, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_2(D_119, A_121, B_122) | ~v1_funct_1(D_119) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))) | ~v1_funct_2(C_120, A_121, B_122) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.74/3.06  tff(c_114, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_93, c_112])).
% 8.74/3.06  tff(c_123, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_114])).
% 8.74/3.06  tff(c_1753, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_123])).
% 8.74/3.06  tff(c_1763, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1368, c_1753])).
% 8.74/3.06  tff(c_1766, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_76, c_1763])).
% 8.74/3.06  tff(c_1767, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_92, c_1766])).
% 8.74/3.06  tff(c_1770, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1767])).
% 8.74/3.06  tff(c_1774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_1770])).
% 8.74/3.06  tff(c_1775, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_123])).
% 8.74/3.06  tff(c_1779, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1775])).
% 8.74/3.06  tff(c_1782, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1779])).
% 8.74/3.06  tff(c_1785, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_84, c_82, c_76, c_245, c_1349, c_1028, c_1782])).
% 8.74/3.06  tff(c_1786, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_1785])).
% 8.74/3.06  tff(c_1789, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1786])).
% 8.74/3.06  tff(c_1793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_1789])).
% 8.74/3.06  tff(c_1794, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1775])).
% 8.74/3.06  tff(c_1837, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1794])).
% 8.74/3.06  tff(c_1850, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1389, c_1837])).
% 8.74/3.06  tff(c_1853, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_76, c_1850])).
% 8.74/3.06  tff(c_1854, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_92, c_1853])).
% 8.74/3.06  tff(c_1857, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1854])).
% 8.74/3.06  tff(c_1861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_1857])).
% 8.74/3.06  tff(c_1862, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1794])).
% 8.74/3.06  tff(c_64, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_48, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_94, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48])).
% 8.74/3.06  tff(c_116, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_94, c_112])).
% 8.74/3.06  tff(c_126, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_116])).
% 8.74/3.06  tff(c_1578, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_126])).
% 8.74/3.06  tff(c_1581, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1368, c_1578])).
% 8.74/3.06  tff(c_1584, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_70, c_1581])).
% 8.74/3.06  tff(c_1585, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_92, c_1584])).
% 8.74/3.06  tff(c_1588, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1585])).
% 8.74/3.06  tff(c_1592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_1588])).
% 8.74/3.06  tff(c_1593, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_126])).
% 8.74/3.06  tff(c_1616, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1593])).
% 8.74/3.06  tff(c_1619, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1616])).
% 8.74/3.06  tff(c_1622, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_84, c_82, c_70, c_245, c_1349, c_1028, c_1619])).
% 8.74/3.06  tff(c_1623, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_1622])).
% 8.74/3.06  tff(c_1626, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1623])).
% 8.74/3.06  tff(c_1630, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_1626])).
% 8.74/3.06  tff(c_1631, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1593])).
% 8.74/3.06  tff(c_1674, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1631])).
% 8.74/3.06  tff(c_1677, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1389, c_1674])).
% 8.74/3.06  tff(c_1680, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_70, c_1677])).
% 8.74/3.06  tff(c_1681, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_92, c_1680])).
% 8.74/3.06  tff(c_1684, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1681])).
% 8.74/3.06  tff(c_1688, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_1684])).
% 8.74/3.06  tff(c_1689, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1631])).
% 8.74/3.06  tff(c_56, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_78, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_72, plain, (v1_tsep_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_260])).
% 8.74/3.06  tff(c_44, plain, (![A_48, B_52, C_54]: (r4_tsep_1(A_48, B_52, C_54) | ~m1_pre_topc(C_54, A_48) | ~v1_tsep_1(C_54, A_48) | ~m1_pre_topc(B_52, A_48) | ~v1_tsep_1(B_52, A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_196])).
% 8.74/3.06  tff(c_1462, plain, (![C_463, B_460, D_462, A_464, E_461]: (v1_funct_1(k3_tmap_1(A_464, B_460, k1_tsep_1(A_464, C_463, D_462), C_463, E_461)) | ~v5_pre_topc(E_461, k1_tsep_1(A_464, C_463, D_462), B_460) | ~m1_subset_1(E_461, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_464, C_463, D_462)), u1_struct_0(B_460)))) | ~v1_funct_2(E_461, u1_struct_0(k1_tsep_1(A_464, C_463, D_462)), u1_struct_0(B_460)) | ~v1_funct_1(E_461) | ~r4_tsep_1(A_464, C_463, D_462) | ~m1_pre_topc(D_462, A_464) | v2_struct_0(D_462) | ~m1_pre_topc(C_463, A_464) | v2_struct_0(C_463) | ~l1_pre_topc(B_460) | ~v2_pre_topc(B_460) | v2_struct_0(B_460) | ~l1_pre_topc(A_464) | ~v2_pre_topc(A_464) | v2_struct_0(A_464))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.74/3.06  tff(c_1467, plain, (![B_460, E_461]: (v1_funct_1(k3_tmap_1('#skF_1', B_460, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_461)) | ~v5_pre_topc(E_461, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), B_460) | ~m1_subset_1(E_461, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_460)))) | ~v1_funct_2(E_461, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_460)) | ~v1_funct_1(E_461) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_460) | ~v2_pre_topc(B_460) | v2_struct_0(B_460) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1462])).
% 8.74/3.06  tff(c_1470, plain, (![B_460, E_461]: (v1_funct_1(k3_tmap_1('#skF_1', B_460, '#skF_1', '#skF_3', E_461)) | ~v5_pre_topc(E_461, '#skF_1', B_460) | ~m1_subset_1(E_461, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_460)))) | ~v1_funct_2(E_461, u1_struct_0('#skF_1'), u1_struct_0(B_460)) | ~v1_funct_1(E_461) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_460) | ~v2_pre_topc(B_460) | v2_struct_0(B_460) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_76, c_70, c_52, c_52, c_52, c_1467])).
% 8.74/3.06  tff(c_1471, plain, (![B_460, E_461]: (v1_funct_1(k3_tmap_1('#skF_1', B_460, '#skF_1', '#skF_3', E_461)) | ~v5_pre_topc(E_461, '#skF_1', B_460) | ~m1_subset_1(E_461, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_460)))) | ~v1_funct_2(E_461, u1_struct_0('#skF_1'), u1_struct_0(B_460)) | ~v1_funct_1(E_461) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~l1_pre_topc(B_460) | ~v2_pre_topc(B_460) | v2_struct_0(B_460))), inference(negUnitSimplification, [status(thm)], [c_92, c_80, c_74, c_1470])).
% 8.74/3.06  tff(c_1473, plain, (~r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1471])).
% 8.74/3.06  tff(c_1476, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_1473])).
% 8.74/3.06  tff(c_1479, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_76, c_72, c_70, c_1476])).
% 8.74/3.06  tff(c_1481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1479])).
% 8.74/3.06  tff(c_1483, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1471])).
% 8.74/3.06  tff(c_2743, plain, (![E_601, B_600, C_603, A_604, D_602]: (v5_pre_topc(E_601, k1_tsep_1(A_604, C_603, D_602), B_600) | ~m1_subset_1(k3_tmap_1(A_604, B_600, k1_tsep_1(A_604, C_603, D_602), D_602, E_601), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_602), u1_struct_0(B_600)))) | ~v5_pre_topc(k3_tmap_1(A_604, B_600, k1_tsep_1(A_604, C_603, D_602), D_602, E_601), D_602, B_600) | ~v1_funct_2(k3_tmap_1(A_604, B_600, k1_tsep_1(A_604, C_603, D_602), D_602, E_601), u1_struct_0(D_602), u1_struct_0(B_600)) | ~v1_funct_1(k3_tmap_1(A_604, B_600, k1_tsep_1(A_604, C_603, D_602), D_602, E_601)) | ~m1_subset_1(k3_tmap_1(A_604, B_600, k1_tsep_1(A_604, C_603, D_602), C_603, E_601), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_603), u1_struct_0(B_600)))) | ~v5_pre_topc(k3_tmap_1(A_604, B_600, k1_tsep_1(A_604, C_603, D_602), C_603, E_601), C_603, B_600) | ~v1_funct_2(k3_tmap_1(A_604, B_600, k1_tsep_1(A_604, C_603, D_602), C_603, E_601), u1_struct_0(C_603), u1_struct_0(B_600)) | ~v1_funct_1(k3_tmap_1(A_604, B_600, k1_tsep_1(A_604, C_603, D_602), C_603, E_601)) | ~m1_subset_1(E_601, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_604, C_603, D_602)), u1_struct_0(B_600)))) | ~v1_funct_2(E_601, u1_struct_0(k1_tsep_1(A_604, C_603, D_602)), u1_struct_0(B_600)) | ~v1_funct_1(E_601) | ~r4_tsep_1(A_604, C_603, D_602) | ~m1_pre_topc(D_602, A_604) | v2_struct_0(D_602) | ~m1_pre_topc(C_603, A_604) | v2_struct_0(C_603) | ~l1_pre_topc(B_600) | ~v2_pre_topc(B_600) | v2_struct_0(B_600) | ~l1_pre_topc(A_604) | ~v2_pre_topc(A_604) | v2_struct_0(A_604))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.74/3.06  tff(c_2753, plain, (![E_601, B_600]: (v5_pre_topc(E_601, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), B_600) | ~m1_subset_1(k3_tmap_1('#skF_1', B_600, '#skF_1', '#skF_4', E_601), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_600)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_600, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_601), '#skF_4', B_600) | ~v1_funct_2(k3_tmap_1('#skF_1', B_600, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_601), u1_struct_0('#skF_4'), u1_struct_0(B_600)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_600, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_601)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_600, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_601), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_600)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_600, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_601), '#skF_3', B_600) | ~v1_funct_2(k3_tmap_1('#skF_1', B_600, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_601), u1_struct_0('#skF_3'), u1_struct_0(B_600)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_600, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_601)) | ~m1_subset_1(E_601, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_600)))) | ~v1_funct_2(E_601, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_600)) | ~v1_funct_1(E_601) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_600) | ~v2_pre_topc(B_600) | v2_struct_0(B_600) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_52, c_2743])).
% 8.74/3.06  tff(c_2758, plain, (![E_601, B_600]: (v5_pre_topc(E_601, '#skF_1', B_600) | ~m1_subset_1(k3_tmap_1('#skF_1', B_600, '#skF_1', '#skF_4', E_601), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_600)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_600, '#skF_1', '#skF_4', E_601), '#skF_4', B_600) | ~v1_funct_2(k3_tmap_1('#skF_1', B_600, '#skF_1', '#skF_4', E_601), u1_struct_0('#skF_4'), u1_struct_0(B_600)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_600, '#skF_1', '#skF_4', E_601)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_600, '#skF_1', '#skF_3', E_601), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_600)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_600, '#skF_1', '#skF_3', E_601), '#skF_3', B_600) | ~v1_funct_2(k3_tmap_1('#skF_1', B_600, '#skF_1', '#skF_3', E_601), u1_struct_0('#skF_3'), u1_struct_0(B_600)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_600, '#skF_1', '#skF_3', E_601)) | ~m1_subset_1(E_601, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_600)))) | ~v1_funct_2(E_601, u1_struct_0('#skF_1'), u1_struct_0(B_600)) | ~v1_funct_1(E_601) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_600) | ~v2_pre_topc(B_600) | v2_struct_0(B_600) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_76, c_70, c_1483, c_52, c_52, c_52, c_52, c_52, c_52, c_52, c_52, c_52, c_52, c_2753])).
% 8.74/3.06  tff(c_4352, plain, (![E_870, B_871]: (v5_pre_topc(E_870, '#skF_1', B_871) | ~m1_subset_1(k3_tmap_1('#skF_1', B_871, '#skF_1', '#skF_4', E_870), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_871)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_871, '#skF_1', '#skF_4', E_870), '#skF_4', B_871) | ~v1_funct_2(k3_tmap_1('#skF_1', B_871, '#skF_1', '#skF_4', E_870), u1_struct_0('#skF_4'), u1_struct_0(B_871)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_871, '#skF_1', '#skF_4', E_870)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_871, '#skF_1', '#skF_3', E_870), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_871)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_871, '#skF_1', '#skF_3', E_870), '#skF_3', B_871) | ~v1_funct_2(k3_tmap_1('#skF_1', B_871, '#skF_1', '#skF_3', E_870), u1_struct_0('#skF_3'), u1_struct_0(B_871)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_871, '#skF_1', '#skF_3', E_870)) | ~m1_subset_1(E_870, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_871)))) | ~v1_funct_2(E_870, u1_struct_0('#skF_1'), u1_struct_0(B_871)) | ~v1_funct_1(E_870) | ~l1_pre_topc(B_871) | ~v2_pre_topc(B_871) | v2_struct_0(B_871))), inference(negUnitSimplification, [status(thm)], [c_92, c_80, c_74, c_2758])).
% 8.74/3.06  tff(c_4358, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1862, c_4352])).
% 8.74/3.06  tff(c_4365, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_245, c_1349, c_1028, c_68, c_1862, c_66, c_1862, c_64, c_1862, c_62, c_60, c_1689, c_58, c_1689, c_56, c_1689, c_54, c_1689, c_4358])).
% 8.74/3.06  tff(c_4367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_1348, c_4365])).
% 8.74/3.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.74/3.06  
% 8.74/3.06  Inference rules
% 8.74/3.06  ----------------------
% 8.74/3.06  #Ref     : 0
% 8.74/3.06  #Sup     : 724
% 8.74/3.06  #Fact    : 0
% 8.74/3.06  #Define  : 0
% 8.74/3.06  #Split   : 16
% 8.74/3.06  #Chain   : 0
% 8.74/3.06  #Close   : 0
% 8.74/3.06  
% 8.74/3.06  Ordering : KBO
% 8.74/3.06  
% 8.74/3.06  Simplification rules
% 8.74/3.06  ----------------------
% 8.74/3.06  #Subsume      : 106
% 8.74/3.06  #Demod        : 2115
% 8.74/3.06  #Tautology    : 49
% 8.74/3.06  #SimpNegUnit  : 452
% 8.74/3.06  #BackRed      : 6
% 8.74/3.06  
% 8.74/3.06  #Partial instantiations: 0
% 8.74/3.06  #Strategies tried      : 1
% 8.74/3.06  
% 8.74/3.06  Timing (in seconds)
% 8.74/3.06  ----------------------
% 8.74/3.06  Preprocessing        : 0.41
% 8.74/3.06  Parsing              : 0.21
% 8.74/3.06  CNF conversion       : 0.06
% 8.74/3.06  Main loop            : 1.81
% 8.74/3.06  Inferencing          : 0.58
% 8.74/3.06  Reduction            : 0.55
% 8.74/3.06  Demodulation         : 0.42
% 8.74/3.06  BG Simplification    : 0.06
% 8.74/3.06  Subsumption          : 0.54
% 8.74/3.06  Abstraction          : 0.08
% 8.74/3.06  MUC search           : 0.00
% 8.74/3.06  Cooper               : 0.00
% 8.74/3.06  Total                : 2.30
% 8.74/3.06  Index Insertion      : 0.00
% 8.74/3.06  Index Deletion       : 0.00
% 8.74/3.06  Index Matching       : 0.00
% 8.74/3.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
