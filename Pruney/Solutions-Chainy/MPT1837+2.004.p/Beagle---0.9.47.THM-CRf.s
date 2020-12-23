%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:14 EST 2020

% Result     : Theorem 8.27s
% Output     : CNFRefutation 8.37s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 943 expanded)
%              Number of leaves         :   31 ( 353 expanded)
%              Depth                    :   15
%              Number of atoms          :  714 (9900 expanded)
%              Number of equality atoms :   14 ( 445 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_243,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_tmap_1)).

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

tff(f_179,axiom,(
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

tff(f_175,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_tmap_1)).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_82,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_80,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_64,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_90,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_88,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_86,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_74,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_68,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_50,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_455,plain,(
    ! [C_255,F_253,A_256,B_254,E_257,D_252] :
      ( m1_subset_1(k10_tmap_1(A_256,B_254,C_255,D_252,E_257,F_253),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_256,C_255,D_252)),u1_struct_0(B_254))))
      | ~ m1_subset_1(F_253,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_252),u1_struct_0(B_254))))
      | ~ v1_funct_2(F_253,u1_struct_0(D_252),u1_struct_0(B_254))
      | ~ v1_funct_1(F_253)
      | ~ m1_subset_1(E_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_255),u1_struct_0(B_254))))
      | ~ v1_funct_2(E_257,u1_struct_0(C_255),u1_struct_0(B_254))
      | ~ v1_funct_1(E_257)
      | ~ m1_pre_topc(D_252,A_256)
      | v2_struct_0(D_252)
      | ~ m1_pre_topc(C_255,A_256)
      | v2_struct_0(C_255)
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc(A_256)
      | ~ v2_pre_topc(A_256)
      | v2_struct_0(A_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_484,plain,(
    ! [B_254,E_257,F_253] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_254,'#skF_3','#skF_4',E_257,F_253),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_254))))
      | ~ m1_subset_1(F_253,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_254))))
      | ~ v1_funct_2(F_253,u1_struct_0('#skF_4'),u1_struct_0(B_254))
      | ~ v1_funct_1(F_253)
      | ~ m1_subset_1(E_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_254))))
      | ~ v1_funct_2(E_257,u1_struct_0('#skF_3'),u1_struct_0(B_254))
      | ~ v1_funct_1(E_257)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_455])).

tff(c_504,plain,(
    ! [B_254,E_257,F_253] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_254,'#skF_3','#skF_4',E_257,F_253),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_254))))
      | ~ m1_subset_1(F_253,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_254))))
      | ~ v1_funct_2(F_253,u1_struct_0('#skF_4'),u1_struct_0(B_254))
      | ~ v1_funct_1(F_253)
      | ~ m1_subset_1(E_257,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_254))))
      | ~ v1_funct_2(E_257,u1_struct_0('#skF_3'),u1_struct_0(B_254))
      | ~ v1_funct_1(E_257)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_254)
      | ~ v2_pre_topc(B_254)
      | v2_struct_0(B_254)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_68,c_484])).

tff(c_506,plain,(
    ! [B_258,E_259,F_260] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_258,'#skF_3','#skF_4',E_259,F_260),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_258))))
      | ~ m1_subset_1(F_260,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_258))))
      | ~ v1_funct_2(F_260,u1_struct_0('#skF_4'),u1_struct_0(B_258))
      | ~ v1_funct_1(F_260)
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_258))))
      | ~ v1_funct_2(E_259,u1_struct_0('#skF_3'),u1_struct_0(B_258))
      | ~ v1_funct_1(E_259)
      | ~ l1_pre_topc(B_258)
      | ~ v2_pre_topc(B_258)
      | v2_struct_0(B_258) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_78,c_72,c_504])).

tff(c_173,plain,(
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

tff(c_177,plain,(
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
    inference(resolution,[status(thm)],[c_52,c_173])).

tff(c_183,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_58,c_56,c_177])).

tff(c_189,plain,(
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
    inference(negUnitSimplification,[status(thm)],[c_84,c_72,c_183])).

tff(c_196,plain,(
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
    inference(resolution,[status(thm)],[c_60,c_189])).

tff(c_207,plain,(
    ! [A_142] :
      ( v1_funct_1(k10_tmap_1(A_142,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_142)
      | ~ m1_pre_topc('#skF_3',A_142)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_142)
      | ~ v2_pre_topc(A_142)
      | v2_struct_0(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_196])).

tff(c_210,plain,(
    ! [A_146] :
      ( v1_funct_1(k10_tmap_1(A_146,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_146)
      | ~ m1_pre_topc('#skF_3',A_146)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_207])).

tff(c_44,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_145,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_213,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_210,c_145])).

tff(c_216,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_68,c_213])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_216])).

tff(c_219,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_223,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_533,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_506,c_223])).

tff(c_558,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_66,c_64,c_60,c_58,c_56,c_52,c_533])).

tff(c_560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_558])).

tff(c_561,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_574,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_561])).

tff(c_732,plain,(
    ! [B_307,D_305,F_306,C_308,E_310,A_309] :
      ( v1_funct_2(k10_tmap_1(A_309,B_307,C_308,D_305,E_310,F_306),u1_struct_0(k1_tsep_1(A_309,C_308,D_305)),u1_struct_0(B_307))
      | ~ m1_subset_1(F_306,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_305),u1_struct_0(B_307))))
      | ~ v1_funct_2(F_306,u1_struct_0(D_305),u1_struct_0(B_307))
      | ~ v1_funct_1(F_306)
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_308),u1_struct_0(B_307))))
      | ~ v1_funct_2(E_310,u1_struct_0(C_308),u1_struct_0(B_307))
      | ~ v1_funct_1(E_310)
      | ~ m1_pre_topc(D_305,A_309)
      | v2_struct_0(D_305)
      | ~ m1_pre_topc(C_308,A_309)
      | v2_struct_0(C_308)
      | ~ l1_pre_topc(B_307)
      | ~ v2_pre_topc(B_307)
      | v2_struct_0(B_307)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309)
      | v2_struct_0(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_735,plain,(
    ! [B_307,E_310,F_306] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_307,'#skF_3','#skF_4',E_310,F_306),u1_struct_0('#skF_1'),u1_struct_0(B_307))
      | ~ m1_subset_1(F_306,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_307))))
      | ~ v1_funct_2(F_306,u1_struct_0('#skF_4'),u1_struct_0(B_307))
      | ~ v1_funct_1(F_306)
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_307))))
      | ~ v1_funct_2(E_310,u1_struct_0('#skF_3'),u1_struct_0(B_307))
      | ~ v1_funct_1(E_310)
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
    inference(superposition,[status(thm),theory(equality)],[c_50,c_732])).

tff(c_737,plain,(
    ! [B_307,E_310,F_306] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_307,'#skF_3','#skF_4',E_310,F_306),u1_struct_0('#skF_1'),u1_struct_0(B_307))
      | ~ m1_subset_1(F_306,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_307))))
      | ~ v1_funct_2(F_306,u1_struct_0('#skF_4'),u1_struct_0(B_307))
      | ~ v1_funct_1(F_306)
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_307))))
      | ~ v1_funct_2(E_310,u1_struct_0('#skF_3'),u1_struct_0(B_307))
      | ~ v1_funct_1(E_310)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_307)
      | ~ v2_pre_topc(B_307)
      | v2_struct_0(B_307)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_68,c_735])).

tff(c_739,plain,(
    ! [B_311,E_312,F_313] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_311,'#skF_3','#skF_4',E_312,F_313),u1_struct_0('#skF_1'),u1_struct_0(B_311))
      | ~ m1_subset_1(F_313,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_311))))
      | ~ v1_funct_2(F_313,u1_struct_0('#skF_4'),u1_struct_0(B_311))
      | ~ v1_funct_1(F_313)
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_311))))
      | ~ v1_funct_2(E_312,u1_struct_0('#skF_3'),u1_struct_0(B_311))
      | ~ v1_funct_1(E_312)
      | ~ l1_pre_topc(B_311)
      | ~ v2_pre_topc(B_311)
      | v2_struct_0(B_311) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_78,c_72,c_737])).

tff(c_744,plain,(
    ! [E_312] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_312,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_312,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_312)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_739])).

tff(c_748,plain,(
    ! [E_312] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_312,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_312,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_312,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_312)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_58,c_56,c_744])).

tff(c_750,plain,(
    ! [E_314] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_314,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_314,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_314,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_314) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_748])).

tff(c_757,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_750])).

tff(c_764,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_757])).

tff(c_766,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_574,c_764])).

tff(c_767,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_220,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_768,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_561])).

tff(c_562,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_42,plain,(
    ! [A_47] :
      ( m1_pre_topc(A_47,A_47)
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_780,plain,(
    ! [A_318,C_317,D_320,B_319,E_321] :
      ( v1_funct_2(k3_tmap_1(A_318,B_319,C_317,D_320,E_321),u1_struct_0(D_320),u1_struct_0(B_319))
      | ~ m1_subset_1(E_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_317),u1_struct_0(B_319))))
      | ~ v1_funct_2(E_321,u1_struct_0(C_317),u1_struct_0(B_319))
      | ~ v1_funct_1(E_321)
      | ~ m1_pre_topc(D_320,A_318)
      | ~ m1_pre_topc(C_317,A_318)
      | ~ l1_pre_topc(B_319)
      | ~ v2_pre_topc(B_319)
      | v2_struct_0(B_319)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_782,plain,(
    ! [A_318,D_320] :
      ( v1_funct_2(k3_tmap_1(A_318,'#skF_2','#skF_1',D_320,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_320),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_320,A_318)
      | ~ m1_pre_topc('#skF_1',A_318)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(resolution,[status(thm)],[c_562,c_780])).

tff(c_789,plain,(
    ! [A_318,D_320] :
      ( v1_funct_2(k3_tmap_1(A_318,'#skF_2','#skF_1',D_320,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_320),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_320,A_318)
      | ~ m1_pre_topc('#skF_1',A_318)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_220,c_768,c_782])).

tff(c_790,plain,(
    ! [A_318,D_320] :
      ( v1_funct_2(k3_tmap_1(A_318,'#skF_2','#skF_1',D_320,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_320),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_320,A_318)
      | ~ m1_pre_topc('#skF_1',A_318)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_789])).

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

tff(c_564,plain,(
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
    inference(resolution,[status(thm)],[c_562,c_16])).

tff(c_569,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_1',D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_1',A_11)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_220,c_564])).

tff(c_570,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_1',D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_1',A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_569])).

tff(c_778,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_1',D_14,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_1',A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_768,c_570])).

tff(c_48,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_91,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48])).

tff(c_109,plain,(
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

tff(c_111,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_91,c_109])).

tff(c_120,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_111])).

tff(c_1071,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_1074,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_778,c_1071])).

tff(c_1077,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_1074])).

tff(c_1078,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1077])).

tff(c_1081,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1078])).

tff(c_1085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1081])).

tff(c_1086,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_1111,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1086])).

tff(c_1135,plain,
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
    inference(resolution,[status(thm)],[c_12,c_1111])).

tff(c_1138,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_74,c_220,c_768,c_562,c_1135])).

tff(c_1139,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_1138])).

tff(c_1142,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1139])).

tff(c_1146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1142])).

tff(c_1147,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1086])).

tff(c_1190,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1147])).

tff(c_1193,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_790,c_1190])).

tff(c_1196,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_1193])).

tff(c_1197,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1196])).

tff(c_1210,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1197])).

tff(c_1214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_1210])).

tff(c_1215,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1147])).

tff(c_62,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_46,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_92,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46])).

tff(c_113,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_92,c_109])).

tff(c_123,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_52,c_113])).

tff(c_802,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_805,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_778,c_802])).

tff(c_808,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_68,c_805])).

tff(c_809,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_808])).

tff(c_812,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_809])).

tff(c_816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_812])).

tff(c_818,plain,(
    v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_817,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_829,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_817])).

tff(c_854,plain,
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
    inference(resolution,[status(thm)],[c_12,c_829])).

tff(c_857,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_82,c_80,c_68,c_220,c_768,c_562,c_854])).

tff(c_858,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_84,c_857])).

tff(c_861,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_858])).

tff(c_865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_861])).

tff(c_867,plain,(
    m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_817])).

tff(c_871,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_4',D_14,k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_4',A_11)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_867,c_16])).

tff(c_880,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_4',D_14,k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_4',A_11)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_818,c_871])).

tff(c_881,plain,(
    ! [A_11,D_14] :
      ( v1_funct_1(k3_tmap_1(A_11,'#skF_2','#skF_4',D_14,k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))))
      | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_14,A_11)
      | ~ m1_pre_topc('#skF_4',A_11)
      | ~ l1_pre_topc(A_11)
      | ~ v2_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_880])).

tff(c_885,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_881])).

tff(c_888,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_790,c_885])).

tff(c_891,plain,
    ( ~ m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_68,c_888])).

tff(c_892,plain,(
    ~ m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_891])).

tff(c_895,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_892])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_895])).

tff(c_901,plain,(
    v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_881])).

tff(c_866,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_817])).

tff(c_903,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_866])).

tff(c_54,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_76,plain,(
    v1_tsep_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_70,plain,(
    v1_tsep_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_243])).

tff(c_2002,plain,(
    ! [C_488,D_487,A_489,B_485,E_486] :
      ( v5_pre_topc(E_486,k1_tsep_1(A_489,C_488,D_487),B_485)
      | ~ m1_subset_1(k3_tmap_1(A_489,B_485,k1_tsep_1(A_489,C_488,D_487),D_487,E_486),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_487),u1_struct_0(B_485))))
      | ~ v5_pre_topc(k3_tmap_1(A_489,B_485,k1_tsep_1(A_489,C_488,D_487),D_487,E_486),D_487,B_485)
      | ~ v1_funct_2(k3_tmap_1(A_489,B_485,k1_tsep_1(A_489,C_488,D_487),D_487,E_486),u1_struct_0(D_487),u1_struct_0(B_485))
      | ~ v1_funct_1(k3_tmap_1(A_489,B_485,k1_tsep_1(A_489,C_488,D_487),D_487,E_486))
      | ~ m1_subset_1(k3_tmap_1(A_489,B_485,k1_tsep_1(A_489,C_488,D_487),C_488,E_486),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_488),u1_struct_0(B_485))))
      | ~ v5_pre_topc(k3_tmap_1(A_489,B_485,k1_tsep_1(A_489,C_488,D_487),C_488,E_486),C_488,B_485)
      | ~ v1_funct_2(k3_tmap_1(A_489,B_485,k1_tsep_1(A_489,C_488,D_487),C_488,E_486),u1_struct_0(C_488),u1_struct_0(B_485))
      | ~ v1_funct_1(k3_tmap_1(A_489,B_485,k1_tsep_1(A_489,C_488,D_487),C_488,E_486))
      | ~ m1_subset_1(E_486,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_489,C_488,D_487)),u1_struct_0(B_485))))
      | ~ v1_funct_2(E_486,u1_struct_0(k1_tsep_1(A_489,C_488,D_487)),u1_struct_0(B_485))
      | ~ v1_funct_1(E_486)
      | ~ m1_pre_topc(D_487,A_489)
      | ~ v1_tsep_1(D_487,A_489)
      | v2_struct_0(D_487)
      | ~ m1_pre_topc(C_488,A_489)
      | ~ v1_tsep_1(C_488,A_489)
      | v2_struct_0(C_488)
      | ~ l1_pre_topc(B_485)
      | ~ v2_pre_topc(B_485)
      | v2_struct_0(B_485)
      | ~ l1_pre_topc(A_489)
      | ~ v2_pre_topc(A_489)
      | v2_struct_0(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_2012,plain,(
    ! [E_486,B_485] :
      ( v5_pre_topc(E_486,k1_tsep_1('#skF_1','#skF_3','#skF_4'),B_485)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_485,'#skF_1','#skF_4',E_486),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_485))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_485,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_486),'#skF_4',B_485)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_485,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_486),u1_struct_0('#skF_4'),u1_struct_0(B_485))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_485,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_486))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_485,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_486),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_485))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_485,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_486),'#skF_3',B_485)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_485,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_486),u1_struct_0('#skF_3'),u1_struct_0(B_485))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_485,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_486))
      | ~ m1_subset_1(E_486,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_485))))
      | ~ v1_funct_2(E_486,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_485))
      | ~ v1_funct_1(E_486)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_tsep_1('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ v1_tsep_1('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_485)
      | ~ v2_pre_topc(B_485)
      | v2_struct_0(B_485)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_2002])).

tff(c_2017,plain,(
    ! [E_486,B_485] :
      ( v5_pre_topc(E_486,'#skF_1',B_485)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_485,'#skF_1','#skF_4',E_486),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_485))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_485,'#skF_1','#skF_4',E_486),'#skF_4',B_485)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_485,'#skF_1','#skF_4',E_486),u1_struct_0('#skF_4'),u1_struct_0(B_485))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_485,'#skF_1','#skF_4',E_486))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_485,'#skF_1','#skF_3',E_486),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_485))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_485,'#skF_1','#skF_3',E_486),'#skF_3',B_485)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_485,'#skF_1','#skF_3',E_486),u1_struct_0('#skF_3'),u1_struct_0(B_485))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_485,'#skF_1','#skF_3',E_486))
      | ~ m1_subset_1(E_486,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_485))))
      | ~ v1_funct_2(E_486,u1_struct_0('#skF_1'),u1_struct_0(B_485))
      | ~ v1_funct_1(E_486)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_485)
      | ~ v2_pre_topc(B_485)
      | v2_struct_0(B_485)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_76,c_74,c_70,c_68,c_50,c_50,c_50,c_50,c_50,c_50,c_50,c_50,c_50,c_50,c_2012])).

tff(c_3321,plain,(
    ! [E_712,B_713] :
      ( v5_pre_topc(E_712,'#skF_1',B_713)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_713,'#skF_1','#skF_4',E_712),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_713))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_713,'#skF_1','#skF_4',E_712),'#skF_4',B_713)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_713,'#skF_1','#skF_4',E_712),u1_struct_0('#skF_4'),u1_struct_0(B_713))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_713,'#skF_1','#skF_4',E_712))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_713,'#skF_1','#skF_3',E_712),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_713))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_713,'#skF_1','#skF_3',E_712),'#skF_3',B_713)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_713,'#skF_1','#skF_3',E_712),u1_struct_0('#skF_3'),u1_struct_0(B_713))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_713,'#skF_1','#skF_3',E_712))
      | ~ m1_subset_1(E_712,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_713))))
      | ~ v1_funct_2(E_712,u1_struct_0('#skF_1'),u1_struct_0(B_713))
      | ~ v1_funct_1(E_712)
      | ~ l1_pre_topc(B_713)
      | ~ v2_pre_topc(B_713)
      | v2_struct_0(B_713) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_78,c_72,c_2017])).

tff(c_3327,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1215,c_3321])).

tff(c_3334,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_220,c_768,c_562,c_66,c_1215,c_64,c_1215,c_62,c_1215,c_60,c_58,c_903,c_56,c_903,c_54,c_903,c_52,c_903,c_3327])).

tff(c_3336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_767,c_3334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.27/2.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.37/2.76  
% 8.37/2.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.37/2.76  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.37/2.76  
% 8.37/2.76  %Foreground sorts:
% 8.37/2.76  
% 8.37/2.76  
% 8.37/2.76  %Background operators:
% 8.37/2.76  
% 8.37/2.76  
% 8.37/2.76  %Foreground operators:
% 8.37/2.76  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.37/2.76  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.37/2.76  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.37/2.76  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.37/2.76  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.37/2.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.37/2.76  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.37/2.76  tff('#skF_5', type, '#skF_5': $i).
% 8.37/2.76  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.37/2.76  tff('#skF_6', type, '#skF_6': $i).
% 8.37/2.76  tff('#skF_2', type, '#skF_2': $i).
% 8.37/2.76  tff('#skF_3', type, '#skF_3': $i).
% 8.37/2.76  tff('#skF_1', type, '#skF_1': $i).
% 8.37/2.76  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.37/2.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.37/2.76  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.37/2.76  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 8.37/2.76  tff('#skF_4', type, '#skF_4': $i).
% 8.37/2.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.37/2.76  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 8.37/2.76  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.37/2.76  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.37/2.76  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.37/2.76  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.37/2.76  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.37/2.76  
% 8.37/2.80  tff(f_243, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_tsep_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, A)) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((A = k1_tsep_1(A, C, D)) & r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E)) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_tmap_1)).
% 8.37/2.80  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 8.37/2.80  tff(f_179, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 8.37/2.80  tff(f_113, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 8.37/2.80  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 8.37/2.80  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_tsep_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, A)) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_tmap_1)).
% 8.37/2.80  tff(c_84, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_82, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_80, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_64, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_56, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_90, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_88, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_86, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_74, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_68, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_50, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_455, plain, (![C_255, F_253, A_256, B_254, E_257, D_252]: (m1_subset_1(k10_tmap_1(A_256, B_254, C_255, D_252, E_257, F_253), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_256, C_255, D_252)), u1_struct_0(B_254)))) | ~m1_subset_1(F_253, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_252), u1_struct_0(B_254)))) | ~v1_funct_2(F_253, u1_struct_0(D_252), u1_struct_0(B_254)) | ~v1_funct_1(F_253) | ~m1_subset_1(E_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_255), u1_struct_0(B_254)))) | ~v1_funct_2(E_257, u1_struct_0(C_255), u1_struct_0(B_254)) | ~v1_funct_1(E_257) | ~m1_pre_topc(D_252, A_256) | v2_struct_0(D_252) | ~m1_pre_topc(C_255, A_256) | v2_struct_0(C_255) | ~l1_pre_topc(B_254) | ~v2_pre_topc(B_254) | v2_struct_0(B_254) | ~l1_pre_topc(A_256) | ~v2_pre_topc(A_256) | v2_struct_0(A_256))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.37/2.80  tff(c_484, plain, (![B_254, E_257, F_253]: (m1_subset_1(k10_tmap_1('#skF_1', B_254, '#skF_3', '#skF_4', E_257, F_253), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_254)))) | ~m1_subset_1(F_253, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_254)))) | ~v1_funct_2(F_253, u1_struct_0('#skF_4'), u1_struct_0(B_254)) | ~v1_funct_1(F_253) | ~m1_subset_1(E_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_254)))) | ~v1_funct_2(E_257, u1_struct_0('#skF_3'), u1_struct_0(B_254)) | ~v1_funct_1(E_257) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_254) | ~v2_pre_topc(B_254) | v2_struct_0(B_254) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_455])).
% 8.37/2.80  tff(c_504, plain, (![B_254, E_257, F_253]: (m1_subset_1(k10_tmap_1('#skF_1', B_254, '#skF_3', '#skF_4', E_257, F_253), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_254)))) | ~m1_subset_1(F_253, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_254)))) | ~v1_funct_2(F_253, u1_struct_0('#skF_4'), u1_struct_0(B_254)) | ~v1_funct_1(F_253) | ~m1_subset_1(E_257, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_254)))) | ~v1_funct_2(E_257, u1_struct_0('#skF_3'), u1_struct_0(B_254)) | ~v1_funct_1(E_257) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_254) | ~v2_pre_topc(B_254) | v2_struct_0(B_254) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_68, c_484])).
% 8.37/2.80  tff(c_506, plain, (![B_258, E_259, F_260]: (m1_subset_1(k10_tmap_1('#skF_1', B_258, '#skF_3', '#skF_4', E_259, F_260), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_258)))) | ~m1_subset_1(F_260, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_258)))) | ~v1_funct_2(F_260, u1_struct_0('#skF_4'), u1_struct_0(B_258)) | ~v1_funct_1(F_260) | ~m1_subset_1(E_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_258)))) | ~v1_funct_2(E_259, u1_struct_0('#skF_3'), u1_struct_0(B_258)) | ~v1_funct_1(E_259) | ~l1_pre_topc(B_258) | ~v2_pre_topc(B_258) | v2_struct_0(B_258))), inference(negUnitSimplification, [status(thm)], [c_90, c_78, c_72, c_504])).
% 8.37/2.80  tff(c_173, plain, (![D_136, B_138, E_141, F_137, C_139, A_140]: (v1_funct_1(k10_tmap_1(A_140, B_138, C_139, D_136, E_141, F_137)) | ~m1_subset_1(F_137, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_136), u1_struct_0(B_138)))) | ~v1_funct_2(F_137, u1_struct_0(D_136), u1_struct_0(B_138)) | ~v1_funct_1(F_137) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139), u1_struct_0(B_138)))) | ~v1_funct_2(E_141, u1_struct_0(C_139), u1_struct_0(B_138)) | ~v1_funct_1(E_141) | ~m1_pre_topc(D_136, A_140) | v2_struct_0(D_136) | ~m1_pre_topc(C_139, A_140) | v2_struct_0(C_139) | ~l1_pre_topc(B_138) | ~v2_pre_topc(B_138) | v2_struct_0(B_138) | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.37/2.80  tff(c_177, plain, (![A_140, C_139, E_141]: (v1_funct_1(k10_tmap_1(A_140, '#skF_2', C_139, '#skF_4', E_141, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_141, u1_struct_0(C_139), u1_struct_0('#skF_2')) | ~v1_funct_1(E_141) | ~m1_pre_topc('#skF_4', A_140) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_139, A_140) | v2_struct_0(C_139) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(resolution, [status(thm)], [c_52, c_173])).
% 8.37/2.80  tff(c_183, plain, (![A_140, C_139, E_141]: (v1_funct_1(k10_tmap_1(A_140, '#skF_2', C_139, '#skF_4', E_141, '#skF_6')) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_139), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_141, u1_struct_0(C_139), u1_struct_0('#skF_2')) | ~v1_funct_1(E_141) | ~m1_pre_topc('#skF_4', A_140) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_139, A_140) | v2_struct_0(C_139) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_140) | ~v2_pre_topc(A_140) | v2_struct_0(A_140))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_58, c_56, c_177])).
% 8.37/2.80  tff(c_189, plain, (![A_142, C_143, E_144]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', C_143, '#skF_4', E_144, '#skF_6')) | ~m1_subset_1(E_144, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_143), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_144, u1_struct_0(C_143), u1_struct_0('#skF_2')) | ~v1_funct_1(E_144) | ~m1_pre_topc('#skF_4', A_142) | ~m1_pre_topc(C_143, A_142) | v2_struct_0(C_143) | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(negUnitSimplification, [status(thm)], [c_84, c_72, c_183])).
% 8.37/2.80  tff(c_196, plain, (![A_142]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_142) | ~m1_pre_topc('#skF_3', A_142) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(resolution, [status(thm)], [c_60, c_189])).
% 8.37/2.80  tff(c_207, plain, (![A_142]: (v1_funct_1(k10_tmap_1(A_142, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_142) | ~m1_pre_topc('#skF_3', A_142) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_142) | ~v2_pre_topc(A_142) | v2_struct_0(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_196])).
% 8.37/2.80  tff(c_210, plain, (![A_146]: (v1_funct_1(k10_tmap_1(A_146, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_146) | ~m1_pre_topc('#skF_3', A_146) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(negUnitSimplification, [status(thm)], [c_78, c_207])).
% 8.37/2.80  tff(c_44, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_145, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_44])).
% 8.37/2.80  tff(c_213, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_210, c_145])).
% 8.37/2.80  tff(c_216, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_68, c_213])).
% 8.37/2.80  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_216])).
% 8.37/2.80  tff(c_219, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_44])).
% 8.37/2.80  tff(c_223, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_219])).
% 8.37/2.80  tff(c_533, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_506, c_223])).
% 8.37/2.80  tff(c_558, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_66, c_64, c_60, c_58, c_56, c_52, c_533])).
% 8.37/2.80  tff(c_560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_558])).
% 8.37/2.80  tff(c_561, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_219])).
% 8.37/2.80  tff(c_574, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_561])).
% 8.37/2.80  tff(c_732, plain, (![B_307, D_305, F_306, C_308, E_310, A_309]: (v1_funct_2(k10_tmap_1(A_309, B_307, C_308, D_305, E_310, F_306), u1_struct_0(k1_tsep_1(A_309, C_308, D_305)), u1_struct_0(B_307)) | ~m1_subset_1(F_306, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_305), u1_struct_0(B_307)))) | ~v1_funct_2(F_306, u1_struct_0(D_305), u1_struct_0(B_307)) | ~v1_funct_1(F_306) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_308), u1_struct_0(B_307)))) | ~v1_funct_2(E_310, u1_struct_0(C_308), u1_struct_0(B_307)) | ~v1_funct_1(E_310) | ~m1_pre_topc(D_305, A_309) | v2_struct_0(D_305) | ~m1_pre_topc(C_308, A_309) | v2_struct_0(C_308) | ~l1_pre_topc(B_307) | ~v2_pre_topc(B_307) | v2_struct_0(B_307) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309) | v2_struct_0(A_309))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.37/2.80  tff(c_735, plain, (![B_307, E_310, F_306]: (v1_funct_2(k10_tmap_1('#skF_1', B_307, '#skF_3', '#skF_4', E_310, F_306), u1_struct_0('#skF_1'), u1_struct_0(B_307)) | ~m1_subset_1(F_306, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_307)))) | ~v1_funct_2(F_306, u1_struct_0('#skF_4'), u1_struct_0(B_307)) | ~v1_funct_1(F_306) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_307)))) | ~v1_funct_2(E_310, u1_struct_0('#skF_3'), u1_struct_0(B_307)) | ~v1_funct_1(E_310) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_307) | ~v2_pre_topc(B_307) | v2_struct_0(B_307) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_732])).
% 8.37/2.80  tff(c_737, plain, (![B_307, E_310, F_306]: (v1_funct_2(k10_tmap_1('#skF_1', B_307, '#skF_3', '#skF_4', E_310, F_306), u1_struct_0('#skF_1'), u1_struct_0(B_307)) | ~m1_subset_1(F_306, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_307)))) | ~v1_funct_2(F_306, u1_struct_0('#skF_4'), u1_struct_0(B_307)) | ~v1_funct_1(F_306) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_307)))) | ~v1_funct_2(E_310, u1_struct_0('#skF_3'), u1_struct_0(B_307)) | ~v1_funct_1(E_310) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_307) | ~v2_pre_topc(B_307) | v2_struct_0(B_307) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_68, c_735])).
% 8.37/2.80  tff(c_739, plain, (![B_311, E_312, F_313]: (v1_funct_2(k10_tmap_1('#skF_1', B_311, '#skF_3', '#skF_4', E_312, F_313), u1_struct_0('#skF_1'), u1_struct_0(B_311)) | ~m1_subset_1(F_313, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_311)))) | ~v1_funct_2(F_313, u1_struct_0('#skF_4'), u1_struct_0(B_311)) | ~v1_funct_1(F_313) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_311)))) | ~v1_funct_2(E_312, u1_struct_0('#skF_3'), u1_struct_0(B_311)) | ~v1_funct_1(E_312) | ~l1_pre_topc(B_311) | ~v2_pre_topc(B_311) | v2_struct_0(B_311))), inference(negUnitSimplification, [status(thm)], [c_90, c_78, c_72, c_737])).
% 8.37/2.80  tff(c_744, plain, (![E_312]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_312, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_312, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_312) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_739])).
% 8.37/2.80  tff(c_748, plain, (![E_312]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_312, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_312, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_312, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_312) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_58, c_56, c_744])).
% 8.37/2.80  tff(c_750, plain, (![E_314]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_314, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_314, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_314, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_314))), inference(negUnitSimplification, [status(thm)], [c_84, c_748])).
% 8.37/2.80  tff(c_757, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_750])).
% 8.37/2.80  tff(c_764, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_757])).
% 8.37/2.80  tff(c_766, plain, $false, inference(negUnitSimplification, [status(thm)], [c_574, c_764])).
% 8.37/2.80  tff(c_767, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_561])).
% 8.37/2.80  tff(c_220, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_44])).
% 8.37/2.80  tff(c_768, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_561])).
% 8.37/2.80  tff(c_562, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_219])).
% 8.37/2.80  tff(c_42, plain, (![A_47]: (m1_pre_topc(A_47, A_47) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_179])).
% 8.37/2.80  tff(c_780, plain, (![A_318, C_317, D_320, B_319, E_321]: (v1_funct_2(k3_tmap_1(A_318, B_319, C_317, D_320, E_321), u1_struct_0(D_320), u1_struct_0(B_319)) | ~m1_subset_1(E_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_317), u1_struct_0(B_319)))) | ~v1_funct_2(E_321, u1_struct_0(C_317), u1_struct_0(B_319)) | ~v1_funct_1(E_321) | ~m1_pre_topc(D_320, A_318) | ~m1_pre_topc(C_317, A_318) | ~l1_pre_topc(B_319) | ~v2_pre_topc(B_319) | v2_struct_0(B_319) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.37/2.80  tff(c_782, plain, (![A_318, D_320]: (v1_funct_2(k3_tmap_1(A_318, '#skF_2', '#skF_1', D_320, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_320), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_320, A_318) | ~m1_pre_topc('#skF_1', A_318) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(resolution, [status(thm)], [c_562, c_780])).
% 8.37/2.80  tff(c_789, plain, (![A_318, D_320]: (v1_funct_2(k3_tmap_1(A_318, '#skF_2', '#skF_1', D_320, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_320), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_320, A_318) | ~m1_pre_topc('#skF_1', A_318) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_220, c_768, c_782])).
% 8.37/2.80  tff(c_790, plain, (![A_318, D_320]: (v1_funct_2(k3_tmap_1(A_318, '#skF_2', '#skF_1', D_320, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_320), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_320, A_318) | ~m1_pre_topc('#skF_1', A_318) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(negUnitSimplification, [status(thm)], [c_84, c_789])).
% 8.37/2.80  tff(c_12, plain, (![D_14, E_15, B_12, A_11, C_13]: (m1_subset_1(k3_tmap_1(A_11, B_12, C_13, D_14, E_15), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_14), u1_struct_0(B_12)))) | ~m1_subset_1(E_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13), u1_struct_0(B_12)))) | ~v1_funct_2(E_15, u1_struct_0(C_13), u1_struct_0(B_12)) | ~v1_funct_1(E_15) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(C_13, A_11) | ~l1_pre_topc(B_12) | ~v2_pre_topc(B_12) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.37/2.80  tff(c_16, plain, (![D_14, E_15, B_12, A_11, C_13]: (v1_funct_1(k3_tmap_1(A_11, B_12, C_13, D_14, E_15)) | ~m1_subset_1(E_15, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_13), u1_struct_0(B_12)))) | ~v1_funct_2(E_15, u1_struct_0(C_13), u1_struct_0(B_12)) | ~v1_funct_1(E_15) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc(C_13, A_11) | ~l1_pre_topc(B_12) | ~v2_pre_topc(B_12) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_113])).
% 8.37/2.80  tff(c_564, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_1', D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_1', A_11) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(resolution, [status(thm)], [c_562, c_16])).
% 8.37/2.80  tff(c_569, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_1', D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_1', A_11) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_220, c_564])).
% 8.37/2.80  tff(c_570, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_1', D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_1', A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(negUnitSimplification, [status(thm)], [c_84, c_569])).
% 8.37/2.80  tff(c_778, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_1', D_14, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_1', A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_768, c_570])).
% 8.37/2.80  tff(c_48, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_91, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48])).
% 8.37/2.80  tff(c_109, plain, (![D_109, C_110, A_111, B_112]: (D_109=C_110 | ~r2_funct_2(A_111, B_112, C_110, D_109) | ~m1_subset_1(D_109, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(D_109, A_111, B_112) | ~v1_funct_1(D_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(C_110, A_111, B_112) | ~v1_funct_1(C_110))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.37/2.80  tff(c_111, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_91, c_109])).
% 8.37/2.80  tff(c_120, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_111])).
% 8.37/2.80  tff(c_1071, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_120])).
% 8.37/2.80  tff(c_1074, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_778, c_1071])).
% 8.37/2.80  tff(c_1077, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_1074])).
% 8.37/2.80  tff(c_1078, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_90, c_1077])).
% 8.37/2.80  tff(c_1081, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1078])).
% 8.37/2.80  tff(c_1085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1081])).
% 8.37/2.80  tff(c_1086, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_120])).
% 8.37/2.80  tff(c_1111, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1086])).
% 8.37/2.80  tff(c_1135, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1111])).
% 8.37/2.80  tff(c_1138, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_80, c_74, c_220, c_768, c_562, c_1135])).
% 8.37/2.80  tff(c_1139, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_1138])).
% 8.37/2.80  tff(c_1142, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1139])).
% 8.37/2.80  tff(c_1146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1142])).
% 8.37/2.80  tff(c_1147, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1086])).
% 8.37/2.80  tff(c_1190, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1147])).
% 8.37/2.80  tff(c_1193, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_790, c_1190])).
% 8.37/2.80  tff(c_1196, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_1193])).
% 8.37/2.80  tff(c_1197, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_90, c_1196])).
% 8.37/2.80  tff(c_1210, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_1197])).
% 8.37/2.80  tff(c_1214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_1210])).
% 8.37/2.80  tff(c_1215, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1147])).
% 8.37/2.80  tff(c_62, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_46, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_92, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46])).
% 8.37/2.80  tff(c_113, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_92, c_109])).
% 8.37/2.80  tff(c_123, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_52, c_113])).
% 8.37/2.80  tff(c_802, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_123])).
% 8.37/2.80  tff(c_805, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_778, c_802])).
% 8.37/2.80  tff(c_808, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_68, c_805])).
% 8.37/2.80  tff(c_809, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_90, c_808])).
% 8.37/2.80  tff(c_812, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_809])).
% 8.37/2.80  tff(c_816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_812])).
% 8.37/2.80  tff(c_818, plain, (v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_123])).
% 8.37/2.80  tff(c_817, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_123])).
% 8.37/2.80  tff(c_829, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_817])).
% 8.37/2.80  tff(c_854, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_829])).
% 8.37/2.80  tff(c_857, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_82, c_80, c_68, c_220, c_768, c_562, c_854])).
% 8.37/2.80  tff(c_858, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_90, c_84, c_857])).
% 8.37/2.80  tff(c_861, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_858])).
% 8.37/2.80  tff(c_865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_861])).
% 8.37/2.80  tff(c_867, plain, (m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_817])).
% 8.37/2.80  tff(c_871, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_4', D_14, k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_4', A_11) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(resolution, [status(thm)], [c_867, c_16])).
% 8.37/2.80  tff(c_880, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_4', D_14, k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_4', A_11) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_818, c_871])).
% 8.37/2.80  tff(c_881, plain, (![A_11, D_14]: (v1_funct_1(k3_tmap_1(A_11, '#skF_2', '#skF_4', D_14, k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_14, A_11) | ~m1_pre_topc('#skF_4', A_11) | ~l1_pre_topc(A_11) | ~v2_pre_topc(A_11) | v2_struct_0(A_11))), inference(negUnitSimplification, [status(thm)], [c_84, c_880])).
% 8.37/2.80  tff(c_885, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_881])).
% 8.37/2.80  tff(c_888, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_790, c_885])).
% 8.37/2.80  tff(c_891, plain, (~m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_68, c_888])).
% 8.37/2.80  tff(c_892, plain, (~m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_90, c_891])).
% 8.37/2.80  tff(c_895, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_892])).
% 8.37/2.80  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_86, c_895])).
% 8.37/2.80  tff(c_901, plain, (v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_881])).
% 8.37/2.80  tff(c_866, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_817])).
% 8.37/2.80  tff(c_903, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_901, c_866])).
% 8.37/2.80  tff(c_54, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_76, plain, (v1_tsep_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_70, plain, (v1_tsep_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_243])).
% 8.37/2.80  tff(c_2002, plain, (![C_488, D_487, A_489, B_485, E_486]: (v5_pre_topc(E_486, k1_tsep_1(A_489, C_488, D_487), B_485) | ~m1_subset_1(k3_tmap_1(A_489, B_485, k1_tsep_1(A_489, C_488, D_487), D_487, E_486), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_487), u1_struct_0(B_485)))) | ~v5_pre_topc(k3_tmap_1(A_489, B_485, k1_tsep_1(A_489, C_488, D_487), D_487, E_486), D_487, B_485) | ~v1_funct_2(k3_tmap_1(A_489, B_485, k1_tsep_1(A_489, C_488, D_487), D_487, E_486), u1_struct_0(D_487), u1_struct_0(B_485)) | ~v1_funct_1(k3_tmap_1(A_489, B_485, k1_tsep_1(A_489, C_488, D_487), D_487, E_486)) | ~m1_subset_1(k3_tmap_1(A_489, B_485, k1_tsep_1(A_489, C_488, D_487), C_488, E_486), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_488), u1_struct_0(B_485)))) | ~v5_pre_topc(k3_tmap_1(A_489, B_485, k1_tsep_1(A_489, C_488, D_487), C_488, E_486), C_488, B_485) | ~v1_funct_2(k3_tmap_1(A_489, B_485, k1_tsep_1(A_489, C_488, D_487), C_488, E_486), u1_struct_0(C_488), u1_struct_0(B_485)) | ~v1_funct_1(k3_tmap_1(A_489, B_485, k1_tsep_1(A_489, C_488, D_487), C_488, E_486)) | ~m1_subset_1(E_486, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_489, C_488, D_487)), u1_struct_0(B_485)))) | ~v1_funct_2(E_486, u1_struct_0(k1_tsep_1(A_489, C_488, D_487)), u1_struct_0(B_485)) | ~v1_funct_1(E_486) | ~m1_pre_topc(D_487, A_489) | ~v1_tsep_1(D_487, A_489) | v2_struct_0(D_487) | ~m1_pre_topc(C_488, A_489) | ~v1_tsep_1(C_488, A_489) | v2_struct_0(C_488) | ~l1_pre_topc(B_485) | ~v2_pre_topc(B_485) | v2_struct_0(B_485) | ~l1_pre_topc(A_489) | ~v2_pre_topc(A_489) | v2_struct_0(A_489))), inference(cnfTransformation, [status(thm)], [f_175])).
% 8.37/2.80  tff(c_2012, plain, (![E_486, B_485]: (v5_pre_topc(E_486, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), B_485) | ~m1_subset_1(k3_tmap_1('#skF_1', B_485, '#skF_1', '#skF_4', E_486), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_485)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_485, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_486), '#skF_4', B_485) | ~v1_funct_2(k3_tmap_1('#skF_1', B_485, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_486), u1_struct_0('#skF_4'), u1_struct_0(B_485)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_485, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_486)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_485, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_486), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_485)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_485, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_486), '#skF_3', B_485) | ~v1_funct_2(k3_tmap_1('#skF_1', B_485, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_486), u1_struct_0('#skF_3'), u1_struct_0(B_485)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_485, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_486)) | ~m1_subset_1(E_486, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_485)))) | ~v1_funct_2(E_486, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_485)) | ~v1_funct_1(E_486) | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_tsep_1('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_tsep_1('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_485) | ~v2_pre_topc(B_485) | v2_struct_0(B_485) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_2002])).
% 8.37/2.80  tff(c_2017, plain, (![E_486, B_485]: (v5_pre_topc(E_486, '#skF_1', B_485) | ~m1_subset_1(k3_tmap_1('#skF_1', B_485, '#skF_1', '#skF_4', E_486), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_485)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_485, '#skF_1', '#skF_4', E_486), '#skF_4', B_485) | ~v1_funct_2(k3_tmap_1('#skF_1', B_485, '#skF_1', '#skF_4', E_486), u1_struct_0('#skF_4'), u1_struct_0(B_485)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_485, '#skF_1', '#skF_4', E_486)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_485, '#skF_1', '#skF_3', E_486), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_485)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_485, '#skF_1', '#skF_3', E_486), '#skF_3', B_485) | ~v1_funct_2(k3_tmap_1('#skF_1', B_485, '#skF_1', '#skF_3', E_486), u1_struct_0('#skF_3'), u1_struct_0(B_485)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_485, '#skF_1', '#skF_3', E_486)) | ~m1_subset_1(E_486, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_485)))) | ~v1_funct_2(E_486, u1_struct_0('#skF_1'), u1_struct_0(B_485)) | ~v1_funct_1(E_486) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_485) | ~v2_pre_topc(B_485) | v2_struct_0(B_485) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_76, c_74, c_70, c_68, c_50, c_50, c_50, c_50, c_50, c_50, c_50, c_50, c_50, c_50, c_2012])).
% 8.37/2.80  tff(c_3321, plain, (![E_712, B_713]: (v5_pre_topc(E_712, '#skF_1', B_713) | ~m1_subset_1(k3_tmap_1('#skF_1', B_713, '#skF_1', '#skF_4', E_712), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_713)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_713, '#skF_1', '#skF_4', E_712), '#skF_4', B_713) | ~v1_funct_2(k3_tmap_1('#skF_1', B_713, '#skF_1', '#skF_4', E_712), u1_struct_0('#skF_4'), u1_struct_0(B_713)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_713, '#skF_1', '#skF_4', E_712)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_713, '#skF_1', '#skF_3', E_712), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_713)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_713, '#skF_1', '#skF_3', E_712), '#skF_3', B_713) | ~v1_funct_2(k3_tmap_1('#skF_1', B_713, '#skF_1', '#skF_3', E_712), u1_struct_0('#skF_3'), u1_struct_0(B_713)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_713, '#skF_1', '#skF_3', E_712)) | ~m1_subset_1(E_712, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_713)))) | ~v1_funct_2(E_712, u1_struct_0('#skF_1'), u1_struct_0(B_713)) | ~v1_funct_1(E_712) | ~l1_pre_topc(B_713) | ~v2_pre_topc(B_713) | v2_struct_0(B_713))), inference(negUnitSimplification, [status(thm)], [c_90, c_78, c_72, c_2017])).
% 8.37/2.80  tff(c_3327, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1215, c_3321])).
% 8.37/2.80  tff(c_3334, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_220, c_768, c_562, c_66, c_1215, c_64, c_1215, c_62, c_1215, c_60, c_58, c_903, c_56, c_903, c_54, c_903, c_52, c_903, c_3327])).
% 8.37/2.80  tff(c_3336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_767, c_3334])).
% 8.37/2.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.37/2.80  
% 8.37/2.80  Inference rules
% 8.37/2.80  ----------------------
% 8.37/2.80  #Ref     : 0
% 8.37/2.80  #Sup     : 554
% 8.37/2.80  #Fact    : 0
% 8.37/2.80  #Define  : 0
% 8.37/2.80  #Split   : 13
% 8.37/2.80  #Chain   : 0
% 8.37/2.80  #Close   : 0
% 8.37/2.80  
% 8.37/2.80  Ordering : KBO
% 8.37/2.80  
% 8.37/2.80  Simplification rules
% 8.37/2.80  ----------------------
% 8.37/2.80  #Subsume      : 87
% 8.37/2.80  #Demod        : 1719
% 8.37/2.80  #Tautology    : 45
% 8.37/2.80  #SimpNegUnit  : 339
% 8.37/2.80  #BackRed      : 7
% 8.37/2.80  
% 8.37/2.80  #Partial instantiations: 0
% 8.37/2.80  #Strategies tried      : 1
% 8.37/2.80  
% 8.37/2.80  Timing (in seconds)
% 8.37/2.80  ----------------------
% 8.37/2.80  Preprocessing        : 0.40
% 8.37/2.80  Parsing              : 0.19
% 8.37/2.80  CNF conversion       : 0.06
% 8.37/2.80  Main loop            : 1.54
% 8.37/2.80  Inferencing          : 0.50
% 8.37/2.80  Reduction            : 0.47
% 8.37/2.80  Demodulation         : 0.36
% 8.37/2.80  BG Simplification    : 0.06
% 8.37/2.80  Subsumption          : 0.44
% 8.37/2.80  Abstraction          : 0.06
% 8.37/2.80  MUC search           : 0.00
% 8.37/2.80  Cooper               : 0.00
% 8.37/2.80  Total                : 2.01
% 8.37/2.80  Index Insertion      : 0.00
% 8.37/2.80  Index Deletion       : 0.00
% 8.37/2.80  Index Matching       : 0.00
% 8.37/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
