%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:12 EST 2020

% Result     : Theorem 8.31s
% Output     : CNFRefutation 8.59s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 811 expanded)
%              Number of leaves         :   32 ( 315 expanded)
%              Depth                    :   10
%              Number of atoms          :  714 (8512 expanded)
%              Number of equality atoms :   14 ( 378 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_257,negated_conjecture,(
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

tff(c_86,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_84,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_82,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_68,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_60,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_92,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_90,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_88,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_78,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_74,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_72,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_505,plain,(
    ! [D_257,B_259,E_262,F_258,A_261,C_260] :
      ( m1_subset_1(k10_tmap_1(A_261,B_259,C_260,D_257,E_262,F_258),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_261,C_260,D_257)),u1_struct_0(B_259))))
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_257),u1_struct_0(B_259))))
      | ~ v1_funct_2(F_258,u1_struct_0(D_257),u1_struct_0(B_259))
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_260),u1_struct_0(B_259))))
      | ~ v1_funct_2(E_262,u1_struct_0(C_260),u1_struct_0(B_259))
      | ~ v1_funct_1(E_262)
      | ~ m1_pre_topc(D_257,A_261)
      | v2_struct_0(D_257)
      | ~ m1_pre_topc(C_260,A_261)
      | v2_struct_0(C_260)
      | ~ l1_pre_topc(B_259)
      | ~ v2_pre_topc(B_259)
      | v2_struct_0(B_259)
      | ~ l1_pre_topc(A_261)
      | ~ v2_pre_topc(A_261)
      | v2_struct_0(A_261) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_534,plain,(
    ! [B_259,E_262,F_258] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_259,'#skF_3','#skF_4',E_262,F_258),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_259))))
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_259))))
      | ~ v1_funct_2(F_258,u1_struct_0('#skF_4'),u1_struct_0(B_259))
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_259))))
      | ~ v1_funct_2(E_262,u1_struct_0('#skF_3'),u1_struct_0(B_259))
      | ~ v1_funct_1(E_262)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_259)
      | ~ v2_pre_topc(B_259)
      | v2_struct_0(B_259)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_505])).

tff(c_554,plain,(
    ! [B_259,E_262,F_258] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_259,'#skF_3','#skF_4',E_262,F_258),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_259))))
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_259))))
      | ~ v1_funct_2(F_258,u1_struct_0('#skF_4'),u1_struct_0(B_259))
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(E_262,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_259))))
      | ~ v1_funct_2(E_262,u1_struct_0('#skF_3'),u1_struct_0(B_259))
      | ~ v1_funct_1(E_262)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_259)
      | ~ v2_pre_topc(B_259)
      | v2_struct_0(B_259)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_534])).

tff(c_556,plain,(
    ! [B_263,E_264,F_265] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_263,'#skF_3','#skF_4',E_264,F_265),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_263))))
      | ~ m1_subset_1(F_265,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_263))))
      | ~ v1_funct_2(F_265,u1_struct_0('#skF_4'),u1_struct_0(B_263))
      | ~ v1_funct_1(F_265)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_263))))
      | ~ v1_funct_2(E_264,u1_struct_0('#skF_3'),u1_struct_0(B_263))
      | ~ v1_funct_1(E_264)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_76,c_554])).

tff(c_196,plain,(
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

tff(c_200,plain,(
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
    inference(resolution,[status(thm)],[c_56,c_196])).

tff(c_206,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_62,c_60,c_200])).

tff(c_212,plain,(
    ! [A_152,C_153,E_154] :
      ( v1_funct_1(k10_tmap_1(A_152,'#skF_2',C_153,'#skF_4',E_154,'#skF_6'))
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_153),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_154,u1_struct_0(C_153),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_154)
      | ~ m1_pre_topc('#skF_4',A_152)
      | ~ m1_pre_topc(C_153,A_152)
      | v2_struct_0(C_153)
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_76,c_206])).

tff(c_219,plain,(
    ! [A_152] :
      ( v1_funct_1(k10_tmap_1(A_152,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_152)
      | ~ m1_pre_topc('#skF_3',A_152)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_64,c_212])).

tff(c_230,plain,(
    ! [A_152] :
      ( v1_funct_1(k10_tmap_1(A_152,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_152)
      | ~ m1_pre_topc('#skF_3',A_152)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_152)
      | ~ v2_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_219])).

tff(c_243,plain,(
    ! [A_161] :
      ( v1_funct_1(k10_tmap_1(A_161,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_161)
      | ~ m1_pre_topc('#skF_3',A_161)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_230])).

tff(c_48,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_131,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_246,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_243,c_131])).

tff(c_249,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_246])).

tff(c_251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_249])).

tff(c_252,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_254,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_585,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_556,c_254])).

tff(c_609,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_68,c_64,c_62,c_60,c_56,c_585])).

tff(c_611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_609])).

tff(c_612,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_619,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_612])).

tff(c_876,plain,(
    ! [B_350,E_353,A_352,D_348,C_351,F_349] :
      ( v1_funct_2(k10_tmap_1(A_352,B_350,C_351,D_348,E_353,F_349),u1_struct_0(k1_tsep_1(A_352,C_351,D_348)),u1_struct_0(B_350))
      | ~ m1_subset_1(F_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_348),u1_struct_0(B_350))))
      | ~ v1_funct_2(F_349,u1_struct_0(D_348),u1_struct_0(B_350))
      | ~ v1_funct_1(F_349)
      | ~ m1_subset_1(E_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_351),u1_struct_0(B_350))))
      | ~ v1_funct_2(E_353,u1_struct_0(C_351),u1_struct_0(B_350))
      | ~ v1_funct_1(E_353)
      | ~ m1_pre_topc(D_348,A_352)
      | v2_struct_0(D_348)
      | ~ m1_pre_topc(C_351,A_352)
      | v2_struct_0(C_351)
      | ~ l1_pre_topc(B_350)
      | ~ v2_pre_topc(B_350)
      | v2_struct_0(B_350)
      | ~ l1_pre_topc(A_352)
      | ~ v2_pre_topc(A_352)
      | v2_struct_0(A_352) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_879,plain,(
    ! [B_350,E_353,F_349] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_350,'#skF_3','#skF_4',E_353,F_349),u1_struct_0('#skF_1'),u1_struct_0(B_350))
      | ~ m1_subset_1(F_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_350))))
      | ~ v1_funct_2(F_349,u1_struct_0('#skF_4'),u1_struct_0(B_350))
      | ~ v1_funct_1(F_349)
      | ~ m1_subset_1(E_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_350))))
      | ~ v1_funct_2(E_353,u1_struct_0('#skF_3'),u1_struct_0(B_350))
      | ~ v1_funct_1(E_353)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_350)
      | ~ v2_pre_topc(B_350)
      | v2_struct_0(B_350)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_876])).

tff(c_881,plain,(
    ! [B_350,E_353,F_349] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_350,'#skF_3','#skF_4',E_353,F_349),u1_struct_0('#skF_1'),u1_struct_0(B_350))
      | ~ m1_subset_1(F_349,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_350))))
      | ~ v1_funct_2(F_349,u1_struct_0('#skF_4'),u1_struct_0(B_350))
      | ~ v1_funct_1(F_349)
      | ~ m1_subset_1(E_353,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_350))))
      | ~ v1_funct_2(E_353,u1_struct_0('#skF_3'),u1_struct_0(B_350))
      | ~ v1_funct_1(E_353)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_350)
      | ~ v2_pre_topc(B_350)
      | v2_struct_0(B_350)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_879])).

tff(c_883,plain,(
    ! [B_354,E_355,F_356] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_354,'#skF_3','#skF_4',E_355,F_356),u1_struct_0('#skF_1'),u1_struct_0(B_354))
      | ~ m1_subset_1(F_356,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_354))))
      | ~ v1_funct_2(F_356,u1_struct_0('#skF_4'),u1_struct_0(B_354))
      | ~ v1_funct_1(F_356)
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_354))))
      | ~ v1_funct_2(E_355,u1_struct_0('#skF_3'),u1_struct_0(B_354))
      | ~ v1_funct_1(E_355)
      | ~ l1_pre_topc(B_354)
      | ~ v2_pre_topc(B_354)
      | v2_struct_0(B_354) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_76,c_881])).

tff(c_888,plain,(
    ! [E_355] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_355,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_355,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_355)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_883])).

tff(c_892,plain,(
    ! [E_355] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_355,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_355,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_355)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_62,c_60,c_888])).

tff(c_894,plain,(
    ! [E_357] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_357,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_357,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_357,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_357) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_892])).

tff(c_901,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_894])).

tff(c_908,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_901])).

tff(c_910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_619,c_908])).

tff(c_911,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_612])).

tff(c_253,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_912,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_612])).

tff(c_613,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_124,plain,(
    ! [A_116,B_117,C_118] :
      ( m1_pre_topc(k1_tsep_1(A_116,B_117,C_118),A_116)
      | ~ m1_pre_topc(C_118,A_116)
      | v2_struct_0(C_118)
      | ~ m1_pre_topc(B_117,A_116)
      | v2_struct_0(B_117)
      | ~ l1_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_127,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_124])).

tff(c_129,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_78,c_74,c_127])).

tff(c_130,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_76,c_129])).

tff(c_999,plain,(
    ! [C_386,D_385,A_388,B_387,E_384] :
      ( v1_funct_2(k3_tmap_1(A_388,B_387,C_386,D_385,E_384),u1_struct_0(D_385),u1_struct_0(B_387))
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_386),u1_struct_0(B_387))))
      | ~ v1_funct_2(E_384,u1_struct_0(C_386),u1_struct_0(B_387))
      | ~ v1_funct_1(E_384)
      | ~ m1_pre_topc(D_385,A_388)
      | ~ m1_pre_topc(C_386,A_388)
      | ~ l1_pre_topc(B_387)
      | ~ v2_pre_topc(B_387)
      | v2_struct_0(B_387)
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1001,plain,(
    ! [A_388,D_385] :
      ( v1_funct_2(k3_tmap_1(A_388,'#skF_2','#skF_1',D_385,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_385),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_385,A_388)
      | ~ m1_pre_topc('#skF_1',A_388)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(resolution,[status(thm)],[c_613,c_999])).

tff(c_1008,plain,(
    ! [A_388,D_385] :
      ( v1_funct_2(k3_tmap_1(A_388,'#skF_2','#skF_1',D_385,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_385),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_385,A_388)
      | ~ m1_pre_topc('#skF_1',A_388)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_253,c_912,c_1001])).

tff(c_1009,plain,(
    ! [A_388,D_385] :
      ( v1_funct_2(k3_tmap_1(A_388,'#skF_2','#skF_1',D_385,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_385),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_385,A_388)
      | ~ m1_pre_topc('#skF_1',A_388)
      | ~ l1_pre_topc(A_388)
      | ~ v2_pre_topc(A_388)
      | v2_struct_0(A_388) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_1008])).

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

tff(c_945,plain,(
    ! [C_364,D_363,A_366,E_362,B_365] :
      ( v1_funct_1(k3_tmap_1(A_366,B_365,C_364,D_363,E_362))
      | ~ m1_subset_1(E_362,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364),u1_struct_0(B_365))))
      | ~ v1_funct_2(E_362,u1_struct_0(C_364),u1_struct_0(B_365))
      | ~ v1_funct_1(E_362)
      | ~ m1_pre_topc(D_363,A_366)
      | ~ m1_pre_topc(C_364,A_366)
      | ~ l1_pre_topc(B_365)
      | ~ v2_pre_topc(B_365)
      | v2_struct_0(B_365)
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366)
      | v2_struct_0(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_947,plain,(
    ! [A_366,D_363] :
      ( v1_funct_1(k3_tmap_1(A_366,'#skF_2','#skF_1',D_363,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_363,A_366)
      | ~ m1_pre_topc('#skF_1',A_366)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366)
      | v2_struct_0(A_366) ) ),
    inference(resolution,[status(thm)],[c_613,c_945])).

tff(c_954,plain,(
    ! [A_366,D_363] :
      ( v1_funct_1(k3_tmap_1(A_366,'#skF_2','#skF_1',D_363,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_363,A_366)
      | ~ m1_pre_topc('#skF_1',A_366)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_366)
      | ~ v2_pre_topc(A_366)
      | v2_struct_0(A_366) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_253,c_912,c_947])).

tff(c_966,plain,(
    ! [A_371,D_372] :
      ( v1_funct_1(k3_tmap_1(A_371,'#skF_2','#skF_1',D_372,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_372,A_371)
      | ~ m1_pre_topc('#skF_1',A_371)
      | ~ l1_pre_topc(A_371)
      | ~ v2_pre_topc(A_371)
      | v2_struct_0(A_371) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_954])).

tff(c_54,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_93,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_54])).

tff(c_913,plain,(
    ! [D_358,C_359,A_360,B_361] :
      ( D_358 = C_359
      | ~ r2_funct_2(A_360,B_361,C_359,D_358)
      | ~ m1_subset_1(D_358,k1_zfmisc_1(k2_zfmisc_1(A_360,B_361)))
      | ~ v1_funct_2(D_358,A_360,B_361)
      | ~ v1_funct_1(D_358)
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_360,B_361)))
      | ~ v1_funct_2(C_359,A_360,B_361)
      | ~ v1_funct_1(C_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_915,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_93,c_913])).

tff(c_924,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_915])).

tff(c_944,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_924])).

tff(c_969,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_966,c_944])).

tff(c_972,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_130,c_78,c_969])).

tff(c_974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_972])).

tff(c_975,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_924])).

tff(c_1163,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_975])).

tff(c_1166,plain,
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
    inference(resolution,[status(thm)],[c_18,c_1163])).

tff(c_1169,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_84,c_82,c_130,c_78,c_253,c_912,c_613,c_1166])).

tff(c_1171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_1169])).

tff(c_1172,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_975])).

tff(c_1215,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1172])).

tff(c_1218,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1009,c_1215])).

tff(c_1221,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_130,c_78,c_1218])).

tff(c_1223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1221])).

tff(c_1224,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1172])).

tff(c_66,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_977,plain,(
    ! [C_375,D_374,A_377,E_373,B_376] :
      ( v1_funct_1(k3_tmap_1(A_377,B_376,C_375,D_374,E_373))
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

tff(c_979,plain,(
    ! [A_377,D_374] :
      ( v1_funct_1(k3_tmap_1(A_377,'#skF_2','#skF_1',D_374,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_374,A_377)
      | ~ m1_pre_topc('#skF_1',A_377)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(resolution,[status(thm)],[c_613,c_977])).

tff(c_986,plain,(
    ! [A_377,D_374] :
      ( v1_funct_1(k3_tmap_1(A_377,'#skF_2','#skF_1',D_374,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_374,A_377)
      | ~ m1_pre_topc('#skF_1',A_377)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_253,c_912,c_979])).

tff(c_987,plain,(
    ! [A_377,D_374] :
      ( v1_funct_1(k3_tmap_1(A_377,'#skF_2','#skF_1',D_374,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_374,A_377)
      | ~ m1_pre_topc('#skF_1',A_377)
      | ~ l1_pre_topc(A_377)
      | ~ v2_pre_topc(A_377)
      | v2_struct_0(A_377) ) ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_986])).

tff(c_52,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_94,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_52])).

tff(c_917,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_94,c_913])).

tff(c_927,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_917])).

tff(c_1311,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_927])).

tff(c_1314,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_987,c_1311])).

tff(c_1317,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_130,c_74,c_1314])).

tff(c_1319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1317])).

tff(c_1320,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_927])).

tff(c_1324,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1320])).

tff(c_1327,plain,
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
    inference(resolution,[status(thm)],[c_18,c_1324])).

tff(c_1330,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_84,c_82,c_130,c_74,c_253,c_912,c_613,c_1327])).

tff(c_1332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_86,c_1330])).

tff(c_1333,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1320])).

tff(c_1376,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1333])).

tff(c_1389,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_1009,c_1376])).

tff(c_1392,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_130,c_74,c_1389])).

tff(c_1394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_1392])).

tff(c_1395,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1333])).

tff(c_58,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_50,plain,(
    r4_tsep_1('#skF_1','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_257])).

tff(c_2290,plain,(
    ! [A_543,B_544,E_545,C_541,D_542] :
      ( v5_pre_topc(E_545,k1_tsep_1(A_543,C_541,D_542),B_544)
      | ~ m1_subset_1(k3_tmap_1(A_543,B_544,k1_tsep_1(A_543,C_541,D_542),D_542,E_545),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_542),u1_struct_0(B_544))))
      | ~ v5_pre_topc(k3_tmap_1(A_543,B_544,k1_tsep_1(A_543,C_541,D_542),D_542,E_545),D_542,B_544)
      | ~ v1_funct_2(k3_tmap_1(A_543,B_544,k1_tsep_1(A_543,C_541,D_542),D_542,E_545),u1_struct_0(D_542),u1_struct_0(B_544))
      | ~ v1_funct_1(k3_tmap_1(A_543,B_544,k1_tsep_1(A_543,C_541,D_542),D_542,E_545))
      | ~ m1_subset_1(k3_tmap_1(A_543,B_544,k1_tsep_1(A_543,C_541,D_542),C_541,E_545),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_541),u1_struct_0(B_544))))
      | ~ v5_pre_topc(k3_tmap_1(A_543,B_544,k1_tsep_1(A_543,C_541,D_542),C_541,E_545),C_541,B_544)
      | ~ v1_funct_2(k3_tmap_1(A_543,B_544,k1_tsep_1(A_543,C_541,D_542),C_541,E_545),u1_struct_0(C_541),u1_struct_0(B_544))
      | ~ v1_funct_1(k3_tmap_1(A_543,B_544,k1_tsep_1(A_543,C_541,D_542),C_541,E_545))
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_543,C_541,D_542)),u1_struct_0(B_544))))
      | ~ v1_funct_2(E_545,u1_struct_0(k1_tsep_1(A_543,C_541,D_542)),u1_struct_0(B_544))
      | ~ v1_funct_1(E_545)
      | ~ r4_tsep_1(A_543,C_541,D_542)
      | ~ m1_pre_topc(D_542,A_543)
      | v2_struct_0(D_542)
      | ~ m1_pre_topc(C_541,A_543)
      | v2_struct_0(C_541)
      | ~ l1_pre_topc(B_544)
      | ~ v2_pre_topc(B_544)
      | v2_struct_0(B_544)
      | ~ l1_pre_topc(A_543)
      | ~ v2_pre_topc(A_543)
      | v2_struct_0(A_543) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_2300,plain,(
    ! [E_545,B_544] :
      ( v5_pre_topc(E_545,k1_tsep_1('#skF_1','#skF_3','#skF_4'),B_544)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_544,'#skF_1','#skF_4',E_545),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_544))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_544,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_545),'#skF_4',B_544)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_544,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_545),u1_struct_0('#skF_4'),u1_struct_0(B_544))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_544,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_545))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_544,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_545),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_544))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_544,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_545),'#skF_3',B_544)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_544,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_545),u1_struct_0('#skF_3'),u1_struct_0(B_544))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_544,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_545))
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_544))))
      | ~ v1_funct_2(E_545,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_544))
      | ~ v1_funct_1(E_545)
      | ~ r4_tsep_1('#skF_1','#skF_3','#skF_4')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_544)
      | ~ v2_pre_topc(B_544)
      | v2_struct_0(B_544)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_2290])).

tff(c_2305,plain,(
    ! [E_545,B_544] :
      ( v5_pre_topc(E_545,'#skF_1',B_544)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_544,'#skF_1','#skF_4',E_545),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_544))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_544,'#skF_1','#skF_4',E_545),'#skF_4',B_544)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_544,'#skF_1','#skF_4',E_545),u1_struct_0('#skF_4'),u1_struct_0(B_544))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_544,'#skF_1','#skF_4',E_545))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_544,'#skF_1','#skF_3',E_545),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_544))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_544,'#skF_1','#skF_3',E_545),'#skF_3',B_544)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_544,'#skF_1','#skF_3',E_545),u1_struct_0('#skF_3'),u1_struct_0(B_544))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_544,'#skF_1','#skF_3',E_545))
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_544))))
      | ~ v1_funct_2(E_545,u1_struct_0('#skF_1'),u1_struct_0(B_544))
      | ~ v1_funct_1(E_545)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_544)
      | ~ v2_pre_topc(B_544)
      | v2_struct_0(B_544)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_78,c_74,c_50,c_72,c_72,c_72,c_72,c_72,c_72,c_72,c_72,c_72,c_72,c_2300])).

tff(c_3887,plain,(
    ! [E_813,B_814] :
      ( v5_pre_topc(E_813,'#skF_1',B_814)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_814,'#skF_1','#skF_4',E_813),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_814))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_814,'#skF_1','#skF_4',E_813),'#skF_4',B_814)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_814,'#skF_1','#skF_4',E_813),u1_struct_0('#skF_4'),u1_struct_0(B_814))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_814,'#skF_1','#skF_4',E_813))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_814,'#skF_1','#skF_3',E_813),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_814))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_814,'#skF_1','#skF_3',E_813),'#skF_3',B_814)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_814,'#skF_1','#skF_3',E_813),u1_struct_0('#skF_3'),u1_struct_0(B_814))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_814,'#skF_1','#skF_3',E_813))
      | ~ m1_subset_1(E_813,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_814))))
      | ~ v1_funct_2(E_813,u1_struct_0('#skF_1'),u1_struct_0(B_814))
      | ~ v1_funct_1(E_813)
      | ~ l1_pre_topc(B_814)
      | ~ v2_pre_topc(B_814)
      | v2_struct_0(B_814) ) ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_80,c_76,c_2305])).

tff(c_3893,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_3887])).

tff(c_3900,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_253,c_912,c_613,c_70,c_1224,c_68,c_1224,c_66,c_1224,c_64,c_62,c_1395,c_60,c_1395,c_58,c_1395,c_56,c_1395,c_3893])).

tff(c_3902,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_911,c_3900])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:42:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.31/2.96  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/2.97  
% 8.31/2.97  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.31/2.98  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > r4_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.31/2.98  
% 8.31/2.98  %Foreground sorts:
% 8.31/2.98  
% 8.31/2.98  
% 8.31/2.98  %Background operators:
% 8.31/2.98  
% 8.31/2.98  
% 8.31/2.98  %Foreground operators:
% 8.31/2.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 8.31/2.98  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.31/2.98  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 8.31/2.98  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 8.31/2.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.31/2.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.31/2.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 8.31/2.98  tff(r4_tsep_1, type, r4_tsep_1: ($i * $i * $i) > $o).
% 8.31/2.98  tff('#skF_5', type, '#skF_5': $i).
% 8.31/2.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.31/2.98  tff('#skF_6', type, '#skF_6': $i).
% 8.31/2.98  tff('#skF_2', type, '#skF_2': $i).
% 8.31/2.98  tff('#skF_3', type, '#skF_3': $i).
% 8.31/2.98  tff('#skF_1', type, '#skF_1': $i).
% 8.31/2.98  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 8.31/2.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.31/2.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.31/2.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.31/2.98  tff('#skF_4', type, '#skF_4': $i).
% 8.31/2.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.31/2.98  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 8.31/2.98  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 8.31/2.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 8.31/2.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 8.31/2.98  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 8.31/2.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.31/2.98  
% 8.59/3.01  tff(f_257, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((A = k1_tsep_1(A, C, D)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (((r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) & r4_tsep_1(A, C, D)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_tmap_1)).
% 8.59/3.01  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 8.59/3.01  tff(f_105, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 8.59/3.01  tff(f_135, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 8.59/3.01  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 8.59/3.01  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (r4_tsep_1(A, C, D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t126_tmap_1)).
% 8.59/3.01  tff(c_86, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_84, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_82, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_68, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_60, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_92, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_76, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_90, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_88, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_78, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_74, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_72, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_505, plain, (![D_257, B_259, E_262, F_258, A_261, C_260]: (m1_subset_1(k10_tmap_1(A_261, B_259, C_260, D_257, E_262, F_258), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_261, C_260, D_257)), u1_struct_0(B_259)))) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_257), u1_struct_0(B_259)))) | ~v1_funct_2(F_258, u1_struct_0(D_257), u1_struct_0(B_259)) | ~v1_funct_1(F_258) | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_260), u1_struct_0(B_259)))) | ~v1_funct_2(E_262, u1_struct_0(C_260), u1_struct_0(B_259)) | ~v1_funct_1(E_262) | ~m1_pre_topc(D_257, A_261) | v2_struct_0(D_257) | ~m1_pre_topc(C_260, A_261) | v2_struct_0(C_260) | ~l1_pre_topc(B_259) | ~v2_pre_topc(B_259) | v2_struct_0(B_259) | ~l1_pre_topc(A_261) | ~v2_pre_topc(A_261) | v2_struct_0(A_261))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.59/3.01  tff(c_534, plain, (![B_259, E_262, F_258]: (m1_subset_1(k10_tmap_1('#skF_1', B_259, '#skF_3', '#skF_4', E_262, F_258), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_259)))) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_259)))) | ~v1_funct_2(F_258, u1_struct_0('#skF_4'), u1_struct_0(B_259)) | ~v1_funct_1(F_258) | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_259)))) | ~v1_funct_2(E_262, u1_struct_0('#skF_3'), u1_struct_0(B_259)) | ~v1_funct_1(E_262) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_259) | ~v2_pre_topc(B_259) | v2_struct_0(B_259) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_505])).
% 8.59/3.01  tff(c_554, plain, (![B_259, E_262, F_258]: (m1_subset_1(k10_tmap_1('#skF_1', B_259, '#skF_3', '#skF_4', E_262, F_258), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_259)))) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_259)))) | ~v1_funct_2(F_258, u1_struct_0('#skF_4'), u1_struct_0(B_259)) | ~v1_funct_1(F_258) | ~m1_subset_1(E_262, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_259)))) | ~v1_funct_2(E_262, u1_struct_0('#skF_3'), u1_struct_0(B_259)) | ~v1_funct_1(E_262) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_259) | ~v2_pre_topc(B_259) | v2_struct_0(B_259) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_534])).
% 8.59/3.01  tff(c_556, plain, (![B_263, E_264, F_265]: (m1_subset_1(k10_tmap_1('#skF_1', B_263, '#skF_3', '#skF_4', E_264, F_265), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_263)))) | ~m1_subset_1(F_265, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_263)))) | ~v1_funct_2(F_265, u1_struct_0('#skF_4'), u1_struct_0(B_263)) | ~v1_funct_1(F_265) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_263)))) | ~v1_funct_2(E_264, u1_struct_0('#skF_3'), u1_struct_0(B_263)) | ~v1_funct_1(E_264) | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263))), inference(negUnitSimplification, [status(thm)], [c_92, c_80, c_76, c_554])).
% 8.59/3.01  tff(c_196, plain, (![E_151, B_148, A_150, D_146, C_149, F_147]: (v1_funct_1(k10_tmap_1(A_150, B_148, C_149, D_146, E_151, F_147)) | ~m1_subset_1(F_147, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_146), u1_struct_0(B_148)))) | ~v1_funct_2(F_147, u1_struct_0(D_146), u1_struct_0(B_148)) | ~v1_funct_1(F_147) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0(B_148)))) | ~v1_funct_2(E_151, u1_struct_0(C_149), u1_struct_0(B_148)) | ~v1_funct_1(E_151) | ~m1_pre_topc(D_146, A_150) | v2_struct_0(D_146) | ~m1_pre_topc(C_149, A_150) | v2_struct_0(C_149) | ~l1_pre_topc(B_148) | ~v2_pre_topc(B_148) | v2_struct_0(B_148) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.59/3.01  tff(c_200, plain, (![A_150, C_149, E_151]: (v1_funct_1(k10_tmap_1(A_150, '#skF_2', C_149, '#skF_4', E_151, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_151, u1_struct_0(C_149), u1_struct_0('#skF_2')) | ~v1_funct_1(E_151) | ~m1_pre_topc('#skF_4', A_150) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_149, A_150) | v2_struct_0(C_149) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(resolution, [status(thm)], [c_56, c_196])).
% 8.59/3.01  tff(c_206, plain, (![A_150, C_149, E_151]: (v1_funct_1(k10_tmap_1(A_150, '#skF_2', C_149, '#skF_4', E_151, '#skF_6')) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_151, u1_struct_0(C_149), u1_struct_0('#skF_2')) | ~v1_funct_1(E_151) | ~m1_pre_topc('#skF_4', A_150) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_149, A_150) | v2_struct_0(C_149) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_62, c_60, c_200])).
% 8.59/3.01  tff(c_212, plain, (![A_152, C_153, E_154]: (v1_funct_1(k10_tmap_1(A_152, '#skF_2', C_153, '#skF_4', E_154, '#skF_6')) | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_153), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_154, u1_struct_0(C_153), u1_struct_0('#skF_2')) | ~v1_funct_1(E_154) | ~m1_pre_topc('#skF_4', A_152) | ~m1_pre_topc(C_153, A_152) | v2_struct_0(C_153) | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(negUnitSimplification, [status(thm)], [c_86, c_76, c_206])).
% 8.59/3.01  tff(c_219, plain, (![A_152]: (v1_funct_1(k10_tmap_1(A_152, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_152) | ~m1_pre_topc('#skF_3', A_152) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(resolution, [status(thm)], [c_64, c_212])).
% 8.59/3.01  tff(c_230, plain, (![A_152]: (v1_funct_1(k10_tmap_1(A_152, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_152) | ~m1_pre_topc('#skF_3', A_152) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_152) | ~v2_pre_topc(A_152) | v2_struct_0(A_152))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_219])).
% 8.59/3.01  tff(c_243, plain, (![A_161]: (v1_funct_1(k10_tmap_1(A_161, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_161) | ~m1_pre_topc('#skF_3', A_161) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(negUnitSimplification, [status(thm)], [c_80, c_230])).
% 8.59/3.01  tff(c_48, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_131, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_48])).
% 8.59/3.01  tff(c_246, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_243, c_131])).
% 8.59/3.01  tff(c_249, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_246])).
% 8.59/3.01  tff(c_251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_249])).
% 8.59/3.01  tff(c_252, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_48])).
% 8.59/3.01  tff(c_254, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_252])).
% 8.59/3.01  tff(c_585, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_556, c_254])).
% 8.59/3.01  tff(c_609, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_68, c_64, c_62, c_60, c_56, c_585])).
% 8.59/3.01  tff(c_611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_609])).
% 8.59/3.01  tff(c_612, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_252])).
% 8.59/3.01  tff(c_619, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_612])).
% 8.59/3.01  tff(c_876, plain, (![B_350, E_353, A_352, D_348, C_351, F_349]: (v1_funct_2(k10_tmap_1(A_352, B_350, C_351, D_348, E_353, F_349), u1_struct_0(k1_tsep_1(A_352, C_351, D_348)), u1_struct_0(B_350)) | ~m1_subset_1(F_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_348), u1_struct_0(B_350)))) | ~v1_funct_2(F_349, u1_struct_0(D_348), u1_struct_0(B_350)) | ~v1_funct_1(F_349) | ~m1_subset_1(E_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_351), u1_struct_0(B_350)))) | ~v1_funct_2(E_353, u1_struct_0(C_351), u1_struct_0(B_350)) | ~v1_funct_1(E_353) | ~m1_pre_topc(D_348, A_352) | v2_struct_0(D_348) | ~m1_pre_topc(C_351, A_352) | v2_struct_0(C_351) | ~l1_pre_topc(B_350) | ~v2_pre_topc(B_350) | v2_struct_0(B_350) | ~l1_pre_topc(A_352) | ~v2_pre_topc(A_352) | v2_struct_0(A_352))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.59/3.01  tff(c_879, plain, (![B_350, E_353, F_349]: (v1_funct_2(k10_tmap_1('#skF_1', B_350, '#skF_3', '#skF_4', E_353, F_349), u1_struct_0('#skF_1'), u1_struct_0(B_350)) | ~m1_subset_1(F_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_350)))) | ~v1_funct_2(F_349, u1_struct_0('#skF_4'), u1_struct_0(B_350)) | ~v1_funct_1(F_349) | ~m1_subset_1(E_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_350)))) | ~v1_funct_2(E_353, u1_struct_0('#skF_3'), u1_struct_0(B_350)) | ~v1_funct_1(E_353) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_350) | ~v2_pre_topc(B_350) | v2_struct_0(B_350) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_876])).
% 8.59/3.01  tff(c_881, plain, (![B_350, E_353, F_349]: (v1_funct_2(k10_tmap_1('#skF_1', B_350, '#skF_3', '#skF_4', E_353, F_349), u1_struct_0('#skF_1'), u1_struct_0(B_350)) | ~m1_subset_1(F_349, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_350)))) | ~v1_funct_2(F_349, u1_struct_0('#skF_4'), u1_struct_0(B_350)) | ~v1_funct_1(F_349) | ~m1_subset_1(E_353, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_350)))) | ~v1_funct_2(E_353, u1_struct_0('#skF_3'), u1_struct_0(B_350)) | ~v1_funct_1(E_353) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_350) | ~v2_pre_topc(B_350) | v2_struct_0(B_350) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_879])).
% 8.59/3.01  tff(c_883, plain, (![B_354, E_355, F_356]: (v1_funct_2(k10_tmap_1('#skF_1', B_354, '#skF_3', '#skF_4', E_355, F_356), u1_struct_0('#skF_1'), u1_struct_0(B_354)) | ~m1_subset_1(F_356, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_354)))) | ~v1_funct_2(F_356, u1_struct_0('#skF_4'), u1_struct_0(B_354)) | ~v1_funct_1(F_356) | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_354)))) | ~v1_funct_2(E_355, u1_struct_0('#skF_3'), u1_struct_0(B_354)) | ~v1_funct_1(E_355) | ~l1_pre_topc(B_354) | ~v2_pre_topc(B_354) | v2_struct_0(B_354))), inference(negUnitSimplification, [status(thm)], [c_92, c_80, c_76, c_881])).
% 8.59/3.01  tff(c_888, plain, (![E_355]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_355, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_355, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_355) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_883])).
% 8.59/3.01  tff(c_892, plain, (![E_355]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_355, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_355, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_355) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_62, c_60, c_888])).
% 8.59/3.01  tff(c_894, plain, (![E_357]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_357, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_357, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_357, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_357))), inference(negUnitSimplification, [status(thm)], [c_86, c_892])).
% 8.59/3.01  tff(c_901, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_894])).
% 8.59/3.01  tff(c_908, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_901])).
% 8.59/3.01  tff(c_910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_619, c_908])).
% 8.59/3.01  tff(c_911, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_612])).
% 8.59/3.01  tff(c_253, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_48])).
% 8.59/3.01  tff(c_912, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_612])).
% 8.59/3.01  tff(c_613, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_252])).
% 8.59/3.01  tff(c_124, plain, (![A_116, B_117, C_118]: (m1_pre_topc(k1_tsep_1(A_116, B_117, C_118), A_116) | ~m1_pre_topc(C_118, A_116) | v2_struct_0(C_118) | ~m1_pre_topc(B_117, A_116) | v2_struct_0(B_117) | ~l1_pre_topc(A_116) | v2_struct_0(A_116))), inference(cnfTransformation, [status(thm)], [f_105])).
% 8.59/3.01  tff(c_127, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_72, c_124])).
% 8.59/3.01  tff(c_129, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_78, c_74, c_127])).
% 8.59/3.01  tff(c_130, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_92, c_80, c_76, c_129])).
% 8.59/3.01  tff(c_999, plain, (![C_386, D_385, A_388, B_387, E_384]: (v1_funct_2(k3_tmap_1(A_388, B_387, C_386, D_385, E_384), u1_struct_0(D_385), u1_struct_0(B_387)) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_386), u1_struct_0(B_387)))) | ~v1_funct_2(E_384, u1_struct_0(C_386), u1_struct_0(B_387)) | ~v1_funct_1(E_384) | ~m1_pre_topc(D_385, A_388) | ~m1_pre_topc(C_386, A_388) | ~l1_pre_topc(B_387) | ~v2_pre_topc(B_387) | v2_struct_0(B_387) | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388) | v2_struct_0(A_388))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.59/3.01  tff(c_1001, plain, (![A_388, D_385]: (v1_funct_2(k3_tmap_1(A_388, '#skF_2', '#skF_1', D_385, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_385), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_385, A_388) | ~m1_pre_topc('#skF_1', A_388) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388) | v2_struct_0(A_388))), inference(resolution, [status(thm)], [c_613, c_999])).
% 8.59/3.01  tff(c_1008, plain, (![A_388, D_385]: (v1_funct_2(k3_tmap_1(A_388, '#skF_2', '#skF_1', D_385, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_385), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_385, A_388) | ~m1_pre_topc('#skF_1', A_388) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388) | v2_struct_0(A_388))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_253, c_912, c_1001])).
% 8.59/3.01  tff(c_1009, plain, (![A_388, D_385]: (v1_funct_2(k3_tmap_1(A_388, '#skF_2', '#skF_1', D_385, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_385), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_385, A_388) | ~m1_pre_topc('#skF_1', A_388) | ~l1_pre_topc(A_388) | ~v2_pre_topc(A_388) | v2_struct_0(A_388))), inference(negUnitSimplification, [status(thm)], [c_86, c_1008])).
% 8.59/3.01  tff(c_18, plain, (![E_18, C_16, D_17, A_14, B_15]: (m1_subset_1(k3_tmap_1(A_14, B_15, C_16, D_17, E_18), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_17), u1_struct_0(B_15)))) | ~m1_subset_1(E_18, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_16), u1_struct_0(B_15)))) | ~v1_funct_2(E_18, u1_struct_0(C_16), u1_struct_0(B_15)) | ~v1_funct_1(E_18) | ~m1_pre_topc(D_17, A_14) | ~m1_pre_topc(C_16, A_14) | ~l1_pre_topc(B_15) | ~v2_pre_topc(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.59/3.01  tff(c_945, plain, (![C_364, D_363, A_366, E_362, B_365]: (v1_funct_1(k3_tmap_1(A_366, B_365, C_364, D_363, E_362)) | ~m1_subset_1(E_362, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_364), u1_struct_0(B_365)))) | ~v1_funct_2(E_362, u1_struct_0(C_364), u1_struct_0(B_365)) | ~v1_funct_1(E_362) | ~m1_pre_topc(D_363, A_366) | ~m1_pre_topc(C_364, A_366) | ~l1_pre_topc(B_365) | ~v2_pre_topc(B_365) | v2_struct_0(B_365) | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366) | v2_struct_0(A_366))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.59/3.01  tff(c_947, plain, (![A_366, D_363]: (v1_funct_1(k3_tmap_1(A_366, '#skF_2', '#skF_1', D_363, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_363, A_366) | ~m1_pre_topc('#skF_1', A_366) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366) | v2_struct_0(A_366))), inference(resolution, [status(thm)], [c_613, c_945])).
% 8.59/3.01  tff(c_954, plain, (![A_366, D_363]: (v1_funct_1(k3_tmap_1(A_366, '#skF_2', '#skF_1', D_363, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_363, A_366) | ~m1_pre_topc('#skF_1', A_366) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_366) | ~v2_pre_topc(A_366) | v2_struct_0(A_366))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_253, c_912, c_947])).
% 8.59/3.01  tff(c_966, plain, (![A_371, D_372]: (v1_funct_1(k3_tmap_1(A_371, '#skF_2', '#skF_1', D_372, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_372, A_371) | ~m1_pre_topc('#skF_1', A_371) | ~l1_pre_topc(A_371) | ~v2_pre_topc(A_371) | v2_struct_0(A_371))), inference(negUnitSimplification, [status(thm)], [c_86, c_954])).
% 8.59/3.01  tff(c_54, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_93, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_54])).
% 8.59/3.01  tff(c_913, plain, (![D_358, C_359, A_360, B_361]: (D_358=C_359 | ~r2_funct_2(A_360, B_361, C_359, D_358) | ~m1_subset_1(D_358, k1_zfmisc_1(k2_zfmisc_1(A_360, B_361))) | ~v1_funct_2(D_358, A_360, B_361) | ~v1_funct_1(D_358) | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(A_360, B_361))) | ~v1_funct_2(C_359, A_360, B_361) | ~v1_funct_1(C_359))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.59/3.01  tff(c_915, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_93, c_913])).
% 8.59/3.01  tff(c_924, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_915])).
% 8.59/3.01  tff(c_944, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_924])).
% 8.59/3.01  tff(c_969, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_966, c_944])).
% 8.59/3.01  tff(c_972, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_130, c_78, c_969])).
% 8.59/3.01  tff(c_974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_972])).
% 8.59/3.01  tff(c_975, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_924])).
% 8.59/3.01  tff(c_1163, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_975])).
% 8.59/3.01  tff(c_1166, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1163])).
% 8.59/3.01  tff(c_1169, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_84, c_82, c_130, c_78, c_253, c_912, c_613, c_1166])).
% 8.59/3.01  tff(c_1171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_1169])).
% 8.59/3.01  tff(c_1172, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_975])).
% 8.59/3.01  tff(c_1215, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1172])).
% 8.59/3.01  tff(c_1218, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1009, c_1215])).
% 8.59/3.01  tff(c_1221, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_130, c_78, c_1218])).
% 8.59/3.01  tff(c_1223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1221])).
% 8.59/3.01  tff(c_1224, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1172])).
% 8.59/3.01  tff(c_66, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_977, plain, (![C_375, D_374, A_377, E_373, B_376]: (v1_funct_1(k3_tmap_1(A_377, B_376, C_375, D_374, E_373)) | ~m1_subset_1(E_373, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_375), u1_struct_0(B_376)))) | ~v1_funct_2(E_373, u1_struct_0(C_375), u1_struct_0(B_376)) | ~v1_funct_1(E_373) | ~m1_pre_topc(D_374, A_377) | ~m1_pre_topc(C_375, A_377) | ~l1_pre_topc(B_376) | ~v2_pre_topc(B_376) | v2_struct_0(B_376) | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(cnfTransformation, [status(thm)], [f_135])).
% 8.59/3.01  tff(c_979, plain, (![A_377, D_374]: (v1_funct_1(k3_tmap_1(A_377, '#skF_2', '#skF_1', D_374, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_374, A_377) | ~m1_pre_topc('#skF_1', A_377) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(resolution, [status(thm)], [c_613, c_977])).
% 8.59/3.01  tff(c_986, plain, (![A_377, D_374]: (v1_funct_1(k3_tmap_1(A_377, '#skF_2', '#skF_1', D_374, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_374, A_377) | ~m1_pre_topc('#skF_1', A_377) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_253, c_912, c_979])).
% 8.59/3.01  tff(c_987, plain, (![A_377, D_374]: (v1_funct_1(k3_tmap_1(A_377, '#skF_2', '#skF_1', D_374, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_374, A_377) | ~m1_pre_topc('#skF_1', A_377) | ~l1_pre_topc(A_377) | ~v2_pre_topc(A_377) | v2_struct_0(A_377))), inference(negUnitSimplification, [status(thm)], [c_86, c_986])).
% 8.59/3.01  tff(c_52, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_94, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_52])).
% 8.59/3.01  tff(c_917, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_94, c_913])).
% 8.59/3.01  tff(c_927, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_917])).
% 8.59/3.01  tff(c_1311, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_927])).
% 8.59/3.01  tff(c_1314, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_987, c_1311])).
% 8.59/3.01  tff(c_1317, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_130, c_74, c_1314])).
% 8.59/3.01  tff(c_1319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1317])).
% 8.59/3.01  tff(c_1320, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_927])).
% 8.59/3.01  tff(c_1324, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1320])).
% 8.59/3.01  tff(c_1327, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1324])).
% 8.59/3.01  tff(c_1330, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_84, c_82, c_130, c_74, c_253, c_912, c_613, c_1327])).
% 8.59/3.01  tff(c_1332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_86, c_1330])).
% 8.59/3.01  tff(c_1333, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1320])).
% 8.59/3.01  tff(c_1376, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1333])).
% 8.59/3.01  tff(c_1389, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_1009, c_1376])).
% 8.59/3.01  tff(c_1392, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_130, c_74, c_1389])).
% 8.59/3.01  tff(c_1394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_1392])).
% 8.59/3.01  tff(c_1395, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1333])).
% 8.59/3.01  tff(c_58, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_50, plain, (r4_tsep_1('#skF_1', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_257])).
% 8.59/3.01  tff(c_2290, plain, (![A_543, B_544, E_545, C_541, D_542]: (v5_pre_topc(E_545, k1_tsep_1(A_543, C_541, D_542), B_544) | ~m1_subset_1(k3_tmap_1(A_543, B_544, k1_tsep_1(A_543, C_541, D_542), D_542, E_545), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_542), u1_struct_0(B_544)))) | ~v5_pre_topc(k3_tmap_1(A_543, B_544, k1_tsep_1(A_543, C_541, D_542), D_542, E_545), D_542, B_544) | ~v1_funct_2(k3_tmap_1(A_543, B_544, k1_tsep_1(A_543, C_541, D_542), D_542, E_545), u1_struct_0(D_542), u1_struct_0(B_544)) | ~v1_funct_1(k3_tmap_1(A_543, B_544, k1_tsep_1(A_543, C_541, D_542), D_542, E_545)) | ~m1_subset_1(k3_tmap_1(A_543, B_544, k1_tsep_1(A_543, C_541, D_542), C_541, E_545), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_541), u1_struct_0(B_544)))) | ~v5_pre_topc(k3_tmap_1(A_543, B_544, k1_tsep_1(A_543, C_541, D_542), C_541, E_545), C_541, B_544) | ~v1_funct_2(k3_tmap_1(A_543, B_544, k1_tsep_1(A_543, C_541, D_542), C_541, E_545), u1_struct_0(C_541), u1_struct_0(B_544)) | ~v1_funct_1(k3_tmap_1(A_543, B_544, k1_tsep_1(A_543, C_541, D_542), C_541, E_545)) | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_543, C_541, D_542)), u1_struct_0(B_544)))) | ~v1_funct_2(E_545, u1_struct_0(k1_tsep_1(A_543, C_541, D_542)), u1_struct_0(B_544)) | ~v1_funct_1(E_545) | ~r4_tsep_1(A_543, C_541, D_542) | ~m1_pre_topc(D_542, A_543) | v2_struct_0(D_542) | ~m1_pre_topc(C_541, A_543) | v2_struct_0(C_541) | ~l1_pre_topc(B_544) | ~v2_pre_topc(B_544) | v2_struct_0(B_544) | ~l1_pre_topc(A_543) | ~v2_pre_topc(A_543) | v2_struct_0(A_543))), inference(cnfTransformation, [status(thm)], [f_195])).
% 8.59/3.01  tff(c_2300, plain, (![E_545, B_544]: (v5_pre_topc(E_545, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), B_544) | ~m1_subset_1(k3_tmap_1('#skF_1', B_544, '#skF_1', '#skF_4', E_545), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_544)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_544, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_545), '#skF_4', B_544) | ~v1_funct_2(k3_tmap_1('#skF_1', B_544, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_545), u1_struct_0('#skF_4'), u1_struct_0(B_544)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_544, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_545)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_544, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_545), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_544)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_544, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_545), '#skF_3', B_544) | ~v1_funct_2(k3_tmap_1('#skF_1', B_544, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_545), u1_struct_0('#skF_3'), u1_struct_0(B_544)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_544, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_545)) | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_544)))) | ~v1_funct_2(E_545, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_544)) | ~v1_funct_1(E_545) | ~r4_tsep_1('#skF_1', '#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_544) | ~v2_pre_topc(B_544) | v2_struct_0(B_544) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_72, c_2290])).
% 8.59/3.01  tff(c_2305, plain, (![E_545, B_544]: (v5_pre_topc(E_545, '#skF_1', B_544) | ~m1_subset_1(k3_tmap_1('#skF_1', B_544, '#skF_1', '#skF_4', E_545), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_544)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_544, '#skF_1', '#skF_4', E_545), '#skF_4', B_544) | ~v1_funct_2(k3_tmap_1('#skF_1', B_544, '#skF_1', '#skF_4', E_545), u1_struct_0('#skF_4'), u1_struct_0(B_544)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_544, '#skF_1', '#skF_4', E_545)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_544, '#skF_1', '#skF_3', E_545), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_544)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_544, '#skF_1', '#skF_3', E_545), '#skF_3', B_544) | ~v1_funct_2(k3_tmap_1('#skF_1', B_544, '#skF_1', '#skF_3', E_545), u1_struct_0('#skF_3'), u1_struct_0(B_544)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_544, '#skF_1', '#skF_3', E_545)) | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_544)))) | ~v1_funct_2(E_545, u1_struct_0('#skF_1'), u1_struct_0(B_544)) | ~v1_funct_1(E_545) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_544) | ~v2_pre_topc(B_544) | v2_struct_0(B_544) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_78, c_74, c_50, c_72, c_72, c_72, c_72, c_72, c_72, c_72, c_72, c_72, c_72, c_2300])).
% 8.59/3.01  tff(c_3887, plain, (![E_813, B_814]: (v5_pre_topc(E_813, '#skF_1', B_814) | ~m1_subset_1(k3_tmap_1('#skF_1', B_814, '#skF_1', '#skF_4', E_813), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_814)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_814, '#skF_1', '#skF_4', E_813), '#skF_4', B_814) | ~v1_funct_2(k3_tmap_1('#skF_1', B_814, '#skF_1', '#skF_4', E_813), u1_struct_0('#skF_4'), u1_struct_0(B_814)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_814, '#skF_1', '#skF_4', E_813)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_814, '#skF_1', '#skF_3', E_813), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_814)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_814, '#skF_1', '#skF_3', E_813), '#skF_3', B_814) | ~v1_funct_2(k3_tmap_1('#skF_1', B_814, '#skF_1', '#skF_3', E_813), u1_struct_0('#skF_3'), u1_struct_0(B_814)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_814, '#skF_1', '#skF_3', E_813)) | ~m1_subset_1(E_813, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_814)))) | ~v1_funct_2(E_813, u1_struct_0('#skF_1'), u1_struct_0(B_814)) | ~v1_funct_1(E_813) | ~l1_pre_topc(B_814) | ~v2_pre_topc(B_814) | v2_struct_0(B_814))), inference(negUnitSimplification, [status(thm)], [c_92, c_80, c_76, c_2305])).
% 8.59/3.01  tff(c_3893, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1224, c_3887])).
% 8.59/3.01  tff(c_3900, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_253, c_912, c_613, c_70, c_1224, c_68, c_1224, c_66, c_1224, c_64, c_62, c_1395, c_60, c_1395, c_58, c_1395, c_56, c_1395, c_3893])).
% 8.59/3.01  tff(c_3902, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_911, c_3900])).
% 8.59/3.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.59/3.01  
% 8.59/3.01  Inference rules
% 8.59/3.01  ----------------------
% 8.59/3.01  #Ref     : 0
% 8.59/3.01  #Sup     : 645
% 8.59/3.01  #Fact    : 0
% 8.59/3.01  #Define  : 0
% 8.59/3.01  #Split   : 14
% 8.59/3.01  #Chain   : 0
% 8.59/3.01  #Close   : 0
% 8.59/3.01  
% 8.59/3.01  Ordering : KBO
% 8.59/3.01  
% 8.59/3.01  Simplification rules
% 8.59/3.01  ----------------------
% 8.59/3.01  #Subsume      : 105
% 8.59/3.01  #Demod        : 2121
% 8.59/3.01  #Tautology    : 52
% 8.59/3.01  #SimpNegUnit  : 403
% 8.59/3.01  #BackRed      : 6
% 8.59/3.01  
% 8.59/3.01  #Partial instantiations: 0
% 8.59/3.01  #Strategies tried      : 1
% 8.59/3.01  
% 8.59/3.01  Timing (in seconds)
% 8.59/3.01  ----------------------
% 8.59/3.02  Preprocessing        : 0.41
% 8.59/3.02  Parsing              : 0.21
% 8.59/3.02  CNF conversion       : 0.06
% 8.59/3.02  Main loop            : 1.80
% 8.59/3.02  Inferencing          : 0.60
% 8.59/3.02  Reduction            : 0.56
% 8.59/3.02  Demodulation         : 0.42
% 8.59/3.02  BG Simplification    : 0.06
% 8.59/3.02  Subsumption          : 0.51
% 8.59/3.02  Abstraction          : 0.07
% 8.59/3.02  MUC search           : 0.00
% 8.59/3.02  Cooper               : 0.00
% 8.59/3.02  Total                : 2.28
% 8.59/3.02  Index Insertion      : 0.00
% 8.59/3.02  Index Deletion       : 0.00
% 8.59/3.02  Index Matching       : 0.00
% 8.59/3.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
