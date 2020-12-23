%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:12 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 813 expanded)
%              Number of leaves         :   32 ( 316 expanded)
%              Depth                    :   10
%              Number of atoms          :  683 (8802 expanded)
%              Number of equality atoms :   14 ( 379 expanded)
%              Maximal formula depth    :   30 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v5_pre_topc > v1_funct_2 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(v1_borsuk_1,type,(
    v1_borsuk_1: ( $i * $i ) > $o )).

tff(f_261,negated_conjecture,(
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

tff(f_197,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_tmap_1)).

tff(c_88,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_86,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_84,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_68,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_60,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_94,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_82,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_92,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_90,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_78,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_72,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_54,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_511,plain,(
    ! [D_253,A_257,F_254,C_256,B_255,E_258] :
      ( m1_subset_1(k10_tmap_1(A_257,B_255,C_256,D_253,E_258,F_254),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_257,C_256,D_253)),u1_struct_0(B_255))))
      | ~ m1_subset_1(F_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_253),u1_struct_0(B_255))))
      | ~ v1_funct_2(F_254,u1_struct_0(D_253),u1_struct_0(B_255))
      | ~ v1_funct_1(F_254)
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_256),u1_struct_0(B_255))))
      | ~ v1_funct_2(E_258,u1_struct_0(C_256),u1_struct_0(B_255))
      | ~ v1_funct_1(E_258)
      | ~ m1_pre_topc(D_253,A_257)
      | v2_struct_0(D_253)
      | ~ m1_pre_topc(C_256,A_257)
      | v2_struct_0(C_256)
      | ~ l1_pre_topc(B_255)
      | ~ v2_pre_topc(B_255)
      | v2_struct_0(B_255)
      | ~ l1_pre_topc(A_257)
      | ~ v2_pre_topc(A_257)
      | v2_struct_0(A_257) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_536,plain,(
    ! [B_255,E_258,F_254] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_255,'#skF_3','#skF_4',E_258,F_254),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_255))))
      | ~ m1_subset_1(F_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_255))))
      | ~ v1_funct_2(F_254,u1_struct_0('#skF_4'),u1_struct_0(B_255))
      | ~ v1_funct_1(F_254)
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_255))))
      | ~ v1_funct_2(E_258,u1_struct_0('#skF_3'),u1_struct_0(B_255))
      | ~ v1_funct_1(E_258)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_255)
      | ~ v2_pre_topc(B_255)
      | v2_struct_0(B_255)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_511])).

tff(c_554,plain,(
    ! [B_255,E_258,F_254] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_255,'#skF_3','#skF_4',E_258,F_254),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_255))))
      | ~ m1_subset_1(F_254,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_255))))
      | ~ v1_funct_2(F_254,u1_struct_0('#skF_4'),u1_struct_0(B_255))
      | ~ v1_funct_1(F_254)
      | ~ m1_subset_1(E_258,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_255))))
      | ~ v1_funct_2(E_258,u1_struct_0('#skF_3'),u1_struct_0(B_255))
      | ~ v1_funct_1(E_258)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_255)
      | ~ v2_pre_topc(B_255)
      | v2_struct_0(B_255)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_78,c_72,c_536])).

tff(c_556,plain,(
    ! [B_259,E_260,F_261] :
      ( m1_subset_1(k10_tmap_1('#skF_1',B_259,'#skF_3','#skF_4',E_260,F_261),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_259))))
      | ~ m1_subset_1(F_261,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_259))))
      | ~ v1_funct_2(F_261,u1_struct_0('#skF_4'),u1_struct_0(B_259))
      | ~ v1_funct_1(F_261)
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_259))))
      | ~ v1_funct_2(E_260,u1_struct_0('#skF_3'),u1_struct_0(B_259))
      | ~ v1_funct_1(E_260)
      | ~ l1_pre_topc(B_259)
      | ~ v2_pre_topc(B_259)
      | v2_struct_0(B_259) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_82,c_76,c_554])).

tff(c_197,plain,(
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

tff(c_203,plain,(
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
    inference(resolution,[status(thm)],[c_56,c_197])).

tff(c_211,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_62,c_60,c_203])).

tff(c_251,plain,(
    ! [A_164,C_165,E_166] :
      ( v1_funct_1(k10_tmap_1(A_164,'#skF_2',C_165,'#skF_4',E_166,'#skF_6'))
      | ~ m1_subset_1(E_166,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_165),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_166,u1_struct_0(C_165),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_166)
      | ~ m1_pre_topc('#skF_4',A_164)
      | ~ m1_pre_topc(C_165,A_164)
      | v2_struct_0(C_165)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_76,c_211])).

tff(c_256,plain,(
    ! [A_164] :
      ( v1_funct_1(k10_tmap_1(A_164,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_164)
      | ~ m1_pre_topc('#skF_3',A_164)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_64,c_251])).

tff(c_265,plain,(
    ! [A_164] :
      ( v1_funct_1(k10_tmap_1(A_164,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_164)
      | ~ m1_pre_topc('#skF_3',A_164)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_256])).

tff(c_272,plain,(
    ! [A_168] :
      ( v1_funct_1(k10_tmap_1(A_168,'#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc('#skF_4',A_168)
      | ~ m1_pre_topc('#skF_3',A_168)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_265])).

tff(c_48,plain,
    ( ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_126,plain,(
    ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_275,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_272,c_126])).

tff(c_278,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_78,c_72,c_275])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_278])).

tff(c_281,plain,
    ( ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_313,plain,(
    ~ m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_581,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_556,c_313])).

tff(c_603,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_70,c_68,c_64,c_62,c_60,c_56,c_581])).

tff(c_605,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_603])).

tff(c_606,plain,
    ( ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_613,plain,(
    ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_606])).

tff(c_802,plain,(
    ! [C_323,B_322,F_321,E_325,D_320,A_324] :
      ( v1_funct_2(k10_tmap_1(A_324,B_322,C_323,D_320,E_325,F_321),u1_struct_0(k1_tsep_1(A_324,C_323,D_320)),u1_struct_0(B_322))
      | ~ m1_subset_1(F_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_320),u1_struct_0(B_322))))
      | ~ v1_funct_2(F_321,u1_struct_0(D_320),u1_struct_0(B_322))
      | ~ v1_funct_1(F_321)
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_323),u1_struct_0(B_322))))
      | ~ v1_funct_2(E_325,u1_struct_0(C_323),u1_struct_0(B_322))
      | ~ v1_funct_1(E_325)
      | ~ m1_pre_topc(D_320,A_324)
      | v2_struct_0(D_320)
      | ~ m1_pre_topc(C_323,A_324)
      | v2_struct_0(C_323)
      | ~ l1_pre_topc(B_322)
      | ~ v2_pre_topc(B_322)
      | v2_struct_0(B_322)
      | ~ l1_pre_topc(A_324)
      | ~ v2_pre_topc(A_324)
      | v2_struct_0(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_805,plain,(
    ! [B_322,E_325,F_321] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_322,'#skF_3','#skF_4',E_325,F_321),u1_struct_0('#skF_1'),u1_struct_0(B_322))
      | ~ m1_subset_1(F_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_322))))
      | ~ v1_funct_2(F_321,u1_struct_0('#skF_4'),u1_struct_0(B_322))
      | ~ v1_funct_1(F_321)
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_322))))
      | ~ v1_funct_2(E_325,u1_struct_0('#skF_3'),u1_struct_0(B_322))
      | ~ v1_funct_1(E_325)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_322)
      | ~ v2_pre_topc(B_322)
      | v2_struct_0(B_322)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_802])).

tff(c_807,plain,(
    ! [B_322,E_325,F_321] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_322,'#skF_3','#skF_4',E_325,F_321),u1_struct_0('#skF_1'),u1_struct_0(B_322))
      | ~ m1_subset_1(F_321,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_322))))
      | ~ v1_funct_2(F_321,u1_struct_0('#skF_4'),u1_struct_0(B_322))
      | ~ v1_funct_1(F_321)
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_322))))
      | ~ v1_funct_2(E_325,u1_struct_0('#skF_3'),u1_struct_0(B_322))
      | ~ v1_funct_1(E_325)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_322)
      | ~ v2_pre_topc(B_322)
      | v2_struct_0(B_322)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_78,c_72,c_805])).

tff(c_820,plain,(
    ! [B_328,E_329,F_330] :
      ( v1_funct_2(k10_tmap_1('#skF_1',B_328,'#skF_3','#skF_4',E_329,F_330),u1_struct_0('#skF_1'),u1_struct_0(B_328))
      | ~ m1_subset_1(F_330,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_328))))
      | ~ v1_funct_2(F_330,u1_struct_0('#skF_4'),u1_struct_0(B_328))
      | ~ v1_funct_1(F_330)
      | ~ m1_subset_1(E_329,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_328))))
      | ~ v1_funct_2(E_329,u1_struct_0('#skF_3'),u1_struct_0(B_328))
      | ~ v1_funct_1(E_329)
      | ~ l1_pre_topc(B_328)
      | ~ v2_pre_topc(B_328)
      | v2_struct_0(B_328) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_82,c_76,c_807])).

tff(c_825,plain,(
    ! [E_329] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_329,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_329,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_329,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_329)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_820])).

tff(c_829,plain,(
    ! [E_329] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_329,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_329,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_329,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_329)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_62,c_60,c_825])).

tff(c_831,plain,(
    ! [E_331] :
      ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4',E_331,'#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(E_331,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2(E_331,u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(E_331) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_829])).

tff(c_838,plain,
    ( v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_831])).

tff(c_845,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_838])).

tff(c_847,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_845])).

tff(c_848,plain,(
    ~ v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_282,plain,(
    v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_849,plain,(
    v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_606])).

tff(c_607,plain,(
    m1_subset_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_283,plain,(
    ! [A_169,B_170,C_171] :
      ( m1_pre_topc(k1_tsep_1(A_169,B_170,C_171),A_169)
      | ~ m1_pre_topc(C_171,A_169)
      | v2_struct_0(C_171)
      | ~ m1_pre_topc(B_170,A_169)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_286,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_283])).

tff(c_288,plain,
    ( m1_pre_topc('#skF_1','#skF_1')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_78,c_72,c_286])).

tff(c_289,plain,(
    m1_pre_topc('#skF_1','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_82,c_76,c_288])).

tff(c_879,plain,(
    ! [B_344,E_341,C_343,D_342,A_345] :
      ( v1_funct_2(k3_tmap_1(A_345,B_344,C_343,D_342,E_341),u1_struct_0(D_342),u1_struct_0(B_344))
      | ~ m1_subset_1(E_341,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_343),u1_struct_0(B_344))))
      | ~ v1_funct_2(E_341,u1_struct_0(C_343),u1_struct_0(B_344))
      | ~ v1_funct_1(E_341)
      | ~ m1_pre_topc(D_342,A_345)
      | ~ m1_pre_topc(C_343,A_345)
      | ~ l1_pre_topc(B_344)
      | ~ v2_pre_topc(B_344)
      | v2_struct_0(B_344)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_881,plain,(
    ! [A_345,D_342] :
      ( v1_funct_2(k3_tmap_1(A_345,'#skF_2','#skF_1',D_342,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_342),u1_struct_0('#skF_2'))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_342,A_345)
      | ~ m1_pre_topc('#skF_1',A_345)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(resolution,[status(thm)],[c_607,c_879])).

tff(c_888,plain,(
    ! [A_345,D_342] :
      ( v1_funct_2(k3_tmap_1(A_345,'#skF_2','#skF_1',D_342,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_342),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_342,A_345)
      | ~ m1_pre_topc('#skF_1',A_345)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_282,c_849,c_881])).

tff(c_889,plain,(
    ! [A_345,D_342] :
      ( v1_funct_2(k3_tmap_1(A_345,'#skF_2','#skF_1',D_342,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0(D_342),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(D_342,A_345)
      | ~ m1_pre_topc('#skF_1',A_345)
      | ~ l1_pre_topc(A_345)
      | ~ v2_pre_topc(A_345)
      | v2_struct_0(A_345) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_888])).

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

tff(c_858,plain,(
    ! [C_334,A_336,D_333,B_335,E_332] :
      ( v1_funct_1(k3_tmap_1(A_336,B_335,C_334,D_333,E_332))
      | ~ m1_subset_1(E_332,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_334),u1_struct_0(B_335))))
      | ~ v1_funct_2(E_332,u1_struct_0(C_334),u1_struct_0(B_335))
      | ~ v1_funct_1(E_332)
      | ~ m1_pre_topc(D_333,A_336)
      | ~ m1_pre_topc(C_334,A_336)
      | ~ l1_pre_topc(B_335)
      | ~ v2_pre_topc(B_335)
      | v2_struct_0(B_335)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_860,plain,(
    ! [A_336,D_333] :
      ( v1_funct_1(k3_tmap_1(A_336,'#skF_2','#skF_1',D_333,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ v1_funct_2(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),u1_struct_0('#skF_1'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))
      | ~ m1_pre_topc(D_333,A_336)
      | ~ m1_pre_topc('#skF_1',A_336)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(resolution,[status(thm)],[c_607,c_858])).

tff(c_867,plain,(
    ! [A_336,D_333] :
      ( v1_funct_1(k3_tmap_1(A_336,'#skF_2','#skF_1',D_333,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_333,A_336)
      | ~ m1_pre_topc('#skF_1',A_336)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_282,c_849,c_860])).

tff(c_868,plain,(
    ! [A_336,D_333] :
      ( v1_funct_1(k3_tmap_1(A_336,'#skF_2','#skF_1',D_333,k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')))
      | ~ m1_pre_topc(D_333,A_336)
      | ~ m1_pre_topc('#skF_1',A_336)
      | ~ l1_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | v2_struct_0(A_336) ) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_867])).

tff(c_52,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_95,plain,(
    r2_funct_2(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52])).

tff(c_290,plain,(
    ! [D_172,C_173,A_174,B_175] :
      ( D_172 = C_173
      | ~ r2_funct_2(A_174,B_175,C_173,D_172)
      | ~ m1_subset_1(D_172,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_2(D_172,A_174,B_175)
      | ~ v1_funct_1(D_172)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_174,B_175)))
      | ~ v1_funct_2(C_173,A_174,B_175)
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_294,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_95,c_290])).

tff(c_304,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_294])).

tff(c_1242,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_1245,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_868,c_1242])).

tff(c_1248,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_289,c_78,c_1245])).

tff(c_1250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1248])).

tff(c_1251,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_1253,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1251])).

tff(c_1256,plain,
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
    inference(resolution,[status(thm)],[c_18,c_1253])).

tff(c_1259,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_86,c_84,c_289,c_78,c_282,c_849,c_607,c_1256])).

tff(c_1261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_1259])).

tff(c_1262,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1251])).

tff(c_1312,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1262])).

tff(c_1315,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_889,c_1312])).

tff(c_1318,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_289,c_78,c_1315])).

tff(c_1320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1318])).

tff(c_1321,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_3',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1262])).

tff(c_66,plain,(
    v5_pre_topc('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_50,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2',k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_96,plain,(
    r2_funct_2(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50])).

tff(c_292,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_96,c_290])).

tff(c_301,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_292])).

tff(c_1067,plain,(
    ~ v1_funct_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_1086,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_868,c_1067])).

tff(c_1089,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_289,c_72,c_1086])).

tff(c_1091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1089])).

tff(c_1092,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_1094,plain,(
    ~ m1_subset_1(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(splitLeft,[status(thm)],[c_1092])).

tff(c_1097,plain,
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
    inference(resolution,[status(thm)],[c_18,c_1094])).

tff(c_1100,plain,
    ( v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_86,c_84,c_289,c_72,c_282,c_849,c_607,c_1097])).

tff(c_1102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_88,c_1100])).

tff(c_1103,plain,
    ( ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1092])).

tff(c_1156,plain,(
    ~ v1_funct_2(k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')),u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1103])).

tff(c_1159,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_1','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_889,c_1156])).

tff(c_1162,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_289,c_72,c_1159])).

tff(c_1164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_1162])).

tff(c_1165,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_1','#skF_4',k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1103])).

tff(c_58,plain,(
    v5_pre_topc('#skF_6','#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_80,plain,(
    v1_borsuk_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_74,plain,(
    v1_borsuk_1('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_2134,plain,(
    ! [B_491,C_488,D_489,E_492,A_490] :
      ( v5_pre_topc(E_492,k1_tsep_1(A_490,C_488,D_489),B_491)
      | ~ m1_subset_1(k3_tmap_1(A_490,B_491,k1_tsep_1(A_490,C_488,D_489),D_489,E_492),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_489),u1_struct_0(B_491))))
      | ~ v5_pre_topc(k3_tmap_1(A_490,B_491,k1_tsep_1(A_490,C_488,D_489),D_489,E_492),D_489,B_491)
      | ~ v1_funct_2(k3_tmap_1(A_490,B_491,k1_tsep_1(A_490,C_488,D_489),D_489,E_492),u1_struct_0(D_489),u1_struct_0(B_491))
      | ~ v1_funct_1(k3_tmap_1(A_490,B_491,k1_tsep_1(A_490,C_488,D_489),D_489,E_492))
      | ~ m1_subset_1(k3_tmap_1(A_490,B_491,k1_tsep_1(A_490,C_488,D_489),C_488,E_492),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_488),u1_struct_0(B_491))))
      | ~ v5_pre_topc(k3_tmap_1(A_490,B_491,k1_tsep_1(A_490,C_488,D_489),C_488,E_492),C_488,B_491)
      | ~ v1_funct_2(k3_tmap_1(A_490,B_491,k1_tsep_1(A_490,C_488,D_489),C_488,E_492),u1_struct_0(C_488),u1_struct_0(B_491))
      | ~ v1_funct_1(k3_tmap_1(A_490,B_491,k1_tsep_1(A_490,C_488,D_489),C_488,E_492))
      | ~ m1_subset_1(E_492,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_490,C_488,D_489)),u1_struct_0(B_491))))
      | ~ v1_funct_2(E_492,u1_struct_0(k1_tsep_1(A_490,C_488,D_489)),u1_struct_0(B_491))
      | ~ v1_funct_1(E_492)
      | ~ m1_pre_topc(D_489,A_490)
      | ~ v1_borsuk_1(D_489,A_490)
      | v2_struct_0(D_489)
      | ~ m1_pre_topc(C_488,A_490)
      | ~ v1_borsuk_1(C_488,A_490)
      | v2_struct_0(C_488)
      | ~ l1_pre_topc(B_491)
      | ~ v2_pre_topc(B_491)
      | v2_struct_0(B_491)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_2144,plain,(
    ! [E_492,B_491] :
      ( v5_pre_topc(E_492,k1_tsep_1('#skF_1','#skF_3','#skF_4'),B_491)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_491,'#skF_1','#skF_4',E_492),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_491))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_491,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_492),'#skF_4',B_491)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_491,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_492),u1_struct_0('#skF_4'),u1_struct_0(B_491))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_491,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_4',E_492))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_491,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_492),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_491))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_491,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_492),'#skF_3',B_491)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_491,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_492),u1_struct_0('#skF_3'),u1_struct_0(B_491))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_491,k1_tsep_1('#skF_1','#skF_3','#skF_4'),'#skF_3',E_492))
      | ~ m1_subset_1(E_492,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_491))))
      | ~ v1_funct_2(E_492,u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_4')),u1_struct_0(B_491))
      | ~ v1_funct_1(E_492)
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | ~ v1_borsuk_1('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | ~ v1_borsuk_1('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_491)
      | ~ v2_pre_topc(B_491)
      | v2_struct_0(B_491)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_2134])).

tff(c_2149,plain,(
    ! [E_492,B_491] :
      ( v5_pre_topc(E_492,'#skF_1',B_491)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_491,'#skF_1','#skF_4',E_492),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_491))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_491,'#skF_1','#skF_4',E_492),'#skF_4',B_491)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_491,'#skF_1','#skF_4',E_492),u1_struct_0('#skF_4'),u1_struct_0(B_491))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_491,'#skF_1','#skF_4',E_492))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_491,'#skF_1','#skF_3',E_492),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_491))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_491,'#skF_1','#skF_3',E_492),'#skF_3',B_491)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_491,'#skF_1','#skF_3',E_492),u1_struct_0('#skF_3'),u1_struct_0(B_491))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_491,'#skF_1','#skF_3',E_492))
      | ~ m1_subset_1(E_492,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_491))))
      | ~ v1_funct_2(E_492,u1_struct_0('#skF_1'),u1_struct_0(B_491))
      | ~ v1_funct_1(E_492)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(B_491)
      | ~ v2_pre_topc(B_491)
      | v2_struct_0(B_491)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_80,c_78,c_74,c_72,c_54,c_54,c_54,c_54,c_54,c_54,c_54,c_54,c_54,c_54,c_2144])).

tff(c_3323,plain,(
    ! [E_721,B_722] :
      ( v5_pre_topc(E_721,'#skF_1',B_722)
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_722,'#skF_1','#skF_4',E_721),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(B_722))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_722,'#skF_1','#skF_4',E_721),'#skF_4',B_722)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_722,'#skF_1','#skF_4',E_721),u1_struct_0('#skF_4'),u1_struct_0(B_722))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_722,'#skF_1','#skF_4',E_721))
      | ~ m1_subset_1(k3_tmap_1('#skF_1',B_722,'#skF_1','#skF_3',E_721),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(B_722))))
      | ~ v5_pre_topc(k3_tmap_1('#skF_1',B_722,'#skF_1','#skF_3',E_721),'#skF_3',B_722)
      | ~ v1_funct_2(k3_tmap_1('#skF_1',B_722,'#skF_1','#skF_3',E_721),u1_struct_0('#skF_3'),u1_struct_0(B_722))
      | ~ v1_funct_1(k3_tmap_1('#skF_1',B_722,'#skF_1','#skF_3',E_721))
      | ~ m1_subset_1(E_721,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0(B_722))))
      | ~ v1_funct_2(E_721,u1_struct_0('#skF_1'),u1_struct_0(B_722))
      | ~ v1_funct_1(E_721)
      | ~ l1_pre_topc(B_722)
      | ~ v2_pre_topc(B_722)
      | v2_struct_0(B_722) ) ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_82,c_76,c_2149])).

tff(c_3329,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1321,c_3323])).

tff(c_3336,plain,
    ( v5_pre_topc(k10_tmap_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_5','#skF_6'),'#skF_1','#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_282,c_849,c_607,c_70,c_1321,c_68,c_1321,c_66,c_1321,c_64,c_62,c_1165,c_60,c_1165,c_58,c_1165,c_56,c_1165,c_3329])).

tff(c_3338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_848,c_3336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:13:21 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.84/2.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/2.62  
% 7.84/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/2.62  %$ r2_funct_2 > v5_pre_topc > v1_funct_2 > v1_borsuk_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k10_tmap_1 > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.84/2.62  
% 7.84/2.62  %Foreground sorts:
% 7.84/2.62  
% 7.84/2.62  
% 7.84/2.62  %Background operators:
% 7.84/2.62  
% 7.84/2.62  
% 7.84/2.62  %Foreground operators:
% 7.84/2.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.84/2.62  tff(k10_tmap_1, type, k10_tmap_1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.84/2.62  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 7.84/2.62  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.84/2.62  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.84/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.84/2.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.84/2.62  tff('#skF_5', type, '#skF_5': $i).
% 7.84/2.62  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.84/2.62  tff('#skF_6', type, '#skF_6': $i).
% 7.84/2.62  tff('#skF_2', type, '#skF_2': $i).
% 7.84/2.62  tff('#skF_3', type, '#skF_3': $i).
% 7.84/2.62  tff('#skF_1', type, '#skF_1': $i).
% 7.84/2.62  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.84/2.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.84/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.84/2.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.84/2.62  tff('#skF_4', type, '#skF_4': $i).
% 7.84/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.84/2.62  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 7.84/2.62  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.84/2.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.84/2.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.84/2.62  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.84/2.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.84/2.62  tff(v1_borsuk_1, type, v1_borsuk_1: ($i * $i) > $o).
% 7.84/2.62  
% 7.84/2.66  tff(f_261, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_borsuk_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_borsuk_1(D, A)) & m1_pre_topc(D, A)) => (![E]: ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(E, C, B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: ((((v1_funct_1(F) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(F, D, B)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((((A = k1_tsep_1(A, C, D)) & r2_funct_2(u1_struct_0(C), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, k10_tmap_1(A, B, C, D, E, F)), E)) & r2_funct_2(u1_struct_0(D), u1_struct_0(B), k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, k10_tmap_1(A, B, C, D, E, F)), F)) => (((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(A), u1_struct_0(B))) & v5_pre_topc(k10_tmap_1(A, B, C, D, E, F), A, B)) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_tmap_1)).
% 7.84/2.66  tff(f_83, axiom, (![A, B, C, D, E, F]: ((((((((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) & ~v2_struct_0(D)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(F)) & v1_funct_2(F, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_funct_1(k10_tmap_1(A, B, C, D, E, F)) & v1_funct_2(k10_tmap_1(A, B, C, D, E, F), u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(k10_tmap_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_tmap_1)).
% 7.84/2.66  tff(f_105, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 7.84/2.66  tff(f_135, axiom, (![A, B, C, D, E]: (((((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v2_pre_topc(B)) & l1_pre_topc(B)) & m1_pre_topc(C, A)) & m1_pre_topc(D, A)) & v1_funct_1(E)) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => ((v1_funct_1(k3_tmap_1(A, B, C, D, E)) & v1_funct_2(k3_tmap_1(A, B, C, D, E), u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(k3_tmap_1(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_tmap_1)).
% 7.84/2.66  tff(f_41, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_funct_2(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 7.84/2.66  tff(f_197, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v1_borsuk_1(C, A)) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_borsuk_1(D, A)) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) => ((((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))) & v5_pre_topc(E, k1_tsep_1(A, C, D), B)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A, C, D)), u1_struct_0(B))))) <=> (((((((v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E)) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), u1_struct_0(C), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), C, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), C, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) & v1_funct_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E))) & v1_funct_2(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), u1_struct_0(D), u1_struct_0(B))) & v5_pre_topc(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), D, B)) & m1_subset_1(k3_tmap_1(A, B, k1_tsep_1(A, C, D), D, E), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_tmap_1)).
% 7.84/2.66  tff(c_88, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_86, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_84, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_68, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_60, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_56, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_94, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_82, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_76, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_92, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_90, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_78, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_72, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_54, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_511, plain, (![D_253, A_257, F_254, C_256, B_255, E_258]: (m1_subset_1(k10_tmap_1(A_257, B_255, C_256, D_253, E_258, F_254), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_257, C_256, D_253)), u1_struct_0(B_255)))) | ~m1_subset_1(F_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_253), u1_struct_0(B_255)))) | ~v1_funct_2(F_254, u1_struct_0(D_253), u1_struct_0(B_255)) | ~v1_funct_1(F_254) | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_256), u1_struct_0(B_255)))) | ~v1_funct_2(E_258, u1_struct_0(C_256), u1_struct_0(B_255)) | ~v1_funct_1(E_258) | ~m1_pre_topc(D_253, A_257) | v2_struct_0(D_253) | ~m1_pre_topc(C_256, A_257) | v2_struct_0(C_256) | ~l1_pre_topc(B_255) | ~v2_pre_topc(B_255) | v2_struct_0(B_255) | ~l1_pre_topc(A_257) | ~v2_pre_topc(A_257) | v2_struct_0(A_257))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.84/2.66  tff(c_536, plain, (![B_255, E_258, F_254]: (m1_subset_1(k10_tmap_1('#skF_1', B_255, '#skF_3', '#skF_4', E_258, F_254), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_255)))) | ~m1_subset_1(F_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_255)))) | ~v1_funct_2(F_254, u1_struct_0('#skF_4'), u1_struct_0(B_255)) | ~v1_funct_1(F_254) | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_255)))) | ~v1_funct_2(E_258, u1_struct_0('#skF_3'), u1_struct_0(B_255)) | ~v1_funct_1(E_258) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_255) | ~v2_pre_topc(B_255) | v2_struct_0(B_255) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_511])).
% 7.84/2.66  tff(c_554, plain, (![B_255, E_258, F_254]: (m1_subset_1(k10_tmap_1('#skF_1', B_255, '#skF_3', '#skF_4', E_258, F_254), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_255)))) | ~m1_subset_1(F_254, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_255)))) | ~v1_funct_2(F_254, u1_struct_0('#skF_4'), u1_struct_0(B_255)) | ~v1_funct_1(F_254) | ~m1_subset_1(E_258, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_255)))) | ~v1_funct_2(E_258, u1_struct_0('#skF_3'), u1_struct_0(B_255)) | ~v1_funct_1(E_258) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_255) | ~v2_pre_topc(B_255) | v2_struct_0(B_255) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_78, c_72, c_536])).
% 7.84/2.66  tff(c_556, plain, (![B_259, E_260, F_261]: (m1_subset_1(k10_tmap_1('#skF_1', B_259, '#skF_3', '#skF_4', E_260, F_261), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_259)))) | ~m1_subset_1(F_261, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_259)))) | ~v1_funct_2(F_261, u1_struct_0('#skF_4'), u1_struct_0(B_259)) | ~v1_funct_1(F_261) | ~m1_subset_1(E_260, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_259)))) | ~v1_funct_2(E_260, u1_struct_0('#skF_3'), u1_struct_0(B_259)) | ~v1_funct_1(E_260) | ~l1_pre_topc(B_259) | ~v2_pre_topc(B_259) | v2_struct_0(B_259))), inference(negUnitSimplification, [status(thm)], [c_94, c_82, c_76, c_554])).
% 7.84/2.66  tff(c_197, plain, (![E_151, B_148, A_150, D_146, C_149, F_147]: (v1_funct_1(k10_tmap_1(A_150, B_148, C_149, D_146, E_151, F_147)) | ~m1_subset_1(F_147, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_146), u1_struct_0(B_148)))) | ~v1_funct_2(F_147, u1_struct_0(D_146), u1_struct_0(B_148)) | ~v1_funct_1(F_147) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0(B_148)))) | ~v1_funct_2(E_151, u1_struct_0(C_149), u1_struct_0(B_148)) | ~v1_funct_1(E_151) | ~m1_pre_topc(D_146, A_150) | v2_struct_0(D_146) | ~m1_pre_topc(C_149, A_150) | v2_struct_0(C_149) | ~l1_pre_topc(B_148) | ~v2_pre_topc(B_148) | v2_struct_0(B_148) | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.84/2.66  tff(c_203, plain, (![A_150, C_149, E_151]: (v1_funct_1(k10_tmap_1(A_150, '#skF_2', C_149, '#skF_4', E_151, '#skF_6')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_151, u1_struct_0(C_149), u1_struct_0('#skF_2')) | ~v1_funct_1(E_151) | ~m1_pre_topc('#skF_4', A_150) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_149, A_150) | v2_struct_0(C_149) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(resolution, [status(thm)], [c_56, c_197])).
% 7.84/2.66  tff(c_211, plain, (![A_150, C_149, E_151]: (v1_funct_1(k10_tmap_1(A_150, '#skF_2', C_149, '#skF_4', E_151, '#skF_6')) | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_149), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_151, u1_struct_0(C_149), u1_struct_0('#skF_2')) | ~v1_funct_1(E_151) | ~m1_pre_topc('#skF_4', A_150) | v2_struct_0('#skF_4') | ~m1_pre_topc(C_149, A_150) | v2_struct_0(C_149) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_150) | ~v2_pre_topc(A_150) | v2_struct_0(A_150))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_62, c_60, c_203])).
% 7.84/2.66  tff(c_251, plain, (![A_164, C_165, E_166]: (v1_funct_1(k10_tmap_1(A_164, '#skF_2', C_165, '#skF_4', E_166, '#skF_6')) | ~m1_subset_1(E_166, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_165), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_166, u1_struct_0(C_165), u1_struct_0('#skF_2')) | ~v1_funct_1(E_166) | ~m1_pre_topc('#skF_4', A_164) | ~m1_pre_topc(C_165, A_164) | v2_struct_0(C_165) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(negUnitSimplification, [status(thm)], [c_88, c_76, c_211])).
% 7.84/2.66  tff(c_256, plain, (![A_164]: (v1_funct_1(k10_tmap_1(A_164, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_164) | ~m1_pre_topc('#skF_3', A_164) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_64, c_251])).
% 7.84/2.66  tff(c_265, plain, (![A_164]: (v1_funct_1(k10_tmap_1(A_164, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_164) | ~m1_pre_topc('#skF_3', A_164) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_256])).
% 7.84/2.66  tff(c_272, plain, (![A_168]: (v1_funct_1(k10_tmap_1(A_168, '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', A_168) | ~m1_pre_topc('#skF_3', A_168) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(negUnitSimplification, [status(thm)], [c_82, c_265])).
% 7.84/2.66  tff(c_48, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_126, plain, (~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_48])).
% 7.84/2.66  tff(c_275, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_272, c_126])).
% 7.84/2.66  tff(c_278, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_78, c_72, c_275])).
% 7.84/2.66  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_278])).
% 7.84/2.66  tff(c_281, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_48])).
% 7.84/2.66  tff(c_313, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_281])).
% 7.84/2.66  tff(c_581, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_556, c_313])).
% 7.84/2.66  tff(c_603, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_70, c_68, c_64, c_62, c_60, c_56, c_581])).
% 7.84/2.66  tff(c_605, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_603])).
% 7.84/2.66  tff(c_606, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_281])).
% 7.84/2.66  tff(c_613, plain, (~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_606])).
% 7.84/2.66  tff(c_802, plain, (![C_323, B_322, F_321, E_325, D_320, A_324]: (v1_funct_2(k10_tmap_1(A_324, B_322, C_323, D_320, E_325, F_321), u1_struct_0(k1_tsep_1(A_324, C_323, D_320)), u1_struct_0(B_322)) | ~m1_subset_1(F_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_320), u1_struct_0(B_322)))) | ~v1_funct_2(F_321, u1_struct_0(D_320), u1_struct_0(B_322)) | ~v1_funct_1(F_321) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_323), u1_struct_0(B_322)))) | ~v1_funct_2(E_325, u1_struct_0(C_323), u1_struct_0(B_322)) | ~v1_funct_1(E_325) | ~m1_pre_topc(D_320, A_324) | v2_struct_0(D_320) | ~m1_pre_topc(C_323, A_324) | v2_struct_0(C_323) | ~l1_pre_topc(B_322) | ~v2_pre_topc(B_322) | v2_struct_0(B_322) | ~l1_pre_topc(A_324) | ~v2_pre_topc(A_324) | v2_struct_0(A_324))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.84/2.66  tff(c_805, plain, (![B_322, E_325, F_321]: (v1_funct_2(k10_tmap_1('#skF_1', B_322, '#skF_3', '#skF_4', E_325, F_321), u1_struct_0('#skF_1'), u1_struct_0(B_322)) | ~m1_subset_1(F_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_322)))) | ~v1_funct_2(F_321, u1_struct_0('#skF_4'), u1_struct_0(B_322)) | ~v1_funct_1(F_321) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_322)))) | ~v1_funct_2(E_325, u1_struct_0('#skF_3'), u1_struct_0(B_322)) | ~v1_funct_1(E_325) | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_322) | ~v2_pre_topc(B_322) | v2_struct_0(B_322) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_802])).
% 7.84/2.66  tff(c_807, plain, (![B_322, E_325, F_321]: (v1_funct_2(k10_tmap_1('#skF_1', B_322, '#skF_3', '#skF_4', E_325, F_321), u1_struct_0('#skF_1'), u1_struct_0(B_322)) | ~m1_subset_1(F_321, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_322)))) | ~v1_funct_2(F_321, u1_struct_0('#skF_4'), u1_struct_0(B_322)) | ~v1_funct_1(F_321) | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_322)))) | ~v1_funct_2(E_325, u1_struct_0('#skF_3'), u1_struct_0(B_322)) | ~v1_funct_1(E_325) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_322) | ~v2_pre_topc(B_322) | v2_struct_0(B_322) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_78, c_72, c_805])).
% 7.84/2.66  tff(c_820, plain, (![B_328, E_329, F_330]: (v1_funct_2(k10_tmap_1('#skF_1', B_328, '#skF_3', '#skF_4', E_329, F_330), u1_struct_0('#skF_1'), u1_struct_0(B_328)) | ~m1_subset_1(F_330, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_328)))) | ~v1_funct_2(F_330, u1_struct_0('#skF_4'), u1_struct_0(B_328)) | ~v1_funct_1(F_330) | ~m1_subset_1(E_329, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_328)))) | ~v1_funct_2(E_329, u1_struct_0('#skF_3'), u1_struct_0(B_328)) | ~v1_funct_1(E_329) | ~l1_pre_topc(B_328) | ~v2_pre_topc(B_328) | v2_struct_0(B_328))), inference(negUnitSimplification, [status(thm)], [c_94, c_82, c_76, c_807])).
% 7.84/2.66  tff(c_825, plain, (![E_329]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_329, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_329, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_329, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_329) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_56, c_820])).
% 7.84/2.66  tff(c_829, plain, (![E_329]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_329, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_329, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_329, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_329) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_62, c_60, c_825])).
% 7.84/2.66  tff(c_831, plain, (![E_331]: (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', E_331, '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~m1_subset_1(E_331, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(E_331, u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(E_331))), inference(negUnitSimplification, [status(thm)], [c_88, c_829])).
% 7.84/2.66  tff(c_838, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_831])).
% 7.84/2.66  tff(c_845, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_838])).
% 7.84/2.66  tff(c_847, plain, $false, inference(negUnitSimplification, [status(thm)], [c_613, c_845])).
% 7.84/2.66  tff(c_848, plain, (~v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_606])).
% 7.84/2.66  tff(c_282, plain, (v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_48])).
% 7.84/2.66  tff(c_849, plain, (v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_606])).
% 7.84/2.66  tff(c_607, plain, (m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(splitRight, [status(thm)], [c_281])).
% 7.84/2.66  tff(c_283, plain, (![A_169, B_170, C_171]: (m1_pre_topc(k1_tsep_1(A_169, B_170, C_171), A_169) | ~m1_pre_topc(C_171, A_169) | v2_struct_0(C_171) | ~m1_pre_topc(B_170, A_169) | v2_struct_0(B_170) | ~l1_pre_topc(A_169) | v2_struct_0(A_169))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.84/2.66  tff(c_286, plain, (m1_pre_topc('#skF_1', '#skF_1') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_54, c_283])).
% 7.84/2.66  tff(c_288, plain, (m1_pre_topc('#skF_1', '#skF_1') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_78, c_72, c_286])).
% 7.84/2.66  tff(c_289, plain, (m1_pre_topc('#skF_1', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_94, c_82, c_76, c_288])).
% 7.84/2.66  tff(c_879, plain, (![B_344, E_341, C_343, D_342, A_345]: (v1_funct_2(k3_tmap_1(A_345, B_344, C_343, D_342, E_341), u1_struct_0(D_342), u1_struct_0(B_344)) | ~m1_subset_1(E_341, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_343), u1_struct_0(B_344)))) | ~v1_funct_2(E_341, u1_struct_0(C_343), u1_struct_0(B_344)) | ~v1_funct_1(E_341) | ~m1_pre_topc(D_342, A_345) | ~m1_pre_topc(C_343, A_345) | ~l1_pre_topc(B_344) | ~v2_pre_topc(B_344) | v2_struct_0(B_344) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.84/2.66  tff(c_881, plain, (![A_345, D_342]: (v1_funct_2(k3_tmap_1(A_345, '#skF_2', '#skF_1', D_342, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_342), u1_struct_0('#skF_2')) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_342, A_345) | ~m1_pre_topc('#skF_1', A_345) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(resolution, [status(thm)], [c_607, c_879])).
% 7.84/2.66  tff(c_888, plain, (![A_345, D_342]: (v1_funct_2(k3_tmap_1(A_345, '#skF_2', '#skF_1', D_342, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_342), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_342, A_345) | ~m1_pre_topc('#skF_1', A_345) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_282, c_849, c_881])).
% 7.84/2.66  tff(c_889, plain, (![A_345, D_342]: (v1_funct_2(k3_tmap_1(A_345, '#skF_2', '#skF_1', D_342, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0(D_342), u1_struct_0('#skF_2')) | ~m1_pre_topc(D_342, A_345) | ~m1_pre_topc('#skF_1', A_345) | ~l1_pre_topc(A_345) | ~v2_pre_topc(A_345) | v2_struct_0(A_345))), inference(negUnitSimplification, [status(thm)], [c_88, c_888])).
% 7.84/2.66  tff(c_18, plain, (![E_18, C_16, D_17, A_14, B_15]: (m1_subset_1(k3_tmap_1(A_14, B_15, C_16, D_17, E_18), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_17), u1_struct_0(B_15)))) | ~m1_subset_1(E_18, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_16), u1_struct_0(B_15)))) | ~v1_funct_2(E_18, u1_struct_0(C_16), u1_struct_0(B_15)) | ~v1_funct_1(E_18) | ~m1_pre_topc(D_17, A_14) | ~m1_pre_topc(C_16, A_14) | ~l1_pre_topc(B_15) | ~v2_pre_topc(B_15) | v2_struct_0(B_15) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.84/2.66  tff(c_858, plain, (![C_334, A_336, D_333, B_335, E_332]: (v1_funct_1(k3_tmap_1(A_336, B_335, C_334, D_333, E_332)) | ~m1_subset_1(E_332, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_334), u1_struct_0(B_335)))) | ~v1_funct_2(E_332, u1_struct_0(C_334), u1_struct_0(B_335)) | ~v1_funct_1(E_332) | ~m1_pre_topc(D_333, A_336) | ~m1_pre_topc(C_334, A_336) | ~l1_pre_topc(B_335) | ~v2_pre_topc(B_335) | v2_struct_0(B_335) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(cnfTransformation, [status(thm)], [f_135])).
% 7.84/2.66  tff(c_860, plain, (![A_336, D_333]: (v1_funct_1(k3_tmap_1(A_336, '#skF_2', '#skF_1', D_333, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc(D_333, A_336) | ~m1_pre_topc('#skF_1', A_336) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(resolution, [status(thm)], [c_607, c_858])).
% 7.84/2.66  tff(c_867, plain, (![A_336, D_333]: (v1_funct_1(k3_tmap_1(A_336, '#skF_2', '#skF_1', D_333, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_333, A_336) | ~m1_pre_topc('#skF_1', A_336) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_282, c_849, c_860])).
% 7.84/2.66  tff(c_868, plain, (![A_336, D_333]: (v1_funct_1(k3_tmap_1(A_336, '#skF_2', '#skF_1', D_333, k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_pre_topc(D_333, A_336) | ~m1_pre_topc('#skF_1', A_336) | ~l1_pre_topc(A_336) | ~v2_pre_topc(A_336) | v2_struct_0(A_336))), inference(negUnitSimplification, [status(thm)], [c_88, c_867])).
% 7.84/2.66  tff(c_52, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_95, plain, (r2_funct_2(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52])).
% 7.84/2.66  tff(c_290, plain, (![D_172, C_173, A_174, B_175]: (D_172=C_173 | ~r2_funct_2(A_174, B_175, C_173, D_172) | ~m1_subset_1(D_172, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_2(D_172, A_174, B_175) | ~v1_funct_1(D_172) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_174, B_175))) | ~v1_funct_2(C_173, A_174, B_175) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.84/2.66  tff(c_294, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_95, c_290])).
% 7.84/2.66  tff(c_304, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_294])).
% 7.84/2.66  tff(c_1242, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_304])).
% 7.84/2.66  tff(c_1245, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_868, c_1242])).
% 7.84/2.66  tff(c_1248, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_289, c_78, c_1245])).
% 7.84/2.66  tff(c_1250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_1248])).
% 7.84/2.66  tff(c_1251, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_304])).
% 7.84/2.66  tff(c_1253, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1251])).
% 7.84/2.66  tff(c_1256, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1253])).
% 7.84/2.66  tff(c_1259, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_86, c_84, c_289, c_78, c_282, c_849, c_607, c_1256])).
% 7.84/2.66  tff(c_1261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_1259])).
% 7.84/2.66  tff(c_1262, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1251])).
% 7.84/2.66  tff(c_1312, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1262])).
% 7.84/2.66  tff(c_1315, plain, (~m1_pre_topc('#skF_3', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_889, c_1312])).
% 7.84/2.66  tff(c_1318, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_289, c_78, c_1315])).
% 7.84/2.66  tff(c_1320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_1318])).
% 7.84/2.66  tff(c_1321, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_1262])).
% 7.84/2.66  tff(c_66, plain, (v5_pre_topc('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_50, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_96, plain, (r2_funct_2(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50])).
% 7.84/2.66  tff(c_292, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_96, c_290])).
% 7.84/2.66  tff(c_301, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_292])).
% 7.84/2.66  tff(c_1067, plain, (~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_301])).
% 7.84/2.66  tff(c_1086, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_868, c_1067])).
% 7.84/2.66  tff(c_1089, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_289, c_72, c_1086])).
% 7.84/2.66  tff(c_1091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_1089])).
% 7.84/2.66  tff(c_1092, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_301])).
% 7.84/2.66  tff(c_1094, plain, (~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(splitLeft, [status(thm)], [c_1092])).
% 7.84/2.66  tff(c_1097, plain, (~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_18, c_1094])).
% 7.84/2.66  tff(c_1100, plain, (v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_86, c_84, c_289, c_72, c_282, c_849, c_607, c_1097])).
% 7.84/2.66  tff(c_1102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_88, c_1100])).
% 7.84/2.66  tff(c_1103, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1092])).
% 7.84/2.66  tff(c_1156, plain, (~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_1103])).
% 7.84/2.66  tff(c_1159, plain, (~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_1', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_889, c_1156])).
% 7.84/2.66  tff(c_1162, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_289, c_72, c_1159])).
% 7.84/2.66  tff(c_1164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_1162])).
% 7.84/2.66  tff(c_1165, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(splitRight, [status(thm)], [c_1103])).
% 7.84/2.66  tff(c_58, plain, (v5_pre_topc('#skF_6', '#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_80, plain, (v1_borsuk_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_74, plain, (v1_borsuk_1('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_261])).
% 7.84/2.66  tff(c_2134, plain, (![B_491, C_488, D_489, E_492, A_490]: (v5_pre_topc(E_492, k1_tsep_1(A_490, C_488, D_489), B_491) | ~m1_subset_1(k3_tmap_1(A_490, B_491, k1_tsep_1(A_490, C_488, D_489), D_489, E_492), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_489), u1_struct_0(B_491)))) | ~v5_pre_topc(k3_tmap_1(A_490, B_491, k1_tsep_1(A_490, C_488, D_489), D_489, E_492), D_489, B_491) | ~v1_funct_2(k3_tmap_1(A_490, B_491, k1_tsep_1(A_490, C_488, D_489), D_489, E_492), u1_struct_0(D_489), u1_struct_0(B_491)) | ~v1_funct_1(k3_tmap_1(A_490, B_491, k1_tsep_1(A_490, C_488, D_489), D_489, E_492)) | ~m1_subset_1(k3_tmap_1(A_490, B_491, k1_tsep_1(A_490, C_488, D_489), C_488, E_492), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_488), u1_struct_0(B_491)))) | ~v5_pre_topc(k3_tmap_1(A_490, B_491, k1_tsep_1(A_490, C_488, D_489), C_488, E_492), C_488, B_491) | ~v1_funct_2(k3_tmap_1(A_490, B_491, k1_tsep_1(A_490, C_488, D_489), C_488, E_492), u1_struct_0(C_488), u1_struct_0(B_491)) | ~v1_funct_1(k3_tmap_1(A_490, B_491, k1_tsep_1(A_490, C_488, D_489), C_488, E_492)) | ~m1_subset_1(E_492, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(A_490, C_488, D_489)), u1_struct_0(B_491)))) | ~v1_funct_2(E_492, u1_struct_0(k1_tsep_1(A_490, C_488, D_489)), u1_struct_0(B_491)) | ~v1_funct_1(E_492) | ~m1_pre_topc(D_489, A_490) | ~v1_borsuk_1(D_489, A_490) | v2_struct_0(D_489) | ~m1_pre_topc(C_488, A_490) | ~v1_borsuk_1(C_488, A_490) | v2_struct_0(C_488) | ~l1_pre_topc(B_491) | ~v2_pre_topc(B_491) | v2_struct_0(B_491) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(cnfTransformation, [status(thm)], [f_197])).
% 7.84/2.66  tff(c_2144, plain, (![E_492, B_491]: (v5_pre_topc(E_492, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), B_491) | ~m1_subset_1(k3_tmap_1('#skF_1', B_491, '#skF_1', '#skF_4', E_492), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_491)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_491, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_492), '#skF_4', B_491) | ~v1_funct_2(k3_tmap_1('#skF_1', B_491, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_492), u1_struct_0('#skF_4'), u1_struct_0(B_491)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_491, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_4', E_492)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_491, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_492), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_491)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_491, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_492), '#skF_3', B_491) | ~v1_funct_2(k3_tmap_1('#skF_1', B_491, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_492), u1_struct_0('#skF_3'), u1_struct_0(B_491)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_491, k1_tsep_1('#skF_1', '#skF_3', '#skF_4'), '#skF_3', E_492)) | ~m1_subset_1(E_492, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_491)))) | ~v1_funct_2(E_492, u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_4')), u1_struct_0(B_491)) | ~v1_funct_1(E_492) | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_borsuk_1('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | ~v1_borsuk_1('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_491) | ~v2_pre_topc(B_491) | v2_struct_0(B_491) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_2134])).
% 7.84/2.66  tff(c_2149, plain, (![E_492, B_491]: (v5_pre_topc(E_492, '#skF_1', B_491) | ~m1_subset_1(k3_tmap_1('#skF_1', B_491, '#skF_1', '#skF_4', E_492), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_491)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_491, '#skF_1', '#skF_4', E_492), '#skF_4', B_491) | ~v1_funct_2(k3_tmap_1('#skF_1', B_491, '#skF_1', '#skF_4', E_492), u1_struct_0('#skF_4'), u1_struct_0(B_491)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_491, '#skF_1', '#skF_4', E_492)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_491, '#skF_1', '#skF_3', E_492), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_491)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_491, '#skF_1', '#skF_3', E_492), '#skF_3', B_491) | ~v1_funct_2(k3_tmap_1('#skF_1', B_491, '#skF_1', '#skF_3', E_492), u1_struct_0('#skF_3'), u1_struct_0(B_491)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_491, '#skF_1', '#skF_3', E_492)) | ~m1_subset_1(E_492, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_491)))) | ~v1_funct_2(E_492, u1_struct_0('#skF_1'), u1_struct_0(B_491)) | ~v1_funct_1(E_492) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | ~l1_pre_topc(B_491) | ~v2_pre_topc(B_491) | v2_struct_0(B_491) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_80, c_78, c_74, c_72, c_54, c_54, c_54, c_54, c_54, c_54, c_54, c_54, c_54, c_54, c_2144])).
% 7.84/2.66  tff(c_3323, plain, (![E_721, B_722]: (v5_pre_topc(E_721, '#skF_1', B_722) | ~m1_subset_1(k3_tmap_1('#skF_1', B_722, '#skF_1', '#skF_4', E_721), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(B_722)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_722, '#skF_1', '#skF_4', E_721), '#skF_4', B_722) | ~v1_funct_2(k3_tmap_1('#skF_1', B_722, '#skF_1', '#skF_4', E_721), u1_struct_0('#skF_4'), u1_struct_0(B_722)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_722, '#skF_1', '#skF_4', E_721)) | ~m1_subset_1(k3_tmap_1('#skF_1', B_722, '#skF_1', '#skF_3', E_721), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(B_722)))) | ~v5_pre_topc(k3_tmap_1('#skF_1', B_722, '#skF_1', '#skF_3', E_721), '#skF_3', B_722) | ~v1_funct_2(k3_tmap_1('#skF_1', B_722, '#skF_1', '#skF_3', E_721), u1_struct_0('#skF_3'), u1_struct_0(B_722)) | ~v1_funct_1(k3_tmap_1('#skF_1', B_722, '#skF_1', '#skF_3', E_721)) | ~m1_subset_1(E_721, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0(B_722)))) | ~v1_funct_2(E_721, u1_struct_0('#skF_1'), u1_struct_0(B_722)) | ~v1_funct_1(E_721) | ~l1_pre_topc(B_722) | ~v2_pre_topc(B_722) | v2_struct_0(B_722))), inference(negUnitSimplification, [status(thm)], [c_94, c_82, c_76, c_2149])).
% 7.84/2.66  tff(c_3329, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | ~m1_subset_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_4', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_4', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_2')))) | ~v5_pre_topc(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), '#skF_3', '#skF_2') | ~v1_funct_2(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')), u1_struct_0('#skF_3'), u1_struct_0('#skF_2')) | ~v1_funct_1(k3_tmap_1('#skF_1', '#skF_2', '#skF_1', '#skF_3', k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'))) | ~m1_subset_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2')))) | ~v1_funct_2(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), u1_struct_0('#skF_1'), u1_struct_0('#skF_2')) | ~v1_funct_1(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1321, c_3323])).
% 7.84/2.66  tff(c_3336, plain, (v5_pre_topc(k10_tmap_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_6'), '#skF_1', '#skF_2') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_282, c_849, c_607, c_70, c_1321, c_68, c_1321, c_66, c_1321, c_64, c_62, c_1165, c_60, c_1165, c_58, c_1165, c_56, c_1165, c_3329])).
% 7.84/2.66  tff(c_3338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_848, c_3336])).
% 7.84/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.84/2.66  
% 7.84/2.66  Inference rules
% 7.84/2.66  ----------------------
% 7.84/2.66  #Ref     : 0
% 7.84/2.66  #Sup     : 547
% 7.84/2.66  #Fact    : 0
% 7.84/2.66  #Define  : 0
% 7.84/2.66  #Split   : 14
% 7.84/2.66  #Chain   : 0
% 7.84/2.66  #Close   : 0
% 7.84/2.66  
% 7.84/2.66  Ordering : KBO
% 7.84/2.66  
% 7.84/2.66  Simplification rules
% 7.84/2.66  ----------------------
% 7.84/2.66  #Subsume      : 90
% 7.84/2.66  #Demod        : 1776
% 7.84/2.66  #Tautology    : 56
% 7.84/2.66  #SimpNegUnit  : 344
% 7.84/2.66  #BackRed      : 9
% 7.84/2.66  
% 7.84/2.66  #Partial instantiations: 0
% 7.84/2.66  #Strategies tried      : 1
% 7.84/2.66  
% 7.84/2.66  Timing (in seconds)
% 7.84/2.66  ----------------------
% 7.84/2.66  Preprocessing        : 0.42
% 7.84/2.66  Parsing              : 0.21
% 7.84/2.66  CNF conversion       : 0.06
% 7.84/2.66  Main loop            : 1.43
% 7.84/2.66  Inferencing          : 0.48
% 7.84/2.66  Reduction            : 0.45
% 7.84/2.66  Demodulation         : 0.34
% 7.84/2.66  BG Simplification    : 0.06
% 7.84/2.66  Subsumption          : 0.38
% 7.84/2.66  Abstraction          : 0.07
% 7.84/2.66  MUC search           : 0.00
% 7.84/2.66  Cooper               : 0.00
% 7.84/2.66  Total                : 1.91
% 7.84/2.66  Index Insertion      : 0.00
% 7.84/2.66  Index Deletion       : 0.00
% 7.84/2.66  Index Matching       : 0.00
% 7.84/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
