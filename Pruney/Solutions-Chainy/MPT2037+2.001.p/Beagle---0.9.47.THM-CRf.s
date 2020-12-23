%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:21 EST 2020

% Result     : Theorem 10.95s
% Output     : CNFRefutation 11.27s
% Verified   : 
% Statistics : Number of formulae       :  179 (1683 expanded)
%              Number of leaves         :   56 ( 714 expanded)
%              Depth                    :   28
%              Number of atoms          : 1032 (15697 expanded)
%              Number of equality atoms :   48 ( 789 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r3_waybel_9 > r1_orders_2 > r1_lattice3 > v11_waybel_0 > r2_yellow_0 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_relat_1 > v1_lattice3 > v1_funct_1 > v1_compts_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k5_yellow_2 > k4_waybel_1 > k2_zfmisc_1 > k2_yellow_0 > k1_waybel_9 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k5_yellow_2,type,(
    k5_yellow_2: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(v11_waybel_0,type,(
    v11_waybel_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k4_waybel_1,type,(
    k4_waybel_1: ( $i * $i ) > $i )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_waybel_9,type,(
    k1_waybel_9: ( $i * $i ) > $i )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_254,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & v8_pre_topc(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & v1_lattice3(A)
          & v2_lattice3(A)
          & v1_compts_1(A)
          & l1_waybel_9(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v4_orders_2(C)
                  & v7_waybel_0(C)
                  & l1_waybel_0(C,A) )
               => ( ( ! [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                       => v5_pre_topc(k4_waybel_1(A,D),A,A) )
                    & v11_waybel_0(C,A)
                    & r3_waybel_9(A,C,B) )
                 => B = k1_waybel_9(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_9)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_37,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( l1_struct_0(A)
        & l1_waybel_0(B,A) )
     => ( v1_funct_1(u1_waybel_0(A,B))
        & v1_funct_2(u1_waybel_0(A,B),u1_struct_0(B),u1_struct_0(A))
        & m1_subset_1(u1_waybel_0(A,B),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_waybel_0)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_161,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & v8_pre_topc(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v1_compts_1(A)
        & l1_waybel_9(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( C = D
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => v5_pre_topc(k4_waybel_1(A,E),A,A) )
                      & v11_waybel_0(B,A)
                      & r3_waybel_9(A,B,C) )
                   => r1_lattice3(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B)),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_waybel_9)).

tff(f_98,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( l1_waybel_0(B,A)
         => k1_waybel_9(A,B) = k5_yellow_2(A,u1_waybel_0(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_9)).

tff(f_108,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( v1_relat_1(B)
         => k5_yellow_2(A,B) = k2_yellow_0(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_yellow_2)).

tff(f_78,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) )
               => ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) ) )
              & ( ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) )
               => ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_211,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & v8_pre_topc(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & v1_compts_1(A)
        & l1_waybel_9(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( ( C = D
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => v5_pre_topc(k4_waybel_1(A,E),A,A) )
                      & r3_waybel_9(A,B,C) )
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(A))
                       => ( r1_lattice3(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B)),E)
                         => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l52_waybel_9)).

tff(c_66,plain,(
    l1_waybel_9('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_83,plain,(
    ! [A_128] :
      ( l1_orders_2(A_128)
      | ~ l1_waybel_9(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_87,plain,(
    l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_83])).

tff(c_72,plain,(
    v1_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_74,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_6,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    ! [A_145,B_146] :
      ( m1_subset_1(u1_waybel_0(A_145,B_146),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_146),u1_struct_0(A_145))))
      | ~ l1_waybel_0(B_146,A_145)
      | ~ l1_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( k2_relset_1(A_4,B_5,C_6) = k2_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_116,plain,(
    ! [B_146,A_145] :
      ( k2_relset_1(u1_struct_0(B_146),u1_struct_0(A_145),u1_waybel_0(A_145,B_146)) = k2_relat_1(u1_waybel_0(A_145,B_146))
      | ~ l1_waybel_0(B_146,A_145)
      | ~ l1_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_82,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_80,plain,(
    v8_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_78,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_76,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_70,plain,(
    v2_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_68,plain,(
    v1_compts_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_42,plain,(
    ! [A_40,B_56,D_68] :
      ( m1_subset_1('#skF_2'(A_40,B_56,D_68,D_68),u1_struct_0(A_40))
      | r1_lattice3(A_40,k2_relset_1(u1_struct_0(B_56),u1_struct_0(A_40),u1_waybel_0(A_40,B_56)),D_68)
      | ~ r3_waybel_9(A_40,B_56,D_68)
      | ~ v11_waybel_0(B_56,A_40)
      | ~ m1_subset_1(D_68,u1_struct_0(A_40))
      | ~ l1_waybel_0(B_56,A_40)
      | ~ v7_waybel_0(B_56)
      | ~ v4_orders_2(B_56)
      | v2_struct_0(B_56)
      | ~ l1_waybel_9(A_40)
      | ~ v1_compts_1(A_40)
      | ~ v2_lattice3(A_40)
      | ~ v1_lattice3(A_40)
      | ~ v5_orders_2(A_40)
      | ~ v4_orders_2(A_40)
      | ~ v3_orders_2(A_40)
      | ~ v8_pre_topc(A_40)
      | ~ v2_pre_topc(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_54,plain,(
    ! [D_127] :
      ( v5_pre_topc(k4_waybel_1('#skF_4',D_127),'#skF_4','#skF_4')
      | ~ m1_subset_1(D_127,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_197,plain,(
    ! [A_197,B_198,D_199] :
      ( ~ v5_pre_topc(k4_waybel_1(A_197,'#skF_2'(A_197,B_198,D_199,D_199)),A_197,A_197)
      | r1_lattice3(A_197,k2_relset_1(u1_struct_0(B_198),u1_struct_0(A_197),u1_waybel_0(A_197,B_198)),D_199)
      | ~ r3_waybel_9(A_197,B_198,D_199)
      | ~ v11_waybel_0(B_198,A_197)
      | ~ m1_subset_1(D_199,u1_struct_0(A_197))
      | ~ l1_waybel_0(B_198,A_197)
      | ~ v7_waybel_0(B_198)
      | ~ v4_orders_2(B_198)
      | v2_struct_0(B_198)
      | ~ l1_waybel_9(A_197)
      | ~ v1_compts_1(A_197)
      | ~ v2_lattice3(A_197)
      | ~ v1_lattice3(A_197)
      | ~ v5_orders_2(A_197)
      | ~ v4_orders_2(A_197)
      | ~ v3_orders_2(A_197)
      | ~ v8_pre_topc(A_197)
      | ~ v2_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_200,plain,(
    ! [B_198,D_199] :
      ( r1_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_198),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_198)),D_199)
      | ~ r3_waybel_9('#skF_4',B_198,D_199)
      | ~ v11_waybel_0(B_198,'#skF_4')
      | ~ m1_subset_1(D_199,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_198,'#skF_4')
      | ~ v7_waybel_0(B_198)
      | ~ v4_orders_2(B_198)
      | v2_struct_0(B_198)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_198,D_199,D_199),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_197])).

tff(c_204,plain,(
    ! [B_200,D_201] :
      ( r1_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_200),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_200)),D_201)
      | ~ r3_waybel_9('#skF_4',B_200,D_201)
      | ~ v11_waybel_0(B_200,'#skF_4')
      | ~ m1_subset_1(D_201,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_200,'#skF_4')
      | ~ v7_waybel_0(B_200)
      | ~ v4_orders_2(B_200)
      | v2_struct_0(B_200)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_200,D_201,D_201),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_200])).

tff(c_210,plain,(
    ! [B_56,D_68] :
      ( r1_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_56),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_56)),D_68)
      | ~ r3_waybel_9('#skF_4',B_56,D_68)
      | ~ v11_waybel_0(B_56,'#skF_4')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_56,'#skF_4')
      | ~ v7_waybel_0(B_56)
      | ~ v4_orders_2(B_56)
      | v2_struct_0(B_56)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_42,c_204])).

tff(c_217,plain,(
    ! [B_202,D_203] :
      ( r1_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_202),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_202)),D_203)
      | ~ r3_waybel_9('#skF_4',B_202,D_203)
      | ~ v11_waybel_0(B_202,'#skF_4')
      | ~ m1_subset_1(D_203,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_202,'#skF_4')
      | ~ v7_waybel_0(B_202)
      | ~ v4_orders_2(B_202)
      | v2_struct_0(B_202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_210])).

tff(c_221,plain,(
    ! [B_146,D_203] :
      ( r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_146)),D_203)
      | ~ r3_waybel_9('#skF_4',B_146,D_203)
      | ~ v11_waybel_0(B_146,'#skF_4')
      | ~ m1_subset_1(D_203,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_146,'#skF_4')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ l1_waybel_0(B_146,'#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_217])).

tff(c_222,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_225,plain,(
    ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_222])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_225])).

tff(c_230,plain,(
    ! [B_146,D_203] :
      ( r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_146)),D_203)
      | ~ r3_waybel_9('#skF_4',B_146,D_203)
      | ~ v11_waybel_0(B_146,'#skF_4')
      | ~ m1_subset_1(D_203,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_146,'#skF_4')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ l1_waybel_0(B_146,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_32,plain,(
    ! [A_33,B_35] :
      ( k5_yellow_2(A_33,u1_waybel_0(A_33,B_35)) = k1_waybel_9(A_33,B_35)
      | ~ l1_waybel_0(B_35,A_33)
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    ! [A_36,B_38] :
      ( k2_yellow_0(A_36,k2_relat_1(B_38)) = k5_yellow_2(A_36,B_38)
      | ~ v1_relat_1(B_38)
      | ~ l1_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_146,plain,(
    ! [A_173,D_174,C_175] :
      ( r1_orders_2(A_173,D_174,k2_yellow_0(A_173,C_175))
      | ~ r1_lattice3(A_173,C_175,D_174)
      | ~ m1_subset_1(D_174,u1_struct_0(A_173))
      | ~ r2_yellow_0(A_173,C_175)
      | ~ m1_subset_1(k2_yellow_0(A_173,C_175),u1_struct_0(A_173))
      | ~ l1_orders_2(A_173)
      | ~ v5_orders_2(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_157,plain,(
    ! [A_180,D_181,B_182] :
      ( r1_orders_2(A_180,D_181,k2_yellow_0(A_180,k2_relat_1(B_182)))
      | ~ r1_lattice3(A_180,k2_relat_1(B_182),D_181)
      | ~ m1_subset_1(D_181,u1_struct_0(A_180))
      | ~ r2_yellow_0(A_180,k2_relat_1(B_182))
      | ~ m1_subset_1(k5_yellow_2(A_180,B_182),u1_struct_0(A_180))
      | ~ l1_orders_2(A_180)
      | ~ v5_orders_2(A_180)
      | ~ v1_relat_1(B_182)
      | ~ l1_orders_2(A_180)
      | v2_struct_0(A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_146])).

tff(c_171,plain,(
    ! [A_183,D_184,B_185] :
      ( r1_orders_2(A_183,D_184,k5_yellow_2(A_183,B_185))
      | ~ r1_lattice3(A_183,k2_relat_1(B_185),D_184)
      | ~ m1_subset_1(D_184,u1_struct_0(A_183))
      | ~ r2_yellow_0(A_183,k2_relat_1(B_185))
      | ~ m1_subset_1(k5_yellow_2(A_183,B_185),u1_struct_0(A_183))
      | ~ l1_orders_2(A_183)
      | ~ v5_orders_2(A_183)
      | ~ v1_relat_1(B_185)
      | ~ l1_orders_2(A_183)
      | v2_struct_0(A_183)
      | ~ v1_relat_1(B_185)
      | ~ l1_orders_2(A_183)
      | v2_struct_0(A_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_157])).

tff(c_269,plain,(
    ! [A_214,D_215,B_216] :
      ( r1_orders_2(A_214,D_215,k5_yellow_2(A_214,u1_waybel_0(A_214,B_216)))
      | ~ r1_lattice3(A_214,k2_relat_1(u1_waybel_0(A_214,B_216)),D_215)
      | ~ m1_subset_1(D_215,u1_struct_0(A_214))
      | ~ r2_yellow_0(A_214,k2_relat_1(u1_waybel_0(A_214,B_216)))
      | ~ m1_subset_1(k1_waybel_9(A_214,B_216),u1_struct_0(A_214))
      | ~ l1_orders_2(A_214)
      | ~ v5_orders_2(A_214)
      | ~ v1_relat_1(u1_waybel_0(A_214,B_216))
      | ~ l1_orders_2(A_214)
      | v2_struct_0(A_214)
      | ~ v1_relat_1(u1_waybel_0(A_214,B_216))
      | ~ l1_orders_2(A_214)
      | v2_struct_0(A_214)
      | ~ l1_waybel_0(B_216,A_214)
      | ~ l1_orders_2(A_214)
      | v2_struct_0(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_171])).

tff(c_354,plain,(
    ! [A_227,D_228,B_229] :
      ( r1_orders_2(A_227,D_228,k1_waybel_9(A_227,B_229))
      | ~ r1_lattice3(A_227,k2_relat_1(u1_waybel_0(A_227,B_229)),D_228)
      | ~ m1_subset_1(D_228,u1_struct_0(A_227))
      | ~ r2_yellow_0(A_227,k2_relat_1(u1_waybel_0(A_227,B_229)))
      | ~ m1_subset_1(k1_waybel_9(A_227,B_229),u1_struct_0(A_227))
      | ~ l1_orders_2(A_227)
      | ~ v5_orders_2(A_227)
      | ~ v1_relat_1(u1_waybel_0(A_227,B_229))
      | ~ l1_orders_2(A_227)
      | v2_struct_0(A_227)
      | ~ v1_relat_1(u1_waybel_0(A_227,B_229))
      | ~ l1_orders_2(A_227)
      | v2_struct_0(A_227)
      | ~ l1_waybel_0(B_229,A_227)
      | ~ l1_orders_2(A_227)
      | v2_struct_0(A_227)
      | ~ l1_waybel_0(B_229,A_227)
      | ~ l1_orders_2(A_227)
      | v2_struct_0(A_227) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_269])).

tff(c_357,plain,(
    ! [D_203,B_146] :
      ( r1_orders_2('#skF_4',D_203,k1_waybel_9('#skF_4',B_146))
      | ~ r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_146)))
      | ~ m1_subset_1(k1_waybel_9('#skF_4',B_146),u1_struct_0('#skF_4'))
      | ~ v5_orders_2('#skF_4')
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_146))
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_146,D_203)
      | ~ v11_waybel_0(B_146,'#skF_4')
      | ~ m1_subset_1(D_203,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ l1_waybel_0(B_146,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_230,c_354])).

tff(c_382,plain,(
    ! [D_203,B_146] :
      ( r1_orders_2('#skF_4',D_203,k1_waybel_9('#skF_4',B_146))
      | ~ r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_146)))
      | ~ m1_subset_1(k1_waybel_9('#skF_4',B_146),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_146))
      | v2_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_146,D_203)
      | ~ v11_waybel_0(B_146,'#skF_4')
      | ~ m1_subset_1(D_203,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ l1_waybel_0(B_146,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_74,c_357])).

tff(c_573,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_8,plain,(
    ! [A_8] :
      ( ~ v2_struct_0(A_8)
      | ~ v1_lattice3(A_8)
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_576,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_573,c_8])).

tff(c_580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_72,c_576])).

tff(c_582,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_48,plain,(
    k1_waybel_9('#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_56,plain,(
    l1_waybel_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_231,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    ! [A_145,B_146] :
      ( v1_relat_1(u1_waybel_0(A_145,B_146))
      | ~ l1_waybel_0(B_146,A_145)
      | ~ l1_struct_0(A_145) ) ),
    inference(resolution,[status(thm)],[c_109,c_2])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_60,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_58,plain,(
    v7_waybel_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_52,plain,(
    v11_waybel_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_50,plain,(
    r3_waybel_9('#skF_4','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_216,plain,(
    ! [B_56,D_68] :
      ( r1_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_56),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_56)),D_68)
      | ~ r3_waybel_9('#skF_4',B_56,D_68)
      | ~ v11_waybel_0(B_56,'#skF_4')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_56,'#skF_4')
      | ~ v7_waybel_0(B_56)
      | ~ v4_orders_2(B_56)
      | v2_struct_0(B_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_210])).

tff(c_18,plain,(
    ! [A_9,B_21,C_27] :
      ( m1_subset_1('#skF_1'(A_9,B_21,C_27),u1_struct_0(A_9))
      | r2_yellow_0(A_9,C_27)
      | ~ r1_lattice3(A_9,C_27,B_21)
      | ~ m1_subset_1(B_21,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_16,plain,(
    ! [A_9,C_27,B_21] :
      ( r1_lattice3(A_9,C_27,'#skF_1'(A_9,B_21,C_27))
      | r2_yellow_0(A_9,C_27)
      | ~ r1_lattice3(A_9,C_27,B_21)
      | ~ m1_subset_1(B_21,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_232,plain,(
    ! [A_204,B_205,D_206,E_207] :
      ( m1_subset_1('#skF_3'(A_204,B_205,D_206,D_206),u1_struct_0(A_204))
      | r1_orders_2(A_204,E_207,D_206)
      | ~ r1_lattice3(A_204,k2_relset_1(u1_struct_0(B_205),u1_struct_0(A_204),u1_waybel_0(A_204,B_205)),E_207)
      | ~ m1_subset_1(E_207,u1_struct_0(A_204))
      | ~ r3_waybel_9(A_204,B_205,D_206)
      | ~ m1_subset_1(D_206,u1_struct_0(A_204))
      | ~ l1_waybel_0(B_205,A_204)
      | ~ v7_waybel_0(B_205)
      | ~ v4_orders_2(B_205)
      | v2_struct_0(B_205)
      | ~ l1_waybel_9(A_204)
      | ~ v1_compts_1(A_204)
      | ~ v2_lattice3(A_204)
      | ~ v1_lattice3(A_204)
      | ~ v5_orders_2(A_204)
      | ~ v4_orders_2(A_204)
      | ~ v3_orders_2(A_204)
      | ~ v8_pre_topc(A_204)
      | ~ v2_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_584,plain,(
    ! [A_262,B_263,D_264,B_265] :
      ( m1_subset_1('#skF_3'(A_262,B_263,D_264,D_264),u1_struct_0(A_262))
      | r1_orders_2(A_262,'#skF_1'(A_262,B_265,k2_relset_1(u1_struct_0(B_263),u1_struct_0(A_262),u1_waybel_0(A_262,B_263))),D_264)
      | ~ m1_subset_1('#skF_1'(A_262,B_265,k2_relset_1(u1_struct_0(B_263),u1_struct_0(A_262),u1_waybel_0(A_262,B_263))),u1_struct_0(A_262))
      | ~ r3_waybel_9(A_262,B_263,D_264)
      | ~ m1_subset_1(D_264,u1_struct_0(A_262))
      | ~ l1_waybel_0(B_263,A_262)
      | ~ v7_waybel_0(B_263)
      | ~ v4_orders_2(B_263)
      | v2_struct_0(B_263)
      | ~ l1_waybel_9(A_262)
      | ~ v1_compts_1(A_262)
      | ~ v2_lattice3(A_262)
      | ~ v1_lattice3(A_262)
      | ~ v4_orders_2(A_262)
      | ~ v3_orders_2(A_262)
      | ~ v8_pre_topc(A_262)
      | ~ v2_pre_topc(A_262)
      | r2_yellow_0(A_262,k2_relset_1(u1_struct_0(B_263),u1_struct_0(A_262),u1_waybel_0(A_262,B_263)))
      | ~ r1_lattice3(A_262,k2_relset_1(u1_struct_0(B_263),u1_struct_0(A_262),u1_waybel_0(A_262,B_263)),B_265)
      | ~ m1_subset_1(B_265,u1_struct_0(A_262))
      | ~ l1_orders_2(A_262)
      | ~ v5_orders_2(A_262) ) ),
    inference(resolution,[status(thm)],[c_16,c_232])).

tff(c_811,plain,(
    ! [A_331,B_332,D_333,B_334] :
      ( m1_subset_1('#skF_3'(A_331,B_332,D_333,D_333),u1_struct_0(A_331))
      | r1_orders_2(A_331,'#skF_1'(A_331,B_334,k2_relset_1(u1_struct_0(B_332),u1_struct_0(A_331),u1_waybel_0(A_331,B_332))),D_333)
      | ~ r3_waybel_9(A_331,B_332,D_333)
      | ~ m1_subset_1(D_333,u1_struct_0(A_331))
      | ~ l1_waybel_0(B_332,A_331)
      | ~ v7_waybel_0(B_332)
      | ~ v4_orders_2(B_332)
      | v2_struct_0(B_332)
      | ~ l1_waybel_9(A_331)
      | ~ v1_compts_1(A_331)
      | ~ v2_lattice3(A_331)
      | ~ v1_lattice3(A_331)
      | ~ v4_orders_2(A_331)
      | ~ v3_orders_2(A_331)
      | ~ v8_pre_topc(A_331)
      | ~ v2_pre_topc(A_331)
      | r2_yellow_0(A_331,k2_relset_1(u1_struct_0(B_332),u1_struct_0(A_331),u1_waybel_0(A_331,B_332)))
      | ~ r1_lattice3(A_331,k2_relset_1(u1_struct_0(B_332),u1_struct_0(A_331),u1_waybel_0(A_331,B_332)),B_334)
      | ~ m1_subset_1(B_334,u1_struct_0(A_331))
      | ~ l1_orders_2(A_331)
      | ~ v5_orders_2(A_331) ) ),
    inference(resolution,[status(thm)],[c_18,c_584])).

tff(c_14,plain,(
    ! [A_9,B_21,C_27] :
      ( ~ r1_orders_2(A_9,'#skF_1'(A_9,B_21,C_27),B_21)
      | r2_yellow_0(A_9,C_27)
      | ~ r1_lattice3(A_9,C_27,B_21)
      | ~ m1_subset_1(B_21,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_911,plain,(
    ! [A_341,B_342,D_343] :
      ( m1_subset_1('#skF_3'(A_341,B_342,D_343,D_343),u1_struct_0(A_341))
      | ~ r3_waybel_9(A_341,B_342,D_343)
      | ~ l1_waybel_0(B_342,A_341)
      | ~ v7_waybel_0(B_342)
      | ~ v4_orders_2(B_342)
      | v2_struct_0(B_342)
      | ~ l1_waybel_9(A_341)
      | ~ v1_compts_1(A_341)
      | ~ v2_lattice3(A_341)
      | ~ v1_lattice3(A_341)
      | ~ v4_orders_2(A_341)
      | ~ v3_orders_2(A_341)
      | ~ v8_pre_topc(A_341)
      | ~ v2_pre_topc(A_341)
      | r2_yellow_0(A_341,k2_relset_1(u1_struct_0(B_342),u1_struct_0(A_341),u1_waybel_0(A_341,B_342)))
      | ~ r1_lattice3(A_341,k2_relset_1(u1_struct_0(B_342),u1_struct_0(A_341),u1_waybel_0(A_341,B_342)),D_343)
      | ~ m1_subset_1(D_343,u1_struct_0(A_341))
      | ~ l1_orders_2(A_341)
      | ~ v5_orders_2(A_341) ) ),
    inference(resolution,[status(thm)],[c_811,c_14])).

tff(c_913,plain,(
    ! [B_56,D_68] :
      ( m1_subset_1('#skF_3'('#skF_4',B_56,D_68,D_68),u1_struct_0('#skF_4'))
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | r2_yellow_0('#skF_4',k2_relset_1(u1_struct_0(B_56),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_56)))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_56,D_68)
      | ~ v11_waybel_0(B_56,'#skF_4')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_56,'#skF_4')
      | ~ v7_waybel_0(B_56)
      | ~ v4_orders_2(B_56)
      | v2_struct_0(B_56) ) ),
    inference(resolution,[status(thm)],[c_216,c_911])).

tff(c_931,plain,(
    ! [B_347,D_348] :
      ( m1_subset_1('#skF_3'('#skF_4',B_347,D_348,D_348),u1_struct_0('#skF_4'))
      | r2_yellow_0('#skF_4',k2_relset_1(u1_struct_0(B_347),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_347)))
      | ~ r3_waybel_9('#skF_4',B_347,D_348)
      | ~ v11_waybel_0(B_347,'#skF_4')
      | ~ m1_subset_1(D_348,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_347,'#skF_4')
      | ~ v7_waybel_0(B_347)
      | ~ v4_orders_2(B_347)
      | v2_struct_0(B_347) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_87,c_82,c_80,c_78,c_76,c_72,c_70,c_68,c_66,c_913])).

tff(c_954,plain,(
    ! [B_146,D_348] :
      ( m1_subset_1('#skF_3'('#skF_4',B_146,D_348,D_348),u1_struct_0('#skF_4'))
      | r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_146)))
      | ~ r3_waybel_9('#skF_4',B_146,D_348)
      | ~ v11_waybel_0(B_146,'#skF_4')
      | ~ m1_subset_1(D_348,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_146,'#skF_4')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ l1_waybel_0(B_146,'#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_931])).

tff(c_966,plain,(
    ! [B_349,D_350] :
      ( m1_subset_1('#skF_3'('#skF_4',B_349,D_350,D_350),u1_struct_0('#skF_4'))
      | r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_349)))
      | ~ r3_waybel_9('#skF_4',B_349,D_350)
      | ~ v11_waybel_0(B_349,'#skF_4')
      | ~ m1_subset_1(D_350,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_349)
      | ~ v4_orders_2(B_349)
      | v2_struct_0(B_349)
      | ~ l1_waybel_0(B_349,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_954])).

tff(c_389,plain,(
    ! [A_230,B_231,D_232,E_233] :
      ( ~ v5_pre_topc(k4_waybel_1(A_230,'#skF_3'(A_230,B_231,D_232,D_232)),A_230,A_230)
      | r1_orders_2(A_230,E_233,D_232)
      | ~ r1_lattice3(A_230,k2_relset_1(u1_struct_0(B_231),u1_struct_0(A_230),u1_waybel_0(A_230,B_231)),E_233)
      | ~ m1_subset_1(E_233,u1_struct_0(A_230))
      | ~ r3_waybel_9(A_230,B_231,D_232)
      | ~ m1_subset_1(D_232,u1_struct_0(A_230))
      | ~ l1_waybel_0(B_231,A_230)
      | ~ v7_waybel_0(B_231)
      | ~ v4_orders_2(B_231)
      | v2_struct_0(B_231)
      | ~ l1_waybel_9(A_230)
      | ~ v1_compts_1(A_230)
      | ~ v2_lattice3(A_230)
      | ~ v1_lattice3(A_230)
      | ~ v5_orders_2(A_230)
      | ~ v4_orders_2(A_230)
      | ~ v3_orders_2(A_230)
      | ~ v8_pre_topc(A_230)
      | ~ v2_pre_topc(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_211])).

tff(c_392,plain,(
    ! [E_233,D_232,B_231] :
      ( r1_orders_2('#skF_4',E_233,D_232)
      | ~ r1_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_231),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_231)),E_233)
      | ~ m1_subset_1(E_233,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_231,D_232)
      | ~ m1_subset_1(D_232,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_231,'#skF_4')
      | ~ v7_waybel_0(B_231)
      | ~ v4_orders_2(B_231)
      | v2_struct_0(B_231)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',B_231,D_232,D_232),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_54,c_389])).

tff(c_403,plain,(
    ! [E_238,D_239,B_240] :
      ( r1_orders_2('#skF_4',E_238,D_239)
      | ~ r1_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_240),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_240)),E_238)
      | ~ m1_subset_1(E_238,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_240,D_239)
      | ~ m1_subset_1(D_239,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_240,'#skF_4')
      | ~ v7_waybel_0(B_240)
      | ~ v4_orders_2(B_240)
      | v2_struct_0(B_240)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_240,D_239,D_239),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_392])).

tff(c_417,plain,(
    ! [E_238,D_239,B_146] :
      ( r1_orders_2('#skF_4',E_238,D_239)
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_146)),E_238)
      | ~ m1_subset_1(E_238,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_146,D_239)
      | ~ m1_subset_1(D_239,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_146,'#skF_4')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_146,D_239,D_239),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_146,'#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_403])).

tff(c_532,plain,(
    ! [E_255,D_256,B_257] :
      ( r1_orders_2('#skF_4',E_255,D_256)
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_257)),E_255)
      | ~ m1_subset_1(E_255,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_257,D_256)
      | ~ m1_subset_1(D_256,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_257)
      | ~ v4_orders_2(B_257)
      | v2_struct_0(B_257)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_257,D_256,D_256),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_257,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_417])).

tff(c_552,plain,(
    ! [B_21,B_257,D_256] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_21,k2_relat_1(u1_waybel_0('#skF_4',B_257))),D_256)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_21,k2_relat_1(u1_waybel_0('#skF_4',B_257))),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_257,D_256)
      | ~ m1_subset_1(D_256,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_257)
      | ~ v4_orders_2(B_257)
      | v2_struct_0(B_257)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_257,D_256,D_256),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_257,'#skF_4')
      | r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_257)))
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_257)),B_21)
      | ~ m1_subset_1(B_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_532])).

tff(c_625,plain,(
    ! [B_281,B_282,D_283] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_281,k2_relat_1(u1_waybel_0('#skF_4',B_282))),D_283)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_281,k2_relat_1(u1_waybel_0('#skF_4',B_282))),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_282,D_283)
      | ~ m1_subset_1(D_283,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_282)
      | ~ v4_orders_2(B_282)
      | v2_struct_0(B_282)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_282,D_283,D_283),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_282,'#skF_4')
      | r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_282)))
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_282)),B_281)
      | ~ m1_subset_1(B_281,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_87,c_552])).

tff(c_631,plain,(
    ! [B_21,B_282,D_283] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_21,k2_relat_1(u1_waybel_0('#skF_4',B_282))),D_283)
      | ~ r3_waybel_9('#skF_4',B_282,D_283)
      | ~ m1_subset_1(D_283,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_282)
      | ~ v4_orders_2(B_282)
      | v2_struct_0(B_282)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_282,D_283,D_283),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_282,'#skF_4')
      | r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_282)))
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_282)),B_21)
      | ~ m1_subset_1(B_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_625])).

tff(c_637,plain,(
    ! [B_21,B_282,D_283] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_21,k2_relat_1(u1_waybel_0('#skF_4',B_282))),D_283)
      | ~ r3_waybel_9('#skF_4',B_282,D_283)
      | ~ m1_subset_1(D_283,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_282)
      | ~ v4_orders_2(B_282)
      | v2_struct_0(B_282)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_282,D_283,D_283),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_282,'#skF_4')
      | r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_282)))
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_282)),B_21)
      | ~ m1_subset_1(B_21,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_87,c_631])).

tff(c_1096,plain,(
    ! [B_365,B_366,D_367] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_365,k2_relat_1(u1_waybel_0('#skF_4',B_366))),D_367)
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_366)),B_365)
      | ~ m1_subset_1(B_365,u1_struct_0('#skF_4'))
      | r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_366)))
      | ~ r3_waybel_9('#skF_4',B_366,D_367)
      | ~ v11_waybel_0(B_366,'#skF_4')
      | ~ m1_subset_1(D_367,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_366)
      | ~ v4_orders_2(B_366)
      | v2_struct_0(B_366)
      | ~ l1_waybel_0(B_366,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_966,c_637])).

tff(c_1104,plain,(
    ! [B_366,D_367] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_366)),D_367)
      | r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_366)))
      | ~ r3_waybel_9('#skF_4',B_366,D_367)
      | ~ v11_waybel_0(B_366,'#skF_4')
      | ~ m1_subset_1(D_367,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_366)
      | ~ v4_orders_2(B_366)
      | v2_struct_0(B_366)
      | ~ l1_waybel_0(B_366,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1096,c_14])).

tff(c_1111,plain,(
    ! [B_368,D_369] :
      ( ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_368)),D_369)
      | r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_368)))
      | ~ r3_waybel_9('#skF_4',B_368,D_369)
      | ~ v11_waybel_0(B_368,'#skF_4')
      | ~ m1_subset_1(D_369,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_368)
      | ~ v4_orders_2(B_368)
      | v2_struct_0(B_368)
      | ~ l1_waybel_0(B_368,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_87,c_1104])).

tff(c_1162,plain,(
    ! [B_373,D_374] :
      ( r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_373)))
      | ~ r3_waybel_9('#skF_4',B_373,D_374)
      | ~ v11_waybel_0(B_373,'#skF_4')
      | ~ m1_subset_1(D_374,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_373)
      | ~ v4_orders_2(B_373)
      | v2_struct_0(B_373)
      | ~ l1_waybel_0(B_373,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_230,c_1111])).

tff(c_1164,plain,
    ( r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6')))
    | ~ v11_waybel_0('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_waybel_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1162])).

tff(c_1167,plain,
    ( r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_58,c_64,c_52,c_1164])).

tff(c_1168,plain,(
    r2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1167])).

tff(c_137,plain,(
    ! [A_153,C_154] :
      ( r1_lattice3(A_153,C_154,k2_yellow_0(A_153,C_154))
      | ~ r2_yellow_0(A_153,C_154)
      | ~ m1_subset_1(k2_yellow_0(A_153,C_154),u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v5_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_149,plain,(
    ! [A_176,B_177] :
      ( r1_lattice3(A_176,k2_relat_1(B_177),k2_yellow_0(A_176,k2_relat_1(B_177)))
      | ~ r2_yellow_0(A_176,k2_relat_1(B_177))
      | ~ m1_subset_1(k5_yellow_2(A_176,B_177),u1_struct_0(A_176))
      | ~ l1_orders_2(A_176)
      | ~ v5_orders_2(A_176)
      | ~ v1_relat_1(B_177)
      | ~ l1_orders_2(A_176)
      | v2_struct_0(A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_137])).

tff(c_153,plain,(
    ! [A_178,B_179] :
      ( r1_lattice3(A_178,k2_relat_1(B_179),k5_yellow_2(A_178,B_179))
      | ~ r2_yellow_0(A_178,k2_relat_1(B_179))
      | ~ m1_subset_1(k5_yellow_2(A_178,B_179),u1_struct_0(A_178))
      | ~ l1_orders_2(A_178)
      | ~ v5_orders_2(A_178)
      | ~ v1_relat_1(B_179)
      | ~ l1_orders_2(A_178)
      | v2_struct_0(A_178)
      | ~ v1_relat_1(B_179)
      | ~ l1_orders_2(A_178)
      | v2_struct_0(A_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_149])).

tff(c_156,plain,(
    ! [A_33,B_35] :
      ( r1_lattice3(A_33,k2_relat_1(u1_waybel_0(A_33,B_35)),k1_waybel_9(A_33,B_35))
      | ~ r2_yellow_0(A_33,k2_relat_1(u1_waybel_0(A_33,B_35)))
      | ~ m1_subset_1(k5_yellow_2(A_33,u1_waybel_0(A_33,B_35)),u1_struct_0(A_33))
      | ~ l1_orders_2(A_33)
      | ~ v5_orders_2(A_33)
      | ~ v1_relat_1(u1_waybel_0(A_33,B_35))
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33)
      | ~ v1_relat_1(u1_waybel_0(A_33,B_35))
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33)
      | ~ l1_waybel_0(B_35,A_33)
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_153])).

tff(c_24,plain,(
    ! [A_9,B_21,C_27] :
      ( m1_subset_1('#skF_1'(A_9,B_21,C_27),u1_struct_0(A_9))
      | k2_yellow_0(A_9,C_27) = B_21
      | ~ r1_lattice3(A_9,C_27,B_21)
      | ~ m1_subset_1(B_21,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_9,C_27,B_21] :
      ( r1_lattice3(A_9,C_27,'#skF_1'(A_9,B_21,C_27))
      | k2_yellow_0(A_9,C_27) = B_21
      | ~ r1_lattice3(A_9,C_27,B_21)
      | ~ m1_subset_1(B_21,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_761,plain,(
    ! [A_316,B_317,B_318] :
      ( r1_orders_2(A_316,'#skF_1'(A_316,B_317,k2_relat_1(u1_waybel_0(A_316,B_318))),k1_waybel_9(A_316,B_318))
      | ~ m1_subset_1('#skF_1'(A_316,B_317,k2_relat_1(u1_waybel_0(A_316,B_318))),u1_struct_0(A_316))
      | ~ r2_yellow_0(A_316,k2_relat_1(u1_waybel_0(A_316,B_318)))
      | ~ m1_subset_1(k1_waybel_9(A_316,B_318),u1_struct_0(A_316))
      | ~ v1_relat_1(u1_waybel_0(A_316,B_318))
      | ~ l1_waybel_0(B_318,A_316)
      | v2_struct_0(A_316)
      | k2_yellow_0(A_316,k2_relat_1(u1_waybel_0(A_316,B_318))) = B_317
      | ~ r1_lattice3(A_316,k2_relat_1(u1_waybel_0(A_316,B_318)),B_317)
      | ~ m1_subset_1(B_317,u1_struct_0(A_316))
      | ~ l1_orders_2(A_316)
      | ~ v5_orders_2(A_316) ) ),
    inference(resolution,[status(thm)],[c_22,c_354])).

tff(c_20,plain,(
    ! [A_9,B_21,C_27] :
      ( ~ r1_orders_2(A_9,'#skF_1'(A_9,B_21,C_27),B_21)
      | k2_yellow_0(A_9,C_27) = B_21
      | ~ r1_lattice3(A_9,C_27,B_21)
      | ~ m1_subset_1(B_21,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_772,plain,(
    ! [A_319,B_320] :
      ( ~ m1_subset_1('#skF_1'(A_319,k1_waybel_9(A_319,B_320),k2_relat_1(u1_waybel_0(A_319,B_320))),u1_struct_0(A_319))
      | ~ r2_yellow_0(A_319,k2_relat_1(u1_waybel_0(A_319,B_320)))
      | ~ v1_relat_1(u1_waybel_0(A_319,B_320))
      | ~ l1_waybel_0(B_320,A_319)
      | v2_struct_0(A_319)
      | k2_yellow_0(A_319,k2_relat_1(u1_waybel_0(A_319,B_320))) = k1_waybel_9(A_319,B_320)
      | ~ r1_lattice3(A_319,k2_relat_1(u1_waybel_0(A_319,B_320)),k1_waybel_9(A_319,B_320))
      | ~ m1_subset_1(k1_waybel_9(A_319,B_320),u1_struct_0(A_319))
      | ~ l1_orders_2(A_319)
      | ~ v5_orders_2(A_319) ) ),
    inference(resolution,[status(thm)],[c_761,c_20])).

tff(c_783,plain,(
    ! [A_321,B_322] :
      ( ~ r2_yellow_0(A_321,k2_relat_1(u1_waybel_0(A_321,B_322)))
      | ~ v1_relat_1(u1_waybel_0(A_321,B_322))
      | ~ l1_waybel_0(B_322,A_321)
      | v2_struct_0(A_321)
      | k2_yellow_0(A_321,k2_relat_1(u1_waybel_0(A_321,B_322))) = k1_waybel_9(A_321,B_322)
      | ~ r1_lattice3(A_321,k2_relat_1(u1_waybel_0(A_321,B_322)),k1_waybel_9(A_321,B_322))
      | ~ m1_subset_1(k1_waybel_9(A_321,B_322),u1_struct_0(A_321))
      | ~ l1_orders_2(A_321)
      | ~ v5_orders_2(A_321) ) ),
    inference(resolution,[status(thm)],[c_24,c_772])).

tff(c_798,plain,(
    ! [A_323,B_324] :
      ( k2_yellow_0(A_323,k2_relat_1(u1_waybel_0(A_323,B_324))) = k1_waybel_9(A_323,B_324)
      | ~ m1_subset_1(k1_waybel_9(A_323,B_324),u1_struct_0(A_323))
      | ~ r2_yellow_0(A_323,k2_relat_1(u1_waybel_0(A_323,B_324)))
      | ~ m1_subset_1(k5_yellow_2(A_323,u1_waybel_0(A_323,B_324)),u1_struct_0(A_323))
      | ~ v5_orders_2(A_323)
      | ~ v1_relat_1(u1_waybel_0(A_323,B_324))
      | ~ l1_waybel_0(B_324,A_323)
      | ~ l1_orders_2(A_323)
      | v2_struct_0(A_323) ) ),
    inference(resolution,[status(thm)],[c_156,c_783])).

tff(c_801,plain,(
    ! [A_33,B_35] :
      ( k2_yellow_0(A_33,k2_relat_1(u1_waybel_0(A_33,B_35))) = k1_waybel_9(A_33,B_35)
      | ~ m1_subset_1(k1_waybel_9(A_33,B_35),u1_struct_0(A_33))
      | ~ r2_yellow_0(A_33,k2_relat_1(u1_waybel_0(A_33,B_35)))
      | ~ m1_subset_1(k1_waybel_9(A_33,B_35),u1_struct_0(A_33))
      | ~ v5_orders_2(A_33)
      | ~ v1_relat_1(u1_waybel_0(A_33,B_35))
      | ~ l1_waybel_0(B_35,A_33)
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33)
      | ~ l1_waybel_0(B_35,A_33)
      | ~ l1_orders_2(A_33)
      | v2_struct_0(A_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_798])).

tff(c_1173,plain,
    ( k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) = k1_waybel_9('#skF_4','#skF_6')
    | ~ m1_subset_1(k1_waybel_9('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ v5_orders_2('#skF_4')
    | ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6'))
    | ~ l1_waybel_0('#skF_6','#skF_4')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1168,c_801])).

tff(c_1184,plain,
    ( k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) = k1_waybel_9('#skF_4','#skF_6')
    | ~ m1_subset_1(k1_waybel_9('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_56,c_74,c_1173])).

tff(c_1185,plain,
    ( k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) = k1_waybel_9('#skF_4','#skF_6')
    | ~ m1_subset_1(k1_waybel_9('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
    | ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_1184])).

tff(c_1194,plain,(
    ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1185])).

tff(c_1197,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_117,c_1194])).

tff(c_1201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_56,c_1197])).

tff(c_1203,plain,(
    v1_relat_1(u1_waybel_0('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1185])).

tff(c_638,plain,(
    ! [A_284,B_285,D_286,B_287] :
      ( m1_subset_1('#skF_3'(A_284,B_285,D_286,D_286),u1_struct_0(A_284))
      | r1_orders_2(A_284,'#skF_1'(A_284,B_287,k2_relset_1(u1_struct_0(B_285),u1_struct_0(A_284),u1_waybel_0(A_284,B_285))),D_286)
      | ~ m1_subset_1('#skF_1'(A_284,B_287,k2_relset_1(u1_struct_0(B_285),u1_struct_0(A_284),u1_waybel_0(A_284,B_285))),u1_struct_0(A_284))
      | ~ r3_waybel_9(A_284,B_285,D_286)
      | ~ m1_subset_1(D_286,u1_struct_0(A_284))
      | ~ l1_waybel_0(B_285,A_284)
      | ~ v7_waybel_0(B_285)
      | ~ v4_orders_2(B_285)
      | v2_struct_0(B_285)
      | ~ l1_waybel_9(A_284)
      | ~ v1_compts_1(A_284)
      | ~ v2_lattice3(A_284)
      | ~ v1_lattice3(A_284)
      | ~ v4_orders_2(A_284)
      | ~ v3_orders_2(A_284)
      | ~ v8_pre_topc(A_284)
      | ~ v2_pre_topc(A_284)
      | k2_yellow_0(A_284,k2_relset_1(u1_struct_0(B_285),u1_struct_0(A_284),u1_waybel_0(A_284,B_285))) = B_287
      | ~ r1_lattice3(A_284,k2_relset_1(u1_struct_0(B_285),u1_struct_0(A_284),u1_waybel_0(A_284,B_285)),B_287)
      | ~ m1_subset_1(B_287,u1_struct_0(A_284))
      | ~ l1_orders_2(A_284)
      | ~ v5_orders_2(A_284) ) ),
    inference(resolution,[status(thm)],[c_22,c_232])).

tff(c_1026,plain,(
    ! [A_359,B_360,D_361,B_362] :
      ( m1_subset_1('#skF_3'(A_359,B_360,D_361,D_361),u1_struct_0(A_359))
      | r1_orders_2(A_359,'#skF_1'(A_359,B_362,k2_relset_1(u1_struct_0(B_360),u1_struct_0(A_359),u1_waybel_0(A_359,B_360))),D_361)
      | ~ r3_waybel_9(A_359,B_360,D_361)
      | ~ m1_subset_1(D_361,u1_struct_0(A_359))
      | ~ l1_waybel_0(B_360,A_359)
      | ~ v7_waybel_0(B_360)
      | ~ v4_orders_2(B_360)
      | v2_struct_0(B_360)
      | ~ l1_waybel_9(A_359)
      | ~ v1_compts_1(A_359)
      | ~ v2_lattice3(A_359)
      | ~ v1_lattice3(A_359)
      | ~ v4_orders_2(A_359)
      | ~ v3_orders_2(A_359)
      | ~ v8_pre_topc(A_359)
      | ~ v2_pre_topc(A_359)
      | k2_yellow_0(A_359,k2_relset_1(u1_struct_0(B_360),u1_struct_0(A_359),u1_waybel_0(A_359,B_360))) = B_362
      | ~ r1_lattice3(A_359,k2_relset_1(u1_struct_0(B_360),u1_struct_0(A_359),u1_waybel_0(A_359,B_360)),B_362)
      | ~ m1_subset_1(B_362,u1_struct_0(A_359))
      | ~ l1_orders_2(A_359)
      | ~ v5_orders_2(A_359) ) ),
    inference(resolution,[status(thm)],[c_24,c_638])).

tff(c_1386,plain,(
    ! [A_403,B_404,D_405] :
      ( m1_subset_1('#skF_3'(A_403,B_404,D_405,D_405),u1_struct_0(A_403))
      | ~ r3_waybel_9(A_403,B_404,D_405)
      | ~ l1_waybel_0(B_404,A_403)
      | ~ v7_waybel_0(B_404)
      | ~ v4_orders_2(B_404)
      | v2_struct_0(B_404)
      | ~ l1_waybel_9(A_403)
      | ~ v1_compts_1(A_403)
      | ~ v2_lattice3(A_403)
      | ~ v1_lattice3(A_403)
      | ~ v4_orders_2(A_403)
      | ~ v3_orders_2(A_403)
      | ~ v8_pre_topc(A_403)
      | ~ v2_pre_topc(A_403)
      | k2_yellow_0(A_403,k2_relset_1(u1_struct_0(B_404),u1_struct_0(A_403),u1_waybel_0(A_403,B_404))) = D_405
      | ~ r1_lattice3(A_403,k2_relset_1(u1_struct_0(B_404),u1_struct_0(A_403),u1_waybel_0(A_403,B_404)),D_405)
      | ~ m1_subset_1(D_405,u1_struct_0(A_403))
      | ~ l1_orders_2(A_403)
      | ~ v5_orders_2(A_403) ) ),
    inference(resolution,[status(thm)],[c_1026,c_20])).

tff(c_1388,plain,(
    ! [B_56,D_68] :
      ( m1_subset_1('#skF_3'('#skF_4',B_56,D_68,D_68),u1_struct_0('#skF_4'))
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | k2_yellow_0('#skF_4',k2_relset_1(u1_struct_0(B_56),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_56))) = D_68
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_56,D_68)
      | ~ v11_waybel_0(B_56,'#skF_4')
      | ~ m1_subset_1(D_68,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_56,'#skF_4')
      | ~ v7_waybel_0(B_56)
      | ~ v4_orders_2(B_56)
      | v2_struct_0(B_56) ) ),
    inference(resolution,[status(thm)],[c_216,c_1386])).

tff(c_1405,plain,(
    ! [B_406,D_407] :
      ( m1_subset_1('#skF_3'('#skF_4',B_406,D_407,D_407),u1_struct_0('#skF_4'))
      | k2_yellow_0('#skF_4',k2_relset_1(u1_struct_0(B_406),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_406))) = D_407
      | ~ r3_waybel_9('#skF_4',B_406,D_407)
      | ~ v11_waybel_0(B_406,'#skF_4')
      | ~ m1_subset_1(D_407,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_406,'#skF_4')
      | ~ v7_waybel_0(B_406)
      | ~ v4_orders_2(B_406)
      | v2_struct_0(B_406) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_87,c_82,c_80,c_78,c_76,c_72,c_70,c_68,c_66,c_1388])).

tff(c_2557,plain,(
    ! [B_146,D_407] :
      ( m1_subset_1('#skF_3'('#skF_4',B_146,D_407,D_407),u1_struct_0('#skF_4'))
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_146))) = D_407
      | ~ r3_waybel_9('#skF_4',B_146,D_407)
      | ~ v11_waybel_0(B_146,'#skF_4')
      | ~ m1_subset_1(D_407,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_146,'#skF_4')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ l1_waybel_0(B_146,'#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_1405])).

tff(c_2577,plain,(
    ! [B_3704,D_3705] :
      ( m1_subset_1('#skF_3'('#skF_4',B_3704,D_3705,D_3705),u1_struct_0('#skF_4'))
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_3704))) = D_3705
      | ~ r3_waybel_9('#skF_4',B_3704,D_3705)
      | ~ v11_waybel_0(B_3704,'#skF_4')
      | ~ m1_subset_1(D_3705,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_3704)
      | ~ v4_orders_2(B_3704)
      | v2_struct_0(B_3704)
      | ~ l1_waybel_0(B_3704,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_2557])).

tff(c_549,plain,(
    ! [B_21,B_257,D_256] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_21,k2_relat_1(u1_waybel_0('#skF_4',B_257))),D_256)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_21,k2_relat_1(u1_waybel_0('#skF_4',B_257))),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_257,D_256)
      | ~ m1_subset_1(D_256,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_257)
      | ~ v4_orders_2(B_257)
      | v2_struct_0(B_257)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_257,D_256,D_256),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_257,'#skF_4')
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_257))) = B_21
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_257)),B_21)
      | ~ m1_subset_1(B_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_532])).

tff(c_656,plain,(
    ! [B_291,B_292,D_293] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_291,k2_relat_1(u1_waybel_0('#skF_4',B_292))),D_293)
      | ~ m1_subset_1('#skF_1'('#skF_4',B_291,k2_relat_1(u1_waybel_0('#skF_4',B_292))),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_292,D_293)
      | ~ m1_subset_1(D_293,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_292)
      | ~ v4_orders_2(B_292)
      | v2_struct_0(B_292)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_292,D_293,D_293),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_292,'#skF_4')
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_292))) = B_291
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_292)),B_291)
      | ~ m1_subset_1(B_291,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_87,c_549])).

tff(c_659,plain,(
    ! [B_21,B_292,D_293] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_21,k2_relat_1(u1_waybel_0('#skF_4',B_292))),D_293)
      | ~ r3_waybel_9('#skF_4',B_292,D_293)
      | ~ m1_subset_1(D_293,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_292)
      | ~ v4_orders_2(B_292)
      | v2_struct_0(B_292)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_292,D_293,D_293),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_292,'#skF_4')
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_292))) = B_21
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_292)),B_21)
      | ~ m1_subset_1(B_21,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_656])).

tff(c_665,plain,(
    ! [B_21,B_292,D_293] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_21,k2_relat_1(u1_waybel_0('#skF_4',B_292))),D_293)
      | ~ r3_waybel_9('#skF_4',B_292,D_293)
      | ~ m1_subset_1(D_293,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_292)
      | ~ v4_orders_2(B_292)
      | v2_struct_0(B_292)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_292,D_293,D_293),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_292,'#skF_4')
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_292))) = B_21
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_292)),B_21)
      | ~ m1_subset_1(B_21,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_87,c_659])).

tff(c_7199,plain,(
    ! [B_6455,B_6456,D_6457] :
      ( r1_orders_2('#skF_4','#skF_1'('#skF_4',B_6455,k2_relat_1(u1_waybel_0('#skF_4',B_6456))),D_6457)
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_6456))) = B_6455
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_6456)),B_6455)
      | ~ m1_subset_1(B_6455,u1_struct_0('#skF_4'))
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_6456))) = D_6457
      | ~ r3_waybel_9('#skF_4',B_6456,D_6457)
      | ~ v11_waybel_0(B_6456,'#skF_4')
      | ~ m1_subset_1(D_6457,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_6456)
      | ~ v4_orders_2(B_6456)
      | v2_struct_0(B_6456)
      | ~ l1_waybel_0(B_6456,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2577,c_665])).

tff(c_7203,plain,(
    ! [B_6456,D_6457] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_6456)),D_6457)
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_6456))) = D_6457
      | ~ r3_waybel_9('#skF_4',B_6456,D_6457)
      | ~ v11_waybel_0(B_6456,'#skF_4')
      | ~ m1_subset_1(D_6457,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_6456)
      | ~ v4_orders_2(B_6456)
      | v2_struct_0(B_6456)
      | ~ l1_waybel_0(B_6456,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7199,c_20])).

tff(c_7255,plain,(
    ! [B_6487,D_6488] :
      ( ~ r1_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_6487)),D_6488)
      | k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_6487))) = D_6488
      | ~ r3_waybel_9('#skF_4',B_6487,D_6488)
      | ~ v11_waybel_0(B_6487,'#skF_4')
      | ~ m1_subset_1(D_6488,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_6487)
      | ~ v4_orders_2(B_6487)
      | v2_struct_0(B_6487)
      | ~ l1_waybel_0(B_6487,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_87,c_7203])).

tff(c_7328,plain,(
    ! [B_6518,D_6519] :
      ( k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_6518))) = D_6519
      | ~ r3_waybel_9('#skF_4',B_6518,D_6519)
      | ~ v11_waybel_0(B_6518,'#skF_4')
      | ~ m1_subset_1(D_6519,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_6518)
      | ~ v4_orders_2(B_6518)
      | v2_struct_0(B_6518)
      | ~ l1_waybel_0(B_6518,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_230,c_7255])).

tff(c_7346,plain,
    ( k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) = '#skF_5'
    | ~ v11_waybel_0('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_waybel_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_7328])).

tff(c_7349,plain,
    ( k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) = '#skF_5'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_60,c_58,c_64,c_52,c_7346])).

tff(c_7350,plain,(
    k2_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_7349])).

tff(c_7452,plain,
    ( k5_yellow_2('#skF_4',u1_waybel_0('#skF_4','#skF_6')) = '#skF_5'
    | ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6'))
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7350,c_34])).

tff(c_7530,plain,
    ( k5_yellow_2('#skF_4',u1_waybel_0('#skF_4','#skF_6')) = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_1203,c_7452])).

tff(c_7531,plain,(
    k5_yellow_2('#skF_4',u1_waybel_0('#skF_4','#skF_6')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_7530])).

tff(c_7591,plain,
    ( k1_waybel_9('#skF_4','#skF_6') = '#skF_5'
    | ~ l1_waybel_0('#skF_6','#skF_4')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7531,c_32])).

tff(c_7659,plain,
    ( k1_waybel_9('#skF_4','#skF_6') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_56,c_7591])).

tff(c_7661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_48,c_7659])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:34:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.95/3.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.95/3.69  
% 10.95/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.95/3.69  %$ v5_pre_topc > v1_funct_2 > r3_waybel_9 > r1_orders_2 > r1_lattice3 > v11_waybel_0 > r2_yellow_0 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_relat_1 > v1_lattice3 > v1_funct_1 > v1_compts_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k5_yellow_2 > k4_waybel_1 > k2_zfmisc_1 > k2_yellow_0 > k1_waybel_9 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 10.95/3.69  
% 10.95/3.69  %Foreground sorts:
% 10.95/3.69  
% 10.95/3.69  
% 10.95/3.69  %Background operators:
% 10.95/3.69  
% 10.95/3.69  
% 10.95/3.69  %Foreground operators:
% 10.95/3.69  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.95/3.69  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 10.95/3.69  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 10.95/3.69  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.95/3.69  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 10.95/3.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.95/3.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.95/3.69  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 10.95/3.69  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 10.95/3.69  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 10.95/3.69  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.95/3.69  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 10.95/3.69  tff('#skF_5', type, '#skF_5': $i).
% 10.95/3.69  tff(k5_yellow_2, type, k5_yellow_2: ($i * $i) > $i).
% 10.95/3.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.95/3.69  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 10.95/3.69  tff(v11_waybel_0, type, v11_waybel_0: ($i * $i) > $o).
% 10.95/3.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 10.95/3.69  tff('#skF_6', type, '#skF_6': $i).
% 10.95/3.69  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 10.95/3.69  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 10.95/3.69  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 10.95/3.69  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 10.95/3.69  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 10.95/3.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.95/3.69  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 10.95/3.69  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 10.95/3.69  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 10.95/3.69  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 10.95/3.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.95/3.69  tff(k1_waybel_9, type, k1_waybel_9: ($i * $i) > $i).
% 10.95/3.69  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 10.95/3.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.95/3.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.95/3.69  tff('#skF_4', type, '#skF_4': $i).
% 10.95/3.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.95/3.69  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 10.95/3.69  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 10.95/3.69  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 10.95/3.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 10.95/3.69  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 10.95/3.69  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 10.95/3.69  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 10.95/3.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.95/3.69  
% 11.27/3.72  tff(f_254, negated_conjecture, ~(![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => ((((![D]: (m1_subset_1(D, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, D), A, A))) & v11_waybel_0(C, A)) & r3_waybel_9(A, C, B)) => (B = k1_waybel_9(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_waybel_9)).
% 11.27/3.72  tff(f_114, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 11.27/3.72  tff(f_37, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 11.27/3.72  tff(f_88, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 11.27/3.72  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 11.27/3.72  tff(f_161, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & v11_waybel_0(B, A)) & r3_waybel_9(A, B, C)) => r1_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_waybel_9)).
% 11.27/3.72  tff(f_98, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (l1_waybel_0(B, A) => (k1_waybel_9(A, B) = k5_yellow_2(A, u1_waybel_0(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_waybel_9)).
% 11.27/3.72  tff(f_108, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (v1_relat_1(B) => (k5_yellow_2(A, B) = k2_yellow_0(A, k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_yellow_2)).
% 11.27/3.72  tff(f_78, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C)) => (r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B)))))) & ((r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B))))) => ((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_yellow_0)).
% 11.27/3.72  tff(f_44, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 11.27/3.72  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 11.27/3.72  tff(f_211, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & r3_waybel_9(A, B, C)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r1_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), E) => r1_orders_2(A, E, D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l52_waybel_9)).
% 11.27/3.72  tff(c_66, plain, (l1_waybel_9('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_83, plain, (![A_128]: (l1_orders_2(A_128) | ~l1_waybel_9(A_128))), inference(cnfTransformation, [status(thm)], [f_114])).
% 11.27/3.72  tff(c_87, plain, (l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_66, c_83])).
% 11.27/3.72  tff(c_72, plain, (v1_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_74, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_6, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.27/3.72  tff(c_109, plain, (![A_145, B_146]: (m1_subset_1(u1_waybel_0(A_145, B_146), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_146), u1_struct_0(A_145)))) | ~l1_waybel_0(B_146, A_145) | ~l1_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_88])).
% 11.27/3.72  tff(c_4, plain, (![A_4, B_5, C_6]: (k2_relset_1(A_4, B_5, C_6)=k2_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.27/3.72  tff(c_116, plain, (![B_146, A_145]: (k2_relset_1(u1_struct_0(B_146), u1_struct_0(A_145), u1_waybel_0(A_145, B_146))=k2_relat_1(u1_waybel_0(A_145, B_146)) | ~l1_waybel_0(B_146, A_145) | ~l1_struct_0(A_145))), inference(resolution, [status(thm)], [c_109, c_4])).
% 11.27/3.72  tff(c_82, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_80, plain, (v8_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_78, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_76, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_70, plain, (v2_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_68, plain, (v1_compts_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_42, plain, (![A_40, B_56, D_68]: (m1_subset_1('#skF_2'(A_40, B_56, D_68, D_68), u1_struct_0(A_40)) | r1_lattice3(A_40, k2_relset_1(u1_struct_0(B_56), u1_struct_0(A_40), u1_waybel_0(A_40, B_56)), D_68) | ~r3_waybel_9(A_40, B_56, D_68) | ~v11_waybel_0(B_56, A_40) | ~m1_subset_1(D_68, u1_struct_0(A_40)) | ~l1_waybel_0(B_56, A_40) | ~v7_waybel_0(B_56) | ~v4_orders_2(B_56) | v2_struct_0(B_56) | ~l1_waybel_9(A_40) | ~v1_compts_1(A_40) | ~v2_lattice3(A_40) | ~v1_lattice3(A_40) | ~v5_orders_2(A_40) | ~v4_orders_2(A_40) | ~v3_orders_2(A_40) | ~v8_pre_topc(A_40) | ~v2_pre_topc(A_40))), inference(cnfTransformation, [status(thm)], [f_161])).
% 11.27/3.72  tff(c_54, plain, (![D_127]: (v5_pre_topc(k4_waybel_1('#skF_4', D_127), '#skF_4', '#skF_4') | ~m1_subset_1(D_127, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_197, plain, (![A_197, B_198, D_199]: (~v5_pre_topc(k4_waybel_1(A_197, '#skF_2'(A_197, B_198, D_199, D_199)), A_197, A_197) | r1_lattice3(A_197, k2_relset_1(u1_struct_0(B_198), u1_struct_0(A_197), u1_waybel_0(A_197, B_198)), D_199) | ~r3_waybel_9(A_197, B_198, D_199) | ~v11_waybel_0(B_198, A_197) | ~m1_subset_1(D_199, u1_struct_0(A_197)) | ~l1_waybel_0(B_198, A_197) | ~v7_waybel_0(B_198) | ~v4_orders_2(B_198) | v2_struct_0(B_198) | ~l1_waybel_9(A_197) | ~v1_compts_1(A_197) | ~v2_lattice3(A_197) | ~v1_lattice3(A_197) | ~v5_orders_2(A_197) | ~v4_orders_2(A_197) | ~v3_orders_2(A_197) | ~v8_pre_topc(A_197) | ~v2_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_161])).
% 11.27/3.72  tff(c_200, plain, (![B_198, D_199]: (r1_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_198), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_198)), D_199) | ~r3_waybel_9('#skF_4', B_198, D_199) | ~v11_waybel_0(B_198, '#skF_4') | ~m1_subset_1(D_199, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_198, '#skF_4') | ~v7_waybel_0(B_198) | ~v4_orders_2(B_198) | v2_struct_0(B_198) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_198, D_199, D_199), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_197])).
% 11.27/3.72  tff(c_204, plain, (![B_200, D_201]: (r1_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_200), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_200)), D_201) | ~r3_waybel_9('#skF_4', B_200, D_201) | ~v11_waybel_0(B_200, '#skF_4') | ~m1_subset_1(D_201, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_200, '#skF_4') | ~v7_waybel_0(B_200) | ~v4_orders_2(B_200) | v2_struct_0(B_200) | ~m1_subset_1('#skF_2'('#skF_4', B_200, D_201, D_201), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_200])).
% 11.27/3.72  tff(c_210, plain, (![B_56, D_68]: (r1_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_56), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_56)), D_68) | ~r3_waybel_9('#skF_4', B_56, D_68) | ~v11_waybel_0(B_56, '#skF_4') | ~m1_subset_1(D_68, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_56, '#skF_4') | ~v7_waybel_0(B_56) | ~v4_orders_2(B_56) | v2_struct_0(B_56) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_42, c_204])).
% 11.27/3.72  tff(c_217, plain, (![B_202, D_203]: (r1_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_202), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_202)), D_203) | ~r3_waybel_9('#skF_4', B_202, D_203) | ~v11_waybel_0(B_202, '#skF_4') | ~m1_subset_1(D_203, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_202, '#skF_4') | ~v7_waybel_0(B_202) | ~v4_orders_2(B_202) | v2_struct_0(B_202))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_210])).
% 11.27/3.72  tff(c_221, plain, (![B_146, D_203]: (r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_146)), D_203) | ~r3_waybel_9('#skF_4', B_146, D_203) | ~v11_waybel_0(B_146, '#skF_4') | ~m1_subset_1(D_203, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_146, '#skF_4') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~l1_waybel_0(B_146, '#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_217])).
% 11.27/3.72  tff(c_222, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_221])).
% 11.27/3.72  tff(c_225, plain, (~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_6, c_222])).
% 11.27/3.72  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_225])).
% 11.27/3.72  tff(c_230, plain, (![B_146, D_203]: (r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_146)), D_203) | ~r3_waybel_9('#skF_4', B_146, D_203) | ~v11_waybel_0(B_146, '#skF_4') | ~m1_subset_1(D_203, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_146, '#skF_4') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~l1_waybel_0(B_146, '#skF_4'))), inference(splitRight, [status(thm)], [c_221])).
% 11.27/3.72  tff(c_32, plain, (![A_33, B_35]: (k5_yellow_2(A_33, u1_waybel_0(A_33, B_35))=k1_waybel_9(A_33, B_35) | ~l1_waybel_0(B_35, A_33) | ~l1_orders_2(A_33) | v2_struct_0(A_33))), inference(cnfTransformation, [status(thm)], [f_98])).
% 11.27/3.72  tff(c_34, plain, (![A_36, B_38]: (k2_yellow_0(A_36, k2_relat_1(B_38))=k5_yellow_2(A_36, B_38) | ~v1_relat_1(B_38) | ~l1_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.27/3.72  tff(c_146, plain, (![A_173, D_174, C_175]: (r1_orders_2(A_173, D_174, k2_yellow_0(A_173, C_175)) | ~r1_lattice3(A_173, C_175, D_174) | ~m1_subset_1(D_174, u1_struct_0(A_173)) | ~r2_yellow_0(A_173, C_175) | ~m1_subset_1(k2_yellow_0(A_173, C_175), u1_struct_0(A_173)) | ~l1_orders_2(A_173) | ~v5_orders_2(A_173))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.27/3.72  tff(c_157, plain, (![A_180, D_181, B_182]: (r1_orders_2(A_180, D_181, k2_yellow_0(A_180, k2_relat_1(B_182))) | ~r1_lattice3(A_180, k2_relat_1(B_182), D_181) | ~m1_subset_1(D_181, u1_struct_0(A_180)) | ~r2_yellow_0(A_180, k2_relat_1(B_182)) | ~m1_subset_1(k5_yellow_2(A_180, B_182), u1_struct_0(A_180)) | ~l1_orders_2(A_180) | ~v5_orders_2(A_180) | ~v1_relat_1(B_182) | ~l1_orders_2(A_180) | v2_struct_0(A_180))), inference(superposition, [status(thm), theory('equality')], [c_34, c_146])).
% 11.27/3.72  tff(c_171, plain, (![A_183, D_184, B_185]: (r1_orders_2(A_183, D_184, k5_yellow_2(A_183, B_185)) | ~r1_lattice3(A_183, k2_relat_1(B_185), D_184) | ~m1_subset_1(D_184, u1_struct_0(A_183)) | ~r2_yellow_0(A_183, k2_relat_1(B_185)) | ~m1_subset_1(k5_yellow_2(A_183, B_185), u1_struct_0(A_183)) | ~l1_orders_2(A_183) | ~v5_orders_2(A_183) | ~v1_relat_1(B_185) | ~l1_orders_2(A_183) | v2_struct_0(A_183) | ~v1_relat_1(B_185) | ~l1_orders_2(A_183) | v2_struct_0(A_183))), inference(superposition, [status(thm), theory('equality')], [c_34, c_157])).
% 11.27/3.72  tff(c_269, plain, (![A_214, D_215, B_216]: (r1_orders_2(A_214, D_215, k5_yellow_2(A_214, u1_waybel_0(A_214, B_216))) | ~r1_lattice3(A_214, k2_relat_1(u1_waybel_0(A_214, B_216)), D_215) | ~m1_subset_1(D_215, u1_struct_0(A_214)) | ~r2_yellow_0(A_214, k2_relat_1(u1_waybel_0(A_214, B_216))) | ~m1_subset_1(k1_waybel_9(A_214, B_216), u1_struct_0(A_214)) | ~l1_orders_2(A_214) | ~v5_orders_2(A_214) | ~v1_relat_1(u1_waybel_0(A_214, B_216)) | ~l1_orders_2(A_214) | v2_struct_0(A_214) | ~v1_relat_1(u1_waybel_0(A_214, B_216)) | ~l1_orders_2(A_214) | v2_struct_0(A_214) | ~l1_waybel_0(B_216, A_214) | ~l1_orders_2(A_214) | v2_struct_0(A_214))), inference(superposition, [status(thm), theory('equality')], [c_32, c_171])).
% 11.27/3.72  tff(c_354, plain, (![A_227, D_228, B_229]: (r1_orders_2(A_227, D_228, k1_waybel_9(A_227, B_229)) | ~r1_lattice3(A_227, k2_relat_1(u1_waybel_0(A_227, B_229)), D_228) | ~m1_subset_1(D_228, u1_struct_0(A_227)) | ~r2_yellow_0(A_227, k2_relat_1(u1_waybel_0(A_227, B_229))) | ~m1_subset_1(k1_waybel_9(A_227, B_229), u1_struct_0(A_227)) | ~l1_orders_2(A_227) | ~v5_orders_2(A_227) | ~v1_relat_1(u1_waybel_0(A_227, B_229)) | ~l1_orders_2(A_227) | v2_struct_0(A_227) | ~v1_relat_1(u1_waybel_0(A_227, B_229)) | ~l1_orders_2(A_227) | v2_struct_0(A_227) | ~l1_waybel_0(B_229, A_227) | ~l1_orders_2(A_227) | v2_struct_0(A_227) | ~l1_waybel_0(B_229, A_227) | ~l1_orders_2(A_227) | v2_struct_0(A_227))), inference(superposition, [status(thm), theory('equality')], [c_32, c_269])).
% 11.27/3.72  tff(c_357, plain, (![D_203, B_146]: (r1_orders_2('#skF_4', D_203, k1_waybel_9('#skF_4', B_146)) | ~r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_146))) | ~m1_subset_1(k1_waybel_9('#skF_4', B_146), u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~v1_relat_1(u1_waybel_0('#skF_4', B_146)) | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_146, D_203) | ~v11_waybel_0(B_146, '#skF_4') | ~m1_subset_1(D_203, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~l1_waybel_0(B_146, '#skF_4'))), inference(resolution, [status(thm)], [c_230, c_354])).
% 11.27/3.72  tff(c_382, plain, (![D_203, B_146]: (r1_orders_2('#skF_4', D_203, k1_waybel_9('#skF_4', B_146)) | ~r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_146))) | ~m1_subset_1(k1_waybel_9('#skF_4', B_146), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', B_146)) | v2_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_146, D_203) | ~v11_waybel_0(B_146, '#skF_4') | ~m1_subset_1(D_203, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~l1_waybel_0(B_146, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_74, c_357])).
% 11.27/3.72  tff(c_573, plain, (v2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_382])).
% 11.27/3.72  tff(c_8, plain, (![A_8]: (~v2_struct_0(A_8) | ~v1_lattice3(A_8) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.27/3.72  tff(c_576, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_573, c_8])).
% 11.27/3.72  tff(c_580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_87, c_72, c_576])).
% 11.27/3.72  tff(c_582, plain, (~v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_382])).
% 11.27/3.72  tff(c_48, plain, (k1_waybel_9('#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_56, plain, (l1_waybel_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_231, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_221])).
% 11.27/3.72  tff(c_2, plain, (![C_3, A_1, B_2]: (v1_relat_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 11.27/3.72  tff(c_117, plain, (![A_145, B_146]: (v1_relat_1(u1_waybel_0(A_145, B_146)) | ~l1_waybel_0(B_146, A_145) | ~l1_struct_0(A_145))), inference(resolution, [status(thm)], [c_109, c_2])).
% 11.27/3.72  tff(c_62, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_60, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_58, plain, (v7_waybel_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_64, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_52, plain, (v11_waybel_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_50, plain, (r3_waybel_9('#skF_4', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_254])).
% 11.27/3.72  tff(c_216, plain, (![B_56, D_68]: (r1_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_56), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_56)), D_68) | ~r3_waybel_9('#skF_4', B_56, D_68) | ~v11_waybel_0(B_56, '#skF_4') | ~m1_subset_1(D_68, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_56, '#skF_4') | ~v7_waybel_0(B_56) | ~v4_orders_2(B_56) | v2_struct_0(B_56))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_210])).
% 11.27/3.72  tff(c_18, plain, (![A_9, B_21, C_27]: (m1_subset_1('#skF_1'(A_9, B_21, C_27), u1_struct_0(A_9)) | r2_yellow_0(A_9, C_27) | ~r1_lattice3(A_9, C_27, B_21) | ~m1_subset_1(B_21, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.27/3.72  tff(c_16, plain, (![A_9, C_27, B_21]: (r1_lattice3(A_9, C_27, '#skF_1'(A_9, B_21, C_27)) | r2_yellow_0(A_9, C_27) | ~r1_lattice3(A_9, C_27, B_21) | ~m1_subset_1(B_21, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.27/3.72  tff(c_232, plain, (![A_204, B_205, D_206, E_207]: (m1_subset_1('#skF_3'(A_204, B_205, D_206, D_206), u1_struct_0(A_204)) | r1_orders_2(A_204, E_207, D_206) | ~r1_lattice3(A_204, k2_relset_1(u1_struct_0(B_205), u1_struct_0(A_204), u1_waybel_0(A_204, B_205)), E_207) | ~m1_subset_1(E_207, u1_struct_0(A_204)) | ~r3_waybel_9(A_204, B_205, D_206) | ~m1_subset_1(D_206, u1_struct_0(A_204)) | ~l1_waybel_0(B_205, A_204) | ~v7_waybel_0(B_205) | ~v4_orders_2(B_205) | v2_struct_0(B_205) | ~l1_waybel_9(A_204) | ~v1_compts_1(A_204) | ~v2_lattice3(A_204) | ~v1_lattice3(A_204) | ~v5_orders_2(A_204) | ~v4_orders_2(A_204) | ~v3_orders_2(A_204) | ~v8_pre_topc(A_204) | ~v2_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.27/3.72  tff(c_584, plain, (![A_262, B_263, D_264, B_265]: (m1_subset_1('#skF_3'(A_262, B_263, D_264, D_264), u1_struct_0(A_262)) | r1_orders_2(A_262, '#skF_1'(A_262, B_265, k2_relset_1(u1_struct_0(B_263), u1_struct_0(A_262), u1_waybel_0(A_262, B_263))), D_264) | ~m1_subset_1('#skF_1'(A_262, B_265, k2_relset_1(u1_struct_0(B_263), u1_struct_0(A_262), u1_waybel_0(A_262, B_263))), u1_struct_0(A_262)) | ~r3_waybel_9(A_262, B_263, D_264) | ~m1_subset_1(D_264, u1_struct_0(A_262)) | ~l1_waybel_0(B_263, A_262) | ~v7_waybel_0(B_263) | ~v4_orders_2(B_263) | v2_struct_0(B_263) | ~l1_waybel_9(A_262) | ~v1_compts_1(A_262) | ~v2_lattice3(A_262) | ~v1_lattice3(A_262) | ~v4_orders_2(A_262) | ~v3_orders_2(A_262) | ~v8_pre_topc(A_262) | ~v2_pre_topc(A_262) | r2_yellow_0(A_262, k2_relset_1(u1_struct_0(B_263), u1_struct_0(A_262), u1_waybel_0(A_262, B_263))) | ~r1_lattice3(A_262, k2_relset_1(u1_struct_0(B_263), u1_struct_0(A_262), u1_waybel_0(A_262, B_263)), B_265) | ~m1_subset_1(B_265, u1_struct_0(A_262)) | ~l1_orders_2(A_262) | ~v5_orders_2(A_262))), inference(resolution, [status(thm)], [c_16, c_232])).
% 11.27/3.72  tff(c_811, plain, (![A_331, B_332, D_333, B_334]: (m1_subset_1('#skF_3'(A_331, B_332, D_333, D_333), u1_struct_0(A_331)) | r1_orders_2(A_331, '#skF_1'(A_331, B_334, k2_relset_1(u1_struct_0(B_332), u1_struct_0(A_331), u1_waybel_0(A_331, B_332))), D_333) | ~r3_waybel_9(A_331, B_332, D_333) | ~m1_subset_1(D_333, u1_struct_0(A_331)) | ~l1_waybel_0(B_332, A_331) | ~v7_waybel_0(B_332) | ~v4_orders_2(B_332) | v2_struct_0(B_332) | ~l1_waybel_9(A_331) | ~v1_compts_1(A_331) | ~v2_lattice3(A_331) | ~v1_lattice3(A_331) | ~v4_orders_2(A_331) | ~v3_orders_2(A_331) | ~v8_pre_topc(A_331) | ~v2_pre_topc(A_331) | r2_yellow_0(A_331, k2_relset_1(u1_struct_0(B_332), u1_struct_0(A_331), u1_waybel_0(A_331, B_332))) | ~r1_lattice3(A_331, k2_relset_1(u1_struct_0(B_332), u1_struct_0(A_331), u1_waybel_0(A_331, B_332)), B_334) | ~m1_subset_1(B_334, u1_struct_0(A_331)) | ~l1_orders_2(A_331) | ~v5_orders_2(A_331))), inference(resolution, [status(thm)], [c_18, c_584])).
% 11.27/3.72  tff(c_14, plain, (![A_9, B_21, C_27]: (~r1_orders_2(A_9, '#skF_1'(A_9, B_21, C_27), B_21) | r2_yellow_0(A_9, C_27) | ~r1_lattice3(A_9, C_27, B_21) | ~m1_subset_1(B_21, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.27/3.72  tff(c_911, plain, (![A_341, B_342, D_343]: (m1_subset_1('#skF_3'(A_341, B_342, D_343, D_343), u1_struct_0(A_341)) | ~r3_waybel_9(A_341, B_342, D_343) | ~l1_waybel_0(B_342, A_341) | ~v7_waybel_0(B_342) | ~v4_orders_2(B_342) | v2_struct_0(B_342) | ~l1_waybel_9(A_341) | ~v1_compts_1(A_341) | ~v2_lattice3(A_341) | ~v1_lattice3(A_341) | ~v4_orders_2(A_341) | ~v3_orders_2(A_341) | ~v8_pre_topc(A_341) | ~v2_pre_topc(A_341) | r2_yellow_0(A_341, k2_relset_1(u1_struct_0(B_342), u1_struct_0(A_341), u1_waybel_0(A_341, B_342))) | ~r1_lattice3(A_341, k2_relset_1(u1_struct_0(B_342), u1_struct_0(A_341), u1_waybel_0(A_341, B_342)), D_343) | ~m1_subset_1(D_343, u1_struct_0(A_341)) | ~l1_orders_2(A_341) | ~v5_orders_2(A_341))), inference(resolution, [status(thm)], [c_811, c_14])).
% 11.27/3.72  tff(c_913, plain, (![B_56, D_68]: (m1_subset_1('#skF_3'('#skF_4', B_56, D_68, D_68), u1_struct_0('#skF_4')) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | r2_yellow_0('#skF_4', k2_relset_1(u1_struct_0(B_56), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_56))) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~r3_waybel_9('#skF_4', B_56, D_68) | ~v11_waybel_0(B_56, '#skF_4') | ~m1_subset_1(D_68, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_56, '#skF_4') | ~v7_waybel_0(B_56) | ~v4_orders_2(B_56) | v2_struct_0(B_56))), inference(resolution, [status(thm)], [c_216, c_911])).
% 11.27/3.72  tff(c_931, plain, (![B_347, D_348]: (m1_subset_1('#skF_3'('#skF_4', B_347, D_348, D_348), u1_struct_0('#skF_4')) | r2_yellow_0('#skF_4', k2_relset_1(u1_struct_0(B_347), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_347))) | ~r3_waybel_9('#skF_4', B_347, D_348) | ~v11_waybel_0(B_347, '#skF_4') | ~m1_subset_1(D_348, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_347, '#skF_4') | ~v7_waybel_0(B_347) | ~v4_orders_2(B_347) | v2_struct_0(B_347))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_87, c_82, c_80, c_78, c_76, c_72, c_70, c_68, c_66, c_913])).
% 11.27/3.72  tff(c_954, plain, (![B_146, D_348]: (m1_subset_1('#skF_3'('#skF_4', B_146, D_348, D_348), u1_struct_0('#skF_4')) | r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_146))) | ~r3_waybel_9('#skF_4', B_146, D_348) | ~v11_waybel_0(B_146, '#skF_4') | ~m1_subset_1(D_348, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_146, '#skF_4') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~l1_waybel_0(B_146, '#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_931])).
% 11.27/3.72  tff(c_966, plain, (![B_349, D_350]: (m1_subset_1('#skF_3'('#skF_4', B_349, D_350, D_350), u1_struct_0('#skF_4')) | r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_349))) | ~r3_waybel_9('#skF_4', B_349, D_350) | ~v11_waybel_0(B_349, '#skF_4') | ~m1_subset_1(D_350, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_349) | ~v4_orders_2(B_349) | v2_struct_0(B_349) | ~l1_waybel_0(B_349, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_954])).
% 11.27/3.72  tff(c_389, plain, (![A_230, B_231, D_232, E_233]: (~v5_pre_topc(k4_waybel_1(A_230, '#skF_3'(A_230, B_231, D_232, D_232)), A_230, A_230) | r1_orders_2(A_230, E_233, D_232) | ~r1_lattice3(A_230, k2_relset_1(u1_struct_0(B_231), u1_struct_0(A_230), u1_waybel_0(A_230, B_231)), E_233) | ~m1_subset_1(E_233, u1_struct_0(A_230)) | ~r3_waybel_9(A_230, B_231, D_232) | ~m1_subset_1(D_232, u1_struct_0(A_230)) | ~l1_waybel_0(B_231, A_230) | ~v7_waybel_0(B_231) | ~v4_orders_2(B_231) | v2_struct_0(B_231) | ~l1_waybel_9(A_230) | ~v1_compts_1(A_230) | ~v2_lattice3(A_230) | ~v1_lattice3(A_230) | ~v5_orders_2(A_230) | ~v4_orders_2(A_230) | ~v3_orders_2(A_230) | ~v8_pre_topc(A_230) | ~v2_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_211])).
% 11.27/3.72  tff(c_392, plain, (![E_233, D_232, B_231]: (r1_orders_2('#skF_4', E_233, D_232) | ~r1_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_231), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_231)), E_233) | ~m1_subset_1(E_233, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_231, D_232) | ~m1_subset_1(D_232, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_231, '#skF_4') | ~v7_waybel_0(B_231) | ~v4_orders_2(B_231) | v2_struct_0(B_231) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_subset_1('#skF_3'('#skF_4', B_231, D_232, D_232), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_54, c_389])).
% 11.27/3.72  tff(c_403, plain, (![E_238, D_239, B_240]: (r1_orders_2('#skF_4', E_238, D_239) | ~r1_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_240), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_240)), E_238) | ~m1_subset_1(E_238, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_240, D_239) | ~m1_subset_1(D_239, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_240, '#skF_4') | ~v7_waybel_0(B_240) | ~v4_orders_2(B_240) | v2_struct_0(B_240) | ~m1_subset_1('#skF_3'('#skF_4', B_240, D_239, D_239), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_392])).
% 11.27/3.72  tff(c_417, plain, (![E_238, D_239, B_146]: (r1_orders_2('#skF_4', E_238, D_239) | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_146)), E_238) | ~m1_subset_1(E_238, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_146, D_239) | ~m1_subset_1(D_239, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_146, '#skF_4') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~m1_subset_1('#skF_3'('#skF_4', B_146, D_239, D_239), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_146, '#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_403])).
% 11.27/3.72  tff(c_532, plain, (![E_255, D_256, B_257]: (r1_orders_2('#skF_4', E_255, D_256) | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_257)), E_255) | ~m1_subset_1(E_255, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_257, D_256) | ~m1_subset_1(D_256, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_257) | ~v4_orders_2(B_257) | v2_struct_0(B_257) | ~m1_subset_1('#skF_3'('#skF_4', B_257, D_256, D_256), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_257, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_417])).
% 11.27/3.72  tff(c_552, plain, (![B_21, B_257, D_256]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_21, k2_relat_1(u1_waybel_0('#skF_4', B_257))), D_256) | ~m1_subset_1('#skF_1'('#skF_4', B_21, k2_relat_1(u1_waybel_0('#skF_4', B_257))), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_257, D_256) | ~m1_subset_1(D_256, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_257) | ~v4_orders_2(B_257) | v2_struct_0(B_257) | ~m1_subset_1('#skF_3'('#skF_4', B_257, D_256, D_256), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_257, '#skF_4') | r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_257))) | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_257)), B_21) | ~m1_subset_1(B_21, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_532])).
% 11.27/3.72  tff(c_625, plain, (![B_281, B_282, D_283]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_281, k2_relat_1(u1_waybel_0('#skF_4', B_282))), D_283) | ~m1_subset_1('#skF_1'('#skF_4', B_281, k2_relat_1(u1_waybel_0('#skF_4', B_282))), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_282, D_283) | ~m1_subset_1(D_283, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_282) | ~v4_orders_2(B_282) | v2_struct_0(B_282) | ~m1_subset_1('#skF_3'('#skF_4', B_282, D_283, D_283), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_282, '#skF_4') | r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_282))) | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_282)), B_281) | ~m1_subset_1(B_281, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_87, c_552])).
% 11.27/3.72  tff(c_631, plain, (![B_21, B_282, D_283]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_21, k2_relat_1(u1_waybel_0('#skF_4', B_282))), D_283) | ~r3_waybel_9('#skF_4', B_282, D_283) | ~m1_subset_1(D_283, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_282) | ~v4_orders_2(B_282) | v2_struct_0(B_282) | ~m1_subset_1('#skF_3'('#skF_4', B_282, D_283, D_283), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_282, '#skF_4') | r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_282))) | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_282)), B_21) | ~m1_subset_1(B_21, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_625])).
% 11.27/3.72  tff(c_637, plain, (![B_21, B_282, D_283]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_21, k2_relat_1(u1_waybel_0('#skF_4', B_282))), D_283) | ~r3_waybel_9('#skF_4', B_282, D_283) | ~m1_subset_1(D_283, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_282) | ~v4_orders_2(B_282) | v2_struct_0(B_282) | ~m1_subset_1('#skF_3'('#skF_4', B_282, D_283, D_283), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_282, '#skF_4') | r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_282))) | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_282)), B_21) | ~m1_subset_1(B_21, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_87, c_631])).
% 11.27/3.72  tff(c_1096, plain, (![B_365, B_366, D_367]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_365, k2_relat_1(u1_waybel_0('#skF_4', B_366))), D_367) | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_366)), B_365) | ~m1_subset_1(B_365, u1_struct_0('#skF_4')) | r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_366))) | ~r3_waybel_9('#skF_4', B_366, D_367) | ~v11_waybel_0(B_366, '#skF_4') | ~m1_subset_1(D_367, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_366) | ~v4_orders_2(B_366) | v2_struct_0(B_366) | ~l1_waybel_0(B_366, '#skF_4'))), inference(resolution, [status(thm)], [c_966, c_637])).
% 11.27/3.72  tff(c_1104, plain, (![B_366, D_367]: (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_366)), D_367) | r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_366))) | ~r3_waybel_9('#skF_4', B_366, D_367) | ~v11_waybel_0(B_366, '#skF_4') | ~m1_subset_1(D_367, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_366) | ~v4_orders_2(B_366) | v2_struct_0(B_366) | ~l1_waybel_0(B_366, '#skF_4'))), inference(resolution, [status(thm)], [c_1096, c_14])).
% 11.27/3.72  tff(c_1111, plain, (![B_368, D_369]: (~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_368)), D_369) | r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_368))) | ~r3_waybel_9('#skF_4', B_368, D_369) | ~v11_waybel_0(B_368, '#skF_4') | ~m1_subset_1(D_369, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_368) | ~v4_orders_2(B_368) | v2_struct_0(B_368) | ~l1_waybel_0(B_368, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_87, c_1104])).
% 11.27/3.72  tff(c_1162, plain, (![B_373, D_374]: (r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_373))) | ~r3_waybel_9('#skF_4', B_373, D_374) | ~v11_waybel_0(B_373, '#skF_4') | ~m1_subset_1(D_374, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_373) | ~v4_orders_2(B_373) | v2_struct_0(B_373) | ~l1_waybel_0(B_373, '#skF_4'))), inference(resolution, [status(thm)], [c_230, c_1111])).
% 11.27/3.72  tff(c_1164, plain, (r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6'))) | ~v11_waybel_0('#skF_6', '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1162])).
% 11.27/3.72  tff(c_1167, plain, (r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_58, c_64, c_52, c_1164])).
% 11.27/3.72  tff(c_1168, plain, (r2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_62, c_1167])).
% 11.27/3.72  tff(c_137, plain, (![A_153, C_154]: (r1_lattice3(A_153, C_154, k2_yellow_0(A_153, C_154)) | ~r2_yellow_0(A_153, C_154) | ~m1_subset_1(k2_yellow_0(A_153, C_154), u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v5_orders_2(A_153))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.27/3.72  tff(c_149, plain, (![A_176, B_177]: (r1_lattice3(A_176, k2_relat_1(B_177), k2_yellow_0(A_176, k2_relat_1(B_177))) | ~r2_yellow_0(A_176, k2_relat_1(B_177)) | ~m1_subset_1(k5_yellow_2(A_176, B_177), u1_struct_0(A_176)) | ~l1_orders_2(A_176) | ~v5_orders_2(A_176) | ~v1_relat_1(B_177) | ~l1_orders_2(A_176) | v2_struct_0(A_176))), inference(superposition, [status(thm), theory('equality')], [c_34, c_137])).
% 11.27/3.72  tff(c_153, plain, (![A_178, B_179]: (r1_lattice3(A_178, k2_relat_1(B_179), k5_yellow_2(A_178, B_179)) | ~r2_yellow_0(A_178, k2_relat_1(B_179)) | ~m1_subset_1(k5_yellow_2(A_178, B_179), u1_struct_0(A_178)) | ~l1_orders_2(A_178) | ~v5_orders_2(A_178) | ~v1_relat_1(B_179) | ~l1_orders_2(A_178) | v2_struct_0(A_178) | ~v1_relat_1(B_179) | ~l1_orders_2(A_178) | v2_struct_0(A_178))), inference(superposition, [status(thm), theory('equality')], [c_34, c_149])).
% 11.27/3.72  tff(c_156, plain, (![A_33, B_35]: (r1_lattice3(A_33, k2_relat_1(u1_waybel_0(A_33, B_35)), k1_waybel_9(A_33, B_35)) | ~r2_yellow_0(A_33, k2_relat_1(u1_waybel_0(A_33, B_35))) | ~m1_subset_1(k5_yellow_2(A_33, u1_waybel_0(A_33, B_35)), u1_struct_0(A_33)) | ~l1_orders_2(A_33) | ~v5_orders_2(A_33) | ~v1_relat_1(u1_waybel_0(A_33, B_35)) | ~l1_orders_2(A_33) | v2_struct_0(A_33) | ~v1_relat_1(u1_waybel_0(A_33, B_35)) | ~l1_orders_2(A_33) | v2_struct_0(A_33) | ~l1_waybel_0(B_35, A_33) | ~l1_orders_2(A_33) | v2_struct_0(A_33))), inference(superposition, [status(thm), theory('equality')], [c_32, c_153])).
% 11.27/3.72  tff(c_24, plain, (![A_9, B_21, C_27]: (m1_subset_1('#skF_1'(A_9, B_21, C_27), u1_struct_0(A_9)) | k2_yellow_0(A_9, C_27)=B_21 | ~r1_lattice3(A_9, C_27, B_21) | ~m1_subset_1(B_21, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.27/3.72  tff(c_22, plain, (![A_9, C_27, B_21]: (r1_lattice3(A_9, C_27, '#skF_1'(A_9, B_21, C_27)) | k2_yellow_0(A_9, C_27)=B_21 | ~r1_lattice3(A_9, C_27, B_21) | ~m1_subset_1(B_21, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.27/3.72  tff(c_761, plain, (![A_316, B_317, B_318]: (r1_orders_2(A_316, '#skF_1'(A_316, B_317, k2_relat_1(u1_waybel_0(A_316, B_318))), k1_waybel_9(A_316, B_318)) | ~m1_subset_1('#skF_1'(A_316, B_317, k2_relat_1(u1_waybel_0(A_316, B_318))), u1_struct_0(A_316)) | ~r2_yellow_0(A_316, k2_relat_1(u1_waybel_0(A_316, B_318))) | ~m1_subset_1(k1_waybel_9(A_316, B_318), u1_struct_0(A_316)) | ~v1_relat_1(u1_waybel_0(A_316, B_318)) | ~l1_waybel_0(B_318, A_316) | v2_struct_0(A_316) | k2_yellow_0(A_316, k2_relat_1(u1_waybel_0(A_316, B_318)))=B_317 | ~r1_lattice3(A_316, k2_relat_1(u1_waybel_0(A_316, B_318)), B_317) | ~m1_subset_1(B_317, u1_struct_0(A_316)) | ~l1_orders_2(A_316) | ~v5_orders_2(A_316))), inference(resolution, [status(thm)], [c_22, c_354])).
% 11.27/3.72  tff(c_20, plain, (![A_9, B_21, C_27]: (~r1_orders_2(A_9, '#skF_1'(A_9, B_21, C_27), B_21) | k2_yellow_0(A_9, C_27)=B_21 | ~r1_lattice3(A_9, C_27, B_21) | ~m1_subset_1(B_21, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.27/3.72  tff(c_772, plain, (![A_319, B_320]: (~m1_subset_1('#skF_1'(A_319, k1_waybel_9(A_319, B_320), k2_relat_1(u1_waybel_0(A_319, B_320))), u1_struct_0(A_319)) | ~r2_yellow_0(A_319, k2_relat_1(u1_waybel_0(A_319, B_320))) | ~v1_relat_1(u1_waybel_0(A_319, B_320)) | ~l1_waybel_0(B_320, A_319) | v2_struct_0(A_319) | k2_yellow_0(A_319, k2_relat_1(u1_waybel_0(A_319, B_320)))=k1_waybel_9(A_319, B_320) | ~r1_lattice3(A_319, k2_relat_1(u1_waybel_0(A_319, B_320)), k1_waybel_9(A_319, B_320)) | ~m1_subset_1(k1_waybel_9(A_319, B_320), u1_struct_0(A_319)) | ~l1_orders_2(A_319) | ~v5_orders_2(A_319))), inference(resolution, [status(thm)], [c_761, c_20])).
% 11.27/3.72  tff(c_783, plain, (![A_321, B_322]: (~r2_yellow_0(A_321, k2_relat_1(u1_waybel_0(A_321, B_322))) | ~v1_relat_1(u1_waybel_0(A_321, B_322)) | ~l1_waybel_0(B_322, A_321) | v2_struct_0(A_321) | k2_yellow_0(A_321, k2_relat_1(u1_waybel_0(A_321, B_322)))=k1_waybel_9(A_321, B_322) | ~r1_lattice3(A_321, k2_relat_1(u1_waybel_0(A_321, B_322)), k1_waybel_9(A_321, B_322)) | ~m1_subset_1(k1_waybel_9(A_321, B_322), u1_struct_0(A_321)) | ~l1_orders_2(A_321) | ~v5_orders_2(A_321))), inference(resolution, [status(thm)], [c_24, c_772])).
% 11.27/3.72  tff(c_798, plain, (![A_323, B_324]: (k2_yellow_0(A_323, k2_relat_1(u1_waybel_0(A_323, B_324)))=k1_waybel_9(A_323, B_324) | ~m1_subset_1(k1_waybel_9(A_323, B_324), u1_struct_0(A_323)) | ~r2_yellow_0(A_323, k2_relat_1(u1_waybel_0(A_323, B_324))) | ~m1_subset_1(k5_yellow_2(A_323, u1_waybel_0(A_323, B_324)), u1_struct_0(A_323)) | ~v5_orders_2(A_323) | ~v1_relat_1(u1_waybel_0(A_323, B_324)) | ~l1_waybel_0(B_324, A_323) | ~l1_orders_2(A_323) | v2_struct_0(A_323))), inference(resolution, [status(thm)], [c_156, c_783])).
% 11.27/3.72  tff(c_801, plain, (![A_33, B_35]: (k2_yellow_0(A_33, k2_relat_1(u1_waybel_0(A_33, B_35)))=k1_waybel_9(A_33, B_35) | ~m1_subset_1(k1_waybel_9(A_33, B_35), u1_struct_0(A_33)) | ~r2_yellow_0(A_33, k2_relat_1(u1_waybel_0(A_33, B_35))) | ~m1_subset_1(k1_waybel_9(A_33, B_35), u1_struct_0(A_33)) | ~v5_orders_2(A_33) | ~v1_relat_1(u1_waybel_0(A_33, B_35)) | ~l1_waybel_0(B_35, A_33) | ~l1_orders_2(A_33) | v2_struct_0(A_33) | ~l1_waybel_0(B_35, A_33) | ~l1_orders_2(A_33) | v2_struct_0(A_33))), inference(superposition, [status(thm), theory('equality')], [c_32, c_798])).
% 11.27/3.72  tff(c_1173, plain, (k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))=k1_waybel_9('#skF_4', '#skF_6') | ~m1_subset_1(k1_waybel_9('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6')) | ~l1_waybel_0('#skF_6', '#skF_4') | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1168, c_801])).
% 11.27/3.72  tff(c_1184, plain, (k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))=k1_waybel_9('#skF_4', '#skF_6') | ~m1_subset_1(k1_waybel_9('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_56, c_74, c_1173])).
% 11.27/3.72  tff(c_1185, plain, (k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))=k1_waybel_9('#skF_4', '#skF_6') | ~m1_subset_1(k1_waybel_9('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_582, c_1184])).
% 11.27/3.72  tff(c_1194, plain, (~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1185])).
% 11.27/3.72  tff(c_1197, plain, (~l1_waybel_0('#skF_6', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_117, c_1194])).
% 11.27/3.72  tff(c_1201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_231, c_56, c_1197])).
% 11.27/3.72  tff(c_1203, plain, (v1_relat_1(u1_waybel_0('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_1185])).
% 11.27/3.72  tff(c_638, plain, (![A_284, B_285, D_286, B_287]: (m1_subset_1('#skF_3'(A_284, B_285, D_286, D_286), u1_struct_0(A_284)) | r1_orders_2(A_284, '#skF_1'(A_284, B_287, k2_relset_1(u1_struct_0(B_285), u1_struct_0(A_284), u1_waybel_0(A_284, B_285))), D_286) | ~m1_subset_1('#skF_1'(A_284, B_287, k2_relset_1(u1_struct_0(B_285), u1_struct_0(A_284), u1_waybel_0(A_284, B_285))), u1_struct_0(A_284)) | ~r3_waybel_9(A_284, B_285, D_286) | ~m1_subset_1(D_286, u1_struct_0(A_284)) | ~l1_waybel_0(B_285, A_284) | ~v7_waybel_0(B_285) | ~v4_orders_2(B_285) | v2_struct_0(B_285) | ~l1_waybel_9(A_284) | ~v1_compts_1(A_284) | ~v2_lattice3(A_284) | ~v1_lattice3(A_284) | ~v4_orders_2(A_284) | ~v3_orders_2(A_284) | ~v8_pre_topc(A_284) | ~v2_pre_topc(A_284) | k2_yellow_0(A_284, k2_relset_1(u1_struct_0(B_285), u1_struct_0(A_284), u1_waybel_0(A_284, B_285)))=B_287 | ~r1_lattice3(A_284, k2_relset_1(u1_struct_0(B_285), u1_struct_0(A_284), u1_waybel_0(A_284, B_285)), B_287) | ~m1_subset_1(B_287, u1_struct_0(A_284)) | ~l1_orders_2(A_284) | ~v5_orders_2(A_284))), inference(resolution, [status(thm)], [c_22, c_232])).
% 11.27/3.72  tff(c_1026, plain, (![A_359, B_360, D_361, B_362]: (m1_subset_1('#skF_3'(A_359, B_360, D_361, D_361), u1_struct_0(A_359)) | r1_orders_2(A_359, '#skF_1'(A_359, B_362, k2_relset_1(u1_struct_0(B_360), u1_struct_0(A_359), u1_waybel_0(A_359, B_360))), D_361) | ~r3_waybel_9(A_359, B_360, D_361) | ~m1_subset_1(D_361, u1_struct_0(A_359)) | ~l1_waybel_0(B_360, A_359) | ~v7_waybel_0(B_360) | ~v4_orders_2(B_360) | v2_struct_0(B_360) | ~l1_waybel_9(A_359) | ~v1_compts_1(A_359) | ~v2_lattice3(A_359) | ~v1_lattice3(A_359) | ~v4_orders_2(A_359) | ~v3_orders_2(A_359) | ~v8_pre_topc(A_359) | ~v2_pre_topc(A_359) | k2_yellow_0(A_359, k2_relset_1(u1_struct_0(B_360), u1_struct_0(A_359), u1_waybel_0(A_359, B_360)))=B_362 | ~r1_lattice3(A_359, k2_relset_1(u1_struct_0(B_360), u1_struct_0(A_359), u1_waybel_0(A_359, B_360)), B_362) | ~m1_subset_1(B_362, u1_struct_0(A_359)) | ~l1_orders_2(A_359) | ~v5_orders_2(A_359))), inference(resolution, [status(thm)], [c_24, c_638])).
% 11.27/3.72  tff(c_1386, plain, (![A_403, B_404, D_405]: (m1_subset_1('#skF_3'(A_403, B_404, D_405, D_405), u1_struct_0(A_403)) | ~r3_waybel_9(A_403, B_404, D_405) | ~l1_waybel_0(B_404, A_403) | ~v7_waybel_0(B_404) | ~v4_orders_2(B_404) | v2_struct_0(B_404) | ~l1_waybel_9(A_403) | ~v1_compts_1(A_403) | ~v2_lattice3(A_403) | ~v1_lattice3(A_403) | ~v4_orders_2(A_403) | ~v3_orders_2(A_403) | ~v8_pre_topc(A_403) | ~v2_pre_topc(A_403) | k2_yellow_0(A_403, k2_relset_1(u1_struct_0(B_404), u1_struct_0(A_403), u1_waybel_0(A_403, B_404)))=D_405 | ~r1_lattice3(A_403, k2_relset_1(u1_struct_0(B_404), u1_struct_0(A_403), u1_waybel_0(A_403, B_404)), D_405) | ~m1_subset_1(D_405, u1_struct_0(A_403)) | ~l1_orders_2(A_403) | ~v5_orders_2(A_403))), inference(resolution, [status(thm)], [c_1026, c_20])).
% 11.27/3.72  tff(c_1388, plain, (![B_56, D_68]: (m1_subset_1('#skF_3'('#skF_4', B_56, D_68, D_68), u1_struct_0('#skF_4')) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | k2_yellow_0('#skF_4', k2_relset_1(u1_struct_0(B_56), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_56)))=D_68 | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~r3_waybel_9('#skF_4', B_56, D_68) | ~v11_waybel_0(B_56, '#skF_4') | ~m1_subset_1(D_68, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_56, '#skF_4') | ~v7_waybel_0(B_56) | ~v4_orders_2(B_56) | v2_struct_0(B_56))), inference(resolution, [status(thm)], [c_216, c_1386])).
% 11.27/3.72  tff(c_1405, plain, (![B_406, D_407]: (m1_subset_1('#skF_3'('#skF_4', B_406, D_407, D_407), u1_struct_0('#skF_4')) | k2_yellow_0('#skF_4', k2_relset_1(u1_struct_0(B_406), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_406)))=D_407 | ~r3_waybel_9('#skF_4', B_406, D_407) | ~v11_waybel_0(B_406, '#skF_4') | ~m1_subset_1(D_407, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_406, '#skF_4') | ~v7_waybel_0(B_406) | ~v4_orders_2(B_406) | v2_struct_0(B_406))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_87, c_82, c_80, c_78, c_76, c_72, c_70, c_68, c_66, c_1388])).
% 11.27/3.72  tff(c_2557, plain, (![B_146, D_407]: (m1_subset_1('#skF_3'('#skF_4', B_146, D_407, D_407), u1_struct_0('#skF_4')) | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_146)))=D_407 | ~r3_waybel_9('#skF_4', B_146, D_407) | ~v11_waybel_0(B_146, '#skF_4') | ~m1_subset_1(D_407, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_146, '#skF_4') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~l1_waybel_0(B_146, '#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_1405])).
% 11.27/3.72  tff(c_2577, plain, (![B_3704, D_3705]: (m1_subset_1('#skF_3'('#skF_4', B_3704, D_3705, D_3705), u1_struct_0('#skF_4')) | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_3704)))=D_3705 | ~r3_waybel_9('#skF_4', B_3704, D_3705) | ~v11_waybel_0(B_3704, '#skF_4') | ~m1_subset_1(D_3705, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_3704) | ~v4_orders_2(B_3704) | v2_struct_0(B_3704) | ~l1_waybel_0(B_3704, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_2557])).
% 11.27/3.72  tff(c_549, plain, (![B_21, B_257, D_256]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_21, k2_relat_1(u1_waybel_0('#skF_4', B_257))), D_256) | ~m1_subset_1('#skF_1'('#skF_4', B_21, k2_relat_1(u1_waybel_0('#skF_4', B_257))), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_257, D_256) | ~m1_subset_1(D_256, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_257) | ~v4_orders_2(B_257) | v2_struct_0(B_257) | ~m1_subset_1('#skF_3'('#skF_4', B_257, D_256, D_256), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_257, '#skF_4') | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_257)))=B_21 | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_257)), B_21) | ~m1_subset_1(B_21, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_532])).
% 11.27/3.72  tff(c_656, plain, (![B_291, B_292, D_293]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_291, k2_relat_1(u1_waybel_0('#skF_4', B_292))), D_293) | ~m1_subset_1('#skF_1'('#skF_4', B_291, k2_relat_1(u1_waybel_0('#skF_4', B_292))), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_292, D_293) | ~m1_subset_1(D_293, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_292) | ~v4_orders_2(B_292) | v2_struct_0(B_292) | ~m1_subset_1('#skF_3'('#skF_4', B_292, D_293, D_293), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_292, '#skF_4') | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_292)))=B_291 | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_292)), B_291) | ~m1_subset_1(B_291, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_87, c_549])).
% 11.27/3.72  tff(c_659, plain, (![B_21, B_292, D_293]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_21, k2_relat_1(u1_waybel_0('#skF_4', B_292))), D_293) | ~r3_waybel_9('#skF_4', B_292, D_293) | ~m1_subset_1(D_293, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_292) | ~v4_orders_2(B_292) | v2_struct_0(B_292) | ~m1_subset_1('#skF_3'('#skF_4', B_292, D_293, D_293), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_292, '#skF_4') | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_292)))=B_21 | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_292)), B_21) | ~m1_subset_1(B_21, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_656])).
% 11.27/3.72  tff(c_665, plain, (![B_21, B_292, D_293]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_21, k2_relat_1(u1_waybel_0('#skF_4', B_292))), D_293) | ~r3_waybel_9('#skF_4', B_292, D_293) | ~m1_subset_1(D_293, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_292) | ~v4_orders_2(B_292) | v2_struct_0(B_292) | ~m1_subset_1('#skF_3'('#skF_4', B_292, D_293, D_293), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_292, '#skF_4') | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_292)))=B_21 | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_292)), B_21) | ~m1_subset_1(B_21, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_87, c_659])).
% 11.27/3.72  tff(c_7199, plain, (![B_6455, B_6456, D_6457]: (r1_orders_2('#skF_4', '#skF_1'('#skF_4', B_6455, k2_relat_1(u1_waybel_0('#skF_4', B_6456))), D_6457) | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_6456)))=B_6455 | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_6456)), B_6455) | ~m1_subset_1(B_6455, u1_struct_0('#skF_4')) | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_6456)))=D_6457 | ~r3_waybel_9('#skF_4', B_6456, D_6457) | ~v11_waybel_0(B_6456, '#skF_4') | ~m1_subset_1(D_6457, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_6456) | ~v4_orders_2(B_6456) | v2_struct_0(B_6456) | ~l1_waybel_0(B_6456, '#skF_4'))), inference(resolution, [status(thm)], [c_2577, c_665])).
% 11.27/3.72  tff(c_7203, plain, (![B_6456, D_6457]: (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_6456)), D_6457) | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_6456)))=D_6457 | ~r3_waybel_9('#skF_4', B_6456, D_6457) | ~v11_waybel_0(B_6456, '#skF_4') | ~m1_subset_1(D_6457, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_6456) | ~v4_orders_2(B_6456) | v2_struct_0(B_6456) | ~l1_waybel_0(B_6456, '#skF_4'))), inference(resolution, [status(thm)], [c_7199, c_20])).
% 11.27/3.72  tff(c_7255, plain, (![B_6487, D_6488]: (~r1_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_6487)), D_6488) | k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_6487)))=D_6488 | ~r3_waybel_9('#skF_4', B_6487, D_6488) | ~v11_waybel_0(B_6487, '#skF_4') | ~m1_subset_1(D_6488, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_6487) | ~v4_orders_2(B_6487) | v2_struct_0(B_6487) | ~l1_waybel_0(B_6487, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_87, c_7203])).
% 11.27/3.72  tff(c_7328, plain, (![B_6518, D_6519]: (k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_6518)))=D_6519 | ~r3_waybel_9('#skF_4', B_6518, D_6519) | ~v11_waybel_0(B_6518, '#skF_4') | ~m1_subset_1(D_6519, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_6518) | ~v4_orders_2(B_6518) | v2_struct_0(B_6518) | ~l1_waybel_0(B_6518, '#skF_4'))), inference(resolution, [status(thm)], [c_230, c_7255])).
% 11.27/3.72  tff(c_7346, plain, (k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))='#skF_5' | ~v11_waybel_0('#skF_6', '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_7328])).
% 11.27/3.72  tff(c_7349, plain, (k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))='#skF_5' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_60, c_58, c_64, c_52, c_7346])).
% 11.27/3.72  tff(c_7350, plain, (k2_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_62, c_7349])).
% 11.27/3.72  tff(c_7452, plain, (k5_yellow_2('#skF_4', u1_waybel_0('#skF_4', '#skF_6'))='#skF_5' | ~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6')) | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7350, c_34])).
% 11.27/3.72  tff(c_7530, plain, (k5_yellow_2('#skF_4', u1_waybel_0('#skF_4', '#skF_6'))='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_1203, c_7452])).
% 11.27/3.72  tff(c_7531, plain, (k5_yellow_2('#skF_4', u1_waybel_0('#skF_4', '#skF_6'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_582, c_7530])).
% 11.27/3.72  tff(c_7591, plain, (k1_waybel_9('#skF_4', '#skF_6')='#skF_5' | ~l1_waybel_0('#skF_6', '#skF_4') | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7531, c_32])).
% 11.27/3.72  tff(c_7659, plain, (k1_waybel_9('#skF_4', '#skF_6')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_56, c_7591])).
% 11.27/3.72  tff(c_7661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_582, c_48, c_7659])).
% 11.27/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.27/3.72  
% 11.27/3.72  Inference rules
% 11.27/3.72  ----------------------
% 11.27/3.72  #Ref     : 0
% 11.27/3.72  #Sup     : 1553
% 11.27/3.72  #Fact    : 4
% 11.27/3.72  #Define  : 0
% 11.27/3.72  #Split   : 9
% 11.27/3.72  #Chain   : 0
% 11.27/3.72  #Close   : 0
% 11.27/3.72  
% 11.27/3.72  Ordering : KBO
% 11.27/3.72  
% 11.27/3.72  Simplification rules
% 11.27/3.72  ----------------------
% 11.27/3.72  #Subsume      : 237
% 11.27/3.72  #Demod        : 1111
% 11.27/3.72  #Tautology    : 39
% 11.27/3.72  #SimpNegUnit  : 129
% 11.27/3.72  #BackRed      : 0
% 11.27/3.72  
% 11.27/3.72  #Partial instantiations: 3248
% 11.27/3.72  #Strategies tried      : 1
% 11.27/3.72  
% 11.27/3.72  Timing (in seconds)
% 11.27/3.72  ----------------------
% 11.27/3.72  Preprocessing        : 0.39
% 11.27/3.72  Parsing              : 0.20
% 11.27/3.72  CNF conversion       : 0.03
% 11.27/3.72  Main loop            : 2.54
% 11.27/3.72  Inferencing          : 0.88
% 11.27/3.72  Reduction            : 0.67
% 11.27/3.72  Demodulation         : 0.48
% 11.27/3.72  BG Simplification    : 0.09
% 11.27/3.72  Subsumption          : 0.76
% 11.27/3.72  Abstraction          : 0.14
% 11.27/3.72  MUC search           : 0.00
% 11.27/3.72  Cooper               : 0.00
% 11.27/3.72  Total                : 2.99
% 11.27/3.72  Index Insertion      : 0.00
% 11.27/3.72  Index Deletion       : 0.00
% 11.27/3.72  Index Matching       : 0.00
% 11.27/3.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
