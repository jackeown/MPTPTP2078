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
% DateTime   : Thu Dec  3 10:31:20 EST 2020

% Result     : Theorem 20.28s
% Output     : CNFRefutation 20.72s
% Verified   : 
% Statistics : Number of formulae       :  276 (155012 expanded)
%              Number of leaves         :   61 (62876 expanded)
%              Depth                    :   80
%              Number of atoms          : 1633 (1439777 expanded)
%              Number of equality atoms :   79 (60709 expanded)
%              Maximal formula depth    :   29 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r3_waybel_9 > r3_orders_2 > r2_lattice3 > r1_orders_2 > v10_waybel_0 > r1_yellow_0 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_relat_1 > v1_lattice3 > v1_funct_1 > v1_compts_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_yellow_2 > k4_waybel_1 > k2_zfmisc_1 > k1_yellow_0 > k1_waybel_2 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k4_yellow_2,type,(
    k4_yellow_2: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(v10_waybel_0,type,(
    v10_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k4_waybel_1,type,(
    k4_waybel_1: ( $i * $i ) > $i )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(k1_waybel_2,type,(
    k1_waybel_2: ( $i * $i ) > $i )).

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_272,negated_conjecture,(
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
                    & v10_waybel_0(C,A)
                    & r3_waybel_9(A,C,B) )
                 => B = k1_waybel_2(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_waybel_9)).

tff(f_132,axiom,(
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

tff(f_106,axiom,(
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

tff(f_179,axiom,(
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
                      & v10_waybel_0(B,A)
                      & r3_waybel_9(A,B,C) )
                   => r2_lattice3(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B)),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l48_waybel_9)).

tff(f_96,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r1_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r2_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r2_lattice3(A,B,D)
                   => r1_orders_2(A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_229,axiom,(
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
                       => ( r2_lattice3(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B)),E)
                         => r3_orders_2(A,D,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_waybel_9)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( l1_waybel_0(B,A)
         => k1_waybel_2(A,B) = k4_yellow_2(A,u1_waybel_0(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_2)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r1_yellow_0(A,B)
           => ( C = k1_yellow_0(A,B)
            <=> ( r2_lattice3(A,B,C)
                & ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_lattice3(A,B,D)
                     => r1_orders_2(A,C,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

tff(f_126,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( v1_relat_1(B)
         => k4_yellow_2(A,B) = k1_yellow_0(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_2)).

tff(c_58,plain,(
    k1_waybel_2('#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_76,plain,(
    l1_waybel_9('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_93,plain,(
    ! [A_146] :
      ( l1_orders_2(A_146)
      | ~ l1_waybel_9(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_97,plain,(
    l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_93])).

tff(c_74,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_66,plain,(
    l1_waybel_0('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_70,plain,(
    v4_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_68,plain,(
    v7_waybel_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_62,plain,(
    v10_waybel_0('#skF_8','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_60,plain,(
    r3_waybel_9('#skF_6','#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_6,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_167,B_168] :
      ( m1_subset_1(u1_waybel_0(A_167,B_168),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_168),u1_struct_0(A_167))))
      | ~ l1_waybel_0(B_168,A_167)
      | ~ l1_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( k2_relset_1(A_4,B_5,C_6) = k2_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,(
    ! [B_168,A_167] :
      ( k2_relset_1(u1_struct_0(B_168),u1_struct_0(A_167),u1_waybel_0(A_167,B_168)) = k2_relat_1(u1_waybel_0(A_167,B_168))
      | ~ l1_waybel_0(B_168,A_167)
      | ~ l1_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_121,c_4])).

tff(c_92,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_90,plain,(
    v8_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_88,plain,(
    v3_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_86,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_84,plain,(
    v5_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_82,plain,(
    v1_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_80,plain,(
    v2_lattice3('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_78,plain,(
    v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_52,plain,(
    ! [A_58,B_74,D_86] :
      ( m1_subset_1('#skF_4'(A_58,B_74,D_86,D_86),u1_struct_0(A_58))
      | r2_lattice3(A_58,k2_relset_1(u1_struct_0(B_74),u1_struct_0(A_58),u1_waybel_0(A_58,B_74)),D_86)
      | ~ r3_waybel_9(A_58,B_74,D_86)
      | ~ v10_waybel_0(B_74,A_58)
      | ~ m1_subset_1(D_86,u1_struct_0(A_58))
      | ~ l1_waybel_0(B_74,A_58)
      | ~ v7_waybel_0(B_74)
      | ~ v4_orders_2(B_74)
      | v2_struct_0(B_74)
      | ~ l1_waybel_9(A_58)
      | ~ v1_compts_1(A_58)
      | ~ v2_lattice3(A_58)
      | ~ v1_lattice3(A_58)
      | ~ v5_orders_2(A_58)
      | ~ v4_orders_2(A_58)
      | ~ v3_orders_2(A_58)
      | ~ v8_pre_topc(A_58)
      | ~ v2_pre_topc(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_64,plain,(
    ! [D_145] :
      ( v5_pre_topc(k4_waybel_1('#skF_6',D_145),'#skF_6','#skF_6')
      | ~ m1_subset_1(D_145,u1_struct_0('#skF_6')) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_767,plain,(
    ! [A_343,B_344,D_345] :
      ( ~ v5_pre_topc(k4_waybel_1(A_343,'#skF_4'(A_343,B_344,D_345,D_345)),A_343,A_343)
      | r2_lattice3(A_343,k2_relset_1(u1_struct_0(B_344),u1_struct_0(A_343),u1_waybel_0(A_343,B_344)),D_345)
      | ~ r3_waybel_9(A_343,B_344,D_345)
      | ~ v10_waybel_0(B_344,A_343)
      | ~ m1_subset_1(D_345,u1_struct_0(A_343))
      | ~ l1_waybel_0(B_344,A_343)
      | ~ v7_waybel_0(B_344)
      | ~ v4_orders_2(B_344)
      | v2_struct_0(B_344)
      | ~ l1_waybel_9(A_343)
      | ~ v1_compts_1(A_343)
      | ~ v2_lattice3(A_343)
      | ~ v1_lattice3(A_343)
      | ~ v5_orders_2(A_343)
      | ~ v4_orders_2(A_343)
      | ~ v3_orders_2(A_343)
      | ~ v8_pre_topc(A_343)
      | ~ v2_pre_topc(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_770,plain,(
    ! [B_344,D_345] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_344),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_344)),D_345)
      | ~ r3_waybel_9('#skF_6',B_344,D_345)
      | ~ v10_waybel_0(B_344,'#skF_6')
      | ~ m1_subset_1(D_345,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_344,'#skF_6')
      | ~ v7_waybel_0(B_344)
      | ~ v4_orders_2(B_344)
      | v2_struct_0(B_344)
      | ~ l1_waybel_9('#skF_6')
      | ~ v1_compts_1('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ v8_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_6',B_344,D_345,D_345),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_64,c_767])).

tff(c_785,plain,(
    ! [B_350,D_351] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_350),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_350)),D_351)
      | ~ r3_waybel_9('#skF_6',B_350,D_351)
      | ~ v10_waybel_0(B_350,'#skF_6')
      | ~ m1_subset_1(D_351,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_350,'#skF_6')
      | ~ v7_waybel_0(B_350)
      | ~ v4_orders_2(B_350)
      | v2_struct_0(B_350)
      | ~ m1_subset_1('#skF_4'('#skF_6',B_350,D_351,D_351),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_770])).

tff(c_788,plain,(
    ! [B_74,D_86] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_74),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_74)),D_86)
      | ~ r3_waybel_9('#skF_6',B_74,D_86)
      | ~ v10_waybel_0(B_74,'#skF_6')
      | ~ m1_subset_1(D_86,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_74,'#skF_6')
      | ~ v7_waybel_0(B_74)
      | ~ v4_orders_2(B_74)
      | v2_struct_0(B_74)
      | ~ l1_waybel_9('#skF_6')
      | ~ v1_compts_1('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ v8_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_785])).

tff(c_792,plain,(
    ! [B_352,D_353] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_352),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_352)),D_353)
      | ~ r3_waybel_9('#skF_6',B_352,D_353)
      | ~ v10_waybel_0(B_352,'#skF_6')
      | ~ m1_subset_1(D_353,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_352,'#skF_6')
      | ~ v7_waybel_0(B_352)
      | ~ v4_orders_2(B_352)
      | v2_struct_0(B_352) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_788])).

tff(c_796,plain,(
    ! [B_168,D_353] :
      ( r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)),D_353)
      | ~ r3_waybel_9('#skF_6',B_168,D_353)
      | ~ v10_waybel_0(B_168,'#skF_6')
      | ~ m1_subset_1(D_353,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ v7_waybel_0(B_168)
      | ~ v4_orders_2(B_168)
      | v2_struct_0(B_168)
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_792])).

tff(c_797,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_796])).

tff(c_800,plain,(
    ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_797])).

tff(c_804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_800])).

tff(c_805,plain,(
    ! [B_168,D_353] :
      ( r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)),D_353)
      | ~ r3_waybel_9('#skF_6',B_168,D_353)
      | ~ v10_waybel_0(B_168,'#skF_6')
      | ~ m1_subset_1(D_353,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ v7_waybel_0(B_168)
      | ~ v4_orders_2(B_168)
      | v2_struct_0(B_168)
      | ~ l1_waybel_0(B_168,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_34,plain,(
    ! [A_24,B_38,C_45] :
      ( m1_subset_1('#skF_2'(A_24,B_38,C_45),u1_struct_0(A_24))
      | r1_yellow_0(A_24,B_38)
      | ~ r2_lattice3(A_24,B_38,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_156,plain,(
    ! [A_189,B_190,C_191] :
      ( r3_orders_2(A_189,B_190,C_191)
      | ~ r1_orders_2(A_189,B_190,C_191)
      | ~ m1_subset_1(C_191,u1_struct_0(A_189))
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189)
      | ~ v3_orders_2(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_162,plain,(
    ! [B_190] :
      ( r3_orders_2('#skF_6',B_190,'#skF_7')
      | ~ r1_orders_2('#skF_6',B_190,'#skF_7')
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_74,c_156])).

tff(c_167,plain,(
    ! [B_190] :
      ( r3_orders_2('#skF_6',B_190,'#skF_7')
      | ~ r1_orders_2('#skF_6',B_190,'#skF_7')
      | ~ m1_subset_1(B_190,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_97,c_162])).

tff(c_168,plain,(
    v2_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_167])).

tff(c_12,plain,(
    ! [A_11] :
      ( ~ v2_struct_0(A_11)
      | ~ v1_lattice3(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_171,plain,
    ( ~ v1_lattice3('#skF_6')
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_168,c_12])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_82,c_171])).

tff(c_177,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_167])).

tff(c_806,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_796])).

tff(c_791,plain,(
    ! [B_74,D_86] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_74),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_74)),D_86)
      | ~ r3_waybel_9('#skF_6',B_74,D_86)
      | ~ v10_waybel_0(B_74,'#skF_6')
      | ~ m1_subset_1(D_86,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_74,'#skF_6')
      | ~ v7_waybel_0(B_74)
      | ~ v4_orders_2(B_74)
      | v2_struct_0(B_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_788])).

tff(c_32,plain,(
    ! [A_24,B_38,C_45] :
      ( r2_lattice3(A_24,B_38,'#skF_2'(A_24,B_38,C_45))
      | r1_yellow_0(A_24,B_38)
      | ~ r2_lattice3(A_24,B_38,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_818,plain,(
    ! [A_358,B_359,D_360,E_361] :
      ( m1_subset_1('#skF_5'(A_358,B_359,D_360,D_360),u1_struct_0(A_358))
      | r3_orders_2(A_358,D_360,E_361)
      | ~ r2_lattice3(A_358,k2_relset_1(u1_struct_0(B_359),u1_struct_0(A_358),u1_waybel_0(A_358,B_359)),E_361)
      | ~ m1_subset_1(E_361,u1_struct_0(A_358))
      | ~ r3_waybel_9(A_358,B_359,D_360)
      | ~ m1_subset_1(D_360,u1_struct_0(A_358))
      | ~ l1_waybel_0(B_359,A_358)
      | ~ v7_waybel_0(B_359)
      | ~ v4_orders_2(B_359)
      | v2_struct_0(B_359)
      | ~ l1_waybel_9(A_358)
      | ~ v1_compts_1(A_358)
      | ~ v2_lattice3(A_358)
      | ~ v1_lattice3(A_358)
      | ~ v5_orders_2(A_358)
      | ~ v4_orders_2(A_358)
      | ~ v3_orders_2(A_358)
      | ~ v8_pre_topc(A_358)
      | ~ v2_pre_topc(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1394,plain,(
    ! [A_463,B_464,D_465,C_466] :
      ( m1_subset_1('#skF_5'(A_463,B_464,D_465,D_465),u1_struct_0(A_463))
      | r3_orders_2(A_463,D_465,'#skF_2'(A_463,k2_relset_1(u1_struct_0(B_464),u1_struct_0(A_463),u1_waybel_0(A_463,B_464)),C_466))
      | ~ m1_subset_1('#skF_2'(A_463,k2_relset_1(u1_struct_0(B_464),u1_struct_0(A_463),u1_waybel_0(A_463,B_464)),C_466),u1_struct_0(A_463))
      | ~ r3_waybel_9(A_463,B_464,D_465)
      | ~ m1_subset_1(D_465,u1_struct_0(A_463))
      | ~ l1_waybel_0(B_464,A_463)
      | ~ v7_waybel_0(B_464)
      | ~ v4_orders_2(B_464)
      | v2_struct_0(B_464)
      | ~ l1_waybel_9(A_463)
      | ~ v1_compts_1(A_463)
      | ~ v2_lattice3(A_463)
      | ~ v1_lattice3(A_463)
      | ~ v4_orders_2(A_463)
      | ~ v3_orders_2(A_463)
      | ~ v8_pre_topc(A_463)
      | ~ v2_pre_topc(A_463)
      | r1_yellow_0(A_463,k2_relset_1(u1_struct_0(B_464),u1_struct_0(A_463),u1_waybel_0(A_463,B_464)))
      | ~ r2_lattice3(A_463,k2_relset_1(u1_struct_0(B_464),u1_struct_0(A_463),u1_waybel_0(A_463,B_464)),C_466)
      | ~ m1_subset_1(C_466,u1_struct_0(A_463))
      | ~ l1_orders_2(A_463)
      | ~ v5_orders_2(A_463) ) ),
    inference(resolution,[status(thm)],[c_32,c_818])).

tff(c_2600,plain,(
    ! [A_671,B_672,D_673,C_674] :
      ( m1_subset_1('#skF_5'(A_671,B_672,D_673,D_673),u1_struct_0(A_671))
      | r3_orders_2(A_671,D_673,'#skF_2'(A_671,k2_relset_1(u1_struct_0(B_672),u1_struct_0(A_671),u1_waybel_0(A_671,B_672)),C_674))
      | ~ r3_waybel_9(A_671,B_672,D_673)
      | ~ m1_subset_1(D_673,u1_struct_0(A_671))
      | ~ l1_waybel_0(B_672,A_671)
      | ~ v7_waybel_0(B_672)
      | ~ v4_orders_2(B_672)
      | v2_struct_0(B_672)
      | ~ l1_waybel_9(A_671)
      | ~ v1_compts_1(A_671)
      | ~ v2_lattice3(A_671)
      | ~ v1_lattice3(A_671)
      | ~ v4_orders_2(A_671)
      | ~ v3_orders_2(A_671)
      | ~ v8_pre_topc(A_671)
      | ~ v2_pre_topc(A_671)
      | r1_yellow_0(A_671,k2_relset_1(u1_struct_0(B_672),u1_struct_0(A_671),u1_waybel_0(A_671,B_672)))
      | ~ r2_lattice3(A_671,k2_relset_1(u1_struct_0(B_672),u1_struct_0(A_671),u1_waybel_0(A_671,B_672)),C_674)
      | ~ m1_subset_1(C_674,u1_struct_0(A_671))
      | ~ l1_orders_2(A_671)
      | ~ v5_orders_2(A_671) ) ),
    inference(resolution,[status(thm)],[c_34,c_1394])).

tff(c_6491,plain,(
    ! [A_1131,B_1132,D_1133,C_1134] :
      ( m1_subset_1('#skF_5'(A_1131,B_1132,D_1133,D_1133),u1_struct_0(A_1131))
      | r3_orders_2(A_1131,D_1133,'#skF_2'(A_1131,k2_relat_1(u1_waybel_0(A_1131,B_1132)),C_1134))
      | ~ r3_waybel_9(A_1131,B_1132,D_1133)
      | ~ m1_subset_1(D_1133,u1_struct_0(A_1131))
      | ~ l1_waybel_0(B_1132,A_1131)
      | ~ v7_waybel_0(B_1132)
      | ~ v4_orders_2(B_1132)
      | v2_struct_0(B_1132)
      | ~ l1_waybel_9(A_1131)
      | ~ v1_compts_1(A_1131)
      | ~ v2_lattice3(A_1131)
      | ~ v1_lattice3(A_1131)
      | ~ v4_orders_2(A_1131)
      | ~ v3_orders_2(A_1131)
      | ~ v8_pre_topc(A_1131)
      | ~ v2_pre_topc(A_1131)
      | r1_yellow_0(A_1131,k2_relset_1(u1_struct_0(B_1132),u1_struct_0(A_1131),u1_waybel_0(A_1131,B_1132)))
      | ~ r2_lattice3(A_1131,k2_relset_1(u1_struct_0(B_1132),u1_struct_0(A_1131),u1_waybel_0(A_1131,B_1132)),C_1134)
      | ~ m1_subset_1(C_1134,u1_struct_0(A_1131))
      | ~ l1_orders_2(A_1131)
      | ~ v5_orders_2(A_1131)
      | ~ l1_waybel_0(B_1132,A_1131)
      | ~ l1_struct_0(A_1131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_2600])).

tff(c_6503,plain,(
    ! [B_74,D_1133,D_86] :
      ( m1_subset_1('#skF_5'('#skF_6',B_74,D_1133,D_1133),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1133,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_74)),D_86))
      | ~ r3_waybel_9('#skF_6',B_74,D_1133)
      | ~ m1_subset_1(D_1133,u1_struct_0('#skF_6'))
      | ~ l1_waybel_9('#skF_6')
      | ~ v1_compts_1('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ v8_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_74),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_74)))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6',B_74,D_86)
      | ~ v10_waybel_0(B_74,'#skF_6')
      | ~ m1_subset_1(D_86,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_74,'#skF_6')
      | ~ v7_waybel_0(B_74)
      | ~ v4_orders_2(B_74)
      | v2_struct_0(B_74) ) ),
    inference(resolution,[status(thm)],[c_791,c_6491])).

tff(c_6537,plain,(
    ! [B_1135,D_1136,D_1137] :
      ( m1_subset_1('#skF_5'('#skF_6',B_1135,D_1136,D_1136),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1136,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1135)),D_1137))
      | ~ r3_waybel_9('#skF_6',B_1135,D_1136)
      | ~ m1_subset_1(D_1136,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_1135),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1135)))
      | ~ r3_waybel_9('#skF_6',B_1135,D_1137)
      | ~ v10_waybel_0(B_1135,'#skF_6')
      | ~ m1_subset_1(D_1137,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_1135,'#skF_6')
      | ~ v7_waybel_0(B_1135)
      | ~ v4_orders_2(B_1135)
      | v2_struct_0(B_1135) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_84,c_97,c_92,c_90,c_88,c_86,c_82,c_80,c_78,c_76,c_6503])).

tff(c_6583,plain,(
    ! [B_168,D_1136,D_1137] :
      ( m1_subset_1('#skF_5'('#skF_6',B_168,D_1136,D_1136),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1136,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)),D_1137))
      | ~ r3_waybel_9('#skF_6',B_168,D_1136)
      | ~ m1_subset_1(D_1136,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)))
      | ~ r3_waybel_9('#skF_6',B_168,D_1137)
      | ~ v10_waybel_0(B_168,'#skF_6')
      | ~ m1_subset_1(D_1137,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ v7_waybel_0(B_168)
      | ~ v4_orders_2(B_168)
      | v2_struct_0(B_168)
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_6537])).

tff(c_6618,plain,(
    ! [B_1138,D_1139,D_1140] :
      ( m1_subset_1('#skF_5'('#skF_6',B_1138,D_1139,D_1139),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1139,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1138)),D_1140))
      | ~ r3_waybel_9('#skF_6',B_1138,D_1139)
      | ~ m1_subset_1(D_1139,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1138)))
      | ~ r3_waybel_9('#skF_6',B_1138,D_1140)
      | ~ v10_waybel_0(B_1138,'#skF_6')
      | ~ m1_subset_1(D_1140,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1138)
      | ~ v4_orders_2(B_1138)
      | v2_struct_0(B_1138)
      | ~ l1_waybel_0(B_1138,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_6583])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_orders_2(A_8,B_9,C_10)
      | ~ r3_orders_2(A_8,B_9,C_10)
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6646,plain,(
    ! [D_1139,B_1138,D_1140] :
      ( r1_orders_2('#skF_6',D_1139,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1138)),D_1140))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1138)),D_1140),u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | m1_subset_1('#skF_5'('#skF_6',B_1138,D_1139,D_1139),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_1138,D_1139)
      | ~ m1_subset_1(D_1139,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1138)))
      | ~ r3_waybel_9('#skF_6',B_1138,D_1140)
      | ~ v10_waybel_0(B_1138,'#skF_6')
      | ~ m1_subset_1(D_1140,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1138)
      | ~ v4_orders_2(B_1138)
      | v2_struct_0(B_1138)
      | ~ l1_waybel_0(B_1138,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6618,c_10])).

tff(c_6664,plain,(
    ! [D_1139,B_1138,D_1140] :
      ( r1_orders_2('#skF_6',D_1139,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1138)),D_1140))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1138)),D_1140),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | m1_subset_1('#skF_5'('#skF_6',B_1138,D_1139,D_1139),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_1138,D_1139)
      | ~ m1_subset_1(D_1139,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1138)))
      | ~ r3_waybel_9('#skF_6',B_1138,D_1140)
      | ~ v10_waybel_0(B_1138,'#skF_6')
      | ~ m1_subset_1(D_1140,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1138)
      | ~ v4_orders_2(B_1138)
      | v2_struct_0(B_1138)
      | ~ l1_waybel_0(B_1138,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_97,c_6646])).

tff(c_6681,plain,(
    ! [D_1152,B_1153,D_1154] :
      ( r1_orders_2('#skF_6',D_1152,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1153)),D_1154))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1153)),D_1154),u1_struct_0('#skF_6'))
      | m1_subset_1('#skF_5'('#skF_6',B_1153,D_1152,D_1152),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_1153,D_1152)
      | ~ m1_subset_1(D_1152,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1153)))
      | ~ r3_waybel_9('#skF_6',B_1153,D_1154)
      | ~ v10_waybel_0(B_1153,'#skF_6')
      | ~ m1_subset_1(D_1154,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1153)
      | ~ v4_orders_2(B_1153)
      | v2_struct_0(B_1153)
      | ~ l1_waybel_0(B_1153,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_6664])).

tff(c_6684,plain,(
    ! [D_1152,B_1153,C_45] :
      ( r1_orders_2('#skF_6',D_1152,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1153)),C_45))
      | m1_subset_1('#skF_5'('#skF_6',B_1153,D_1152,D_1152),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_1153,D_1152)
      | ~ m1_subset_1(D_1152,u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_1153,C_45)
      | ~ v10_waybel_0(B_1153,'#skF_6')
      | ~ v7_waybel_0(B_1153)
      | ~ v4_orders_2(B_1153)
      | v2_struct_0(B_1153)
      | ~ l1_waybel_0(B_1153,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1153)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1153)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_6681])).

tff(c_6688,plain,(
    ! [D_1155,B_1156,C_1157] :
      ( r1_orders_2('#skF_6',D_1155,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1156)),C_1157))
      | m1_subset_1('#skF_5'('#skF_6',B_1156,D_1155,D_1155),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_1156,D_1155)
      | ~ m1_subset_1(D_1155,u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_1156,C_1157)
      | ~ v10_waybel_0(B_1156,'#skF_6')
      | ~ v7_waybel_0(B_1156)
      | ~ v4_orders_2(B_1156)
      | v2_struct_0(B_1156)
      | ~ l1_waybel_0(B_1156,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1156)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1156)),C_1157)
      | ~ m1_subset_1(C_1157,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_6684])).

tff(c_30,plain,(
    ! [A_24,C_45,B_38] :
      ( ~ r1_orders_2(A_24,C_45,'#skF_2'(A_24,B_38,C_45))
      | r1_yellow_0(A_24,B_38)
      | ~ r2_lattice3(A_24,B_38,C_45)
      | ~ m1_subset_1(C_45,u1_struct_0(A_24))
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6692,plain,(
    ! [B_1156,C_1157] :
      ( ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | m1_subset_1('#skF_5'('#skF_6',B_1156,C_1157,C_1157),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_1156,C_1157)
      | ~ v10_waybel_0(B_1156,'#skF_6')
      | ~ v7_waybel_0(B_1156)
      | ~ v4_orders_2(B_1156)
      | v2_struct_0(B_1156)
      | ~ l1_waybel_0(B_1156,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1156)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1156)),C_1157)
      | ~ m1_subset_1(C_1157,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_6688,c_30])).

tff(c_6737,plain,(
    ! [B_1158,C_1159] :
      ( m1_subset_1('#skF_5'('#skF_6',B_1158,C_1159,C_1159),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_1158,C_1159)
      | ~ v10_waybel_0(B_1158,'#skF_6')
      | ~ v7_waybel_0(B_1158)
      | ~ v4_orders_2(B_1158)
      | v2_struct_0(B_1158)
      | ~ l1_waybel_0(B_1158,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1158)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1158)),C_1159)
      | ~ m1_subset_1(C_1159,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_6692])).

tff(c_6817,plain,(
    ! [B_1160,D_1161] :
      ( m1_subset_1('#skF_5'('#skF_6',B_1160,D_1161,D_1161),u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1160)))
      | ~ r3_waybel_9('#skF_6',B_1160,D_1161)
      | ~ v10_waybel_0(B_1160,'#skF_6')
      | ~ m1_subset_1(D_1161,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1160)
      | ~ v4_orders_2(B_1160)
      | v2_struct_0(B_1160)
      | ~ l1_waybel_0(B_1160,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_805,c_6737])).

tff(c_916,plain,(
    ! [A_379,B_380,D_381,E_382] :
      ( ~ v5_pre_topc(k4_waybel_1(A_379,'#skF_5'(A_379,B_380,D_381,D_381)),A_379,A_379)
      | r3_orders_2(A_379,D_381,E_382)
      | ~ r2_lattice3(A_379,k2_relset_1(u1_struct_0(B_380),u1_struct_0(A_379),u1_waybel_0(A_379,B_380)),E_382)
      | ~ m1_subset_1(E_382,u1_struct_0(A_379))
      | ~ r3_waybel_9(A_379,B_380,D_381)
      | ~ m1_subset_1(D_381,u1_struct_0(A_379))
      | ~ l1_waybel_0(B_380,A_379)
      | ~ v7_waybel_0(B_380)
      | ~ v4_orders_2(B_380)
      | v2_struct_0(B_380)
      | ~ l1_waybel_9(A_379)
      | ~ v1_compts_1(A_379)
      | ~ v2_lattice3(A_379)
      | ~ v1_lattice3(A_379)
      | ~ v5_orders_2(A_379)
      | ~ v4_orders_2(A_379)
      | ~ v3_orders_2(A_379)
      | ~ v8_pre_topc(A_379)
      | ~ v2_pre_topc(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_919,plain,(
    ! [D_381,E_382,B_380] :
      ( r3_orders_2('#skF_6',D_381,E_382)
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_380),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_380)),E_382)
      | ~ m1_subset_1(E_382,u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_380,D_381)
      | ~ m1_subset_1(D_381,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_380,'#skF_6')
      | ~ v7_waybel_0(B_380)
      | ~ v4_orders_2(B_380)
      | v2_struct_0(B_380)
      | ~ l1_waybel_9('#skF_6')
      | ~ v1_compts_1('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ v8_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | ~ m1_subset_1('#skF_5'('#skF_6',B_380,D_381,D_381),u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_64,c_916])).

tff(c_951,plain,(
    ! [D_389,E_390,B_391] :
      ( r3_orders_2('#skF_6',D_389,E_390)
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391)),E_390)
      | ~ m1_subset_1(E_390,u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_391,D_389)
      | ~ m1_subset_1(D_389,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_391,'#skF_6')
      | ~ v7_waybel_0(B_391)
      | ~ v4_orders_2(B_391)
      | v2_struct_0(B_391)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_391,D_389,D_389),u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_919])).

tff(c_965,plain,(
    ! [D_389,E_390,B_168] :
      ( r3_orders_2('#skF_6',D_389,E_390)
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)),E_390)
      | ~ m1_subset_1(E_390,u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_168,D_389)
      | ~ m1_subset_1(D_389,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ v7_waybel_0(B_168)
      | ~ v4_orders_2(B_168)
      | v2_struct_0(B_168)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_168,D_389,D_389),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_951])).

tff(c_1107,plain,(
    ! [D_409,E_410,B_411] :
      ( r3_orders_2('#skF_6',D_409,E_410)
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_411)),E_410)
      | ~ m1_subset_1(E_410,u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_411,D_409)
      | ~ m1_subset_1(D_409,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_411)
      | ~ v4_orders_2(B_411)
      | v2_struct_0(B_411)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_411,D_409,D_409),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_411,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_965])).

tff(c_1121,plain,(
    ! [D_409,B_411,C_45] :
      ( r3_orders_2('#skF_6',D_409,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_411)),C_45))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_411)),C_45),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_411,D_409)
      | ~ m1_subset_1(D_409,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_411)
      | ~ v4_orders_2(B_411)
      | v2_struct_0(B_411)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_411,D_409,D_409),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_411,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_411)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_411)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_1107])).

tff(c_1539,plain,(
    ! [D_502,B_503,C_504] :
      ( r3_orders_2('#skF_6',D_502,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)),C_504))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)),C_504),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_503,D_502)
      | ~ m1_subset_1(D_502,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_503)
      | ~ v4_orders_2(B_503)
      | v2_struct_0(B_503)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_503,D_502,D_502),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_503,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)),C_504)
      | ~ m1_subset_1(C_504,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_1121])).

tff(c_1542,plain,(
    ! [D_502,B_503,C_45] :
      ( r3_orders_2('#skF_6',D_502,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)),C_45))
      | ~ r3_waybel_9('#skF_6',B_503,D_502)
      | ~ m1_subset_1(D_502,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_503)
      | ~ v4_orders_2(B_503)
      | v2_struct_0(B_503)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_503,D_502,D_502),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_503,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_1539])).

tff(c_1545,plain,(
    ! [D_502,B_503,C_45] :
      ( r3_orders_2('#skF_6',D_502,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)),C_45))
      | ~ r3_waybel_9('#skF_6',B_503,D_502)
      | ~ m1_subset_1(D_502,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_503)
      | ~ v4_orders_2(B_503)
      | v2_struct_0(B_503)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_503,D_502,D_502),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_503,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_503)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_1542])).

tff(c_7054,plain,(
    ! [D_1179,B_1180,C_1181] :
      ( r3_orders_2('#skF_6',D_1179,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)),C_1181))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)),C_1181)
      | ~ m1_subset_1(C_1181,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)))
      | ~ r3_waybel_9('#skF_6',B_1180,D_1179)
      | ~ v10_waybel_0(B_1180,'#skF_6')
      | ~ m1_subset_1(D_1179,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1180)
      | ~ v4_orders_2(B_1180)
      | v2_struct_0(B_1180)
      | ~ l1_waybel_0(B_1180,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6817,c_1545])).

tff(c_7056,plain,(
    ! [D_1179,B_1180,C_1181] :
      ( r1_orders_2('#skF_6',D_1179,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)),C_1181))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)),C_1181),u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)),C_1181)
      | ~ m1_subset_1(C_1181,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)))
      | ~ r3_waybel_9('#skF_6',B_1180,D_1179)
      | ~ v10_waybel_0(B_1180,'#skF_6')
      | ~ m1_subset_1(D_1179,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1180)
      | ~ v4_orders_2(B_1180)
      | v2_struct_0(B_1180)
      | ~ l1_waybel_0(B_1180,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_7054,c_10])).

tff(c_7059,plain,(
    ! [D_1179,B_1180,C_1181] :
      ( r1_orders_2('#skF_6',D_1179,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)),C_1181))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)),C_1181),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)),C_1181)
      | ~ m1_subset_1(C_1181,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1180)))
      | ~ r3_waybel_9('#skF_6',B_1180,D_1179)
      | ~ v10_waybel_0(B_1180,'#skF_6')
      | ~ m1_subset_1(D_1179,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1180)
      | ~ v4_orders_2(B_1180)
      | v2_struct_0(B_1180)
      | ~ l1_waybel_0(B_1180,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_97,c_7056])).

tff(c_7404,plain,(
    ! [D_1208,B_1209,C_1210] :
      ( r1_orders_2('#skF_6',D_1208,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1209)),C_1210))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1209)),C_1210),u1_struct_0('#skF_6'))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1209)),C_1210)
      | ~ m1_subset_1(C_1210,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1209)))
      | ~ r3_waybel_9('#skF_6',B_1209,D_1208)
      | ~ v10_waybel_0(B_1209,'#skF_6')
      | ~ m1_subset_1(D_1208,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1209)
      | ~ v4_orders_2(B_1209)
      | v2_struct_0(B_1209)
      | ~ l1_waybel_0(B_1209,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_7059])).

tff(c_7407,plain,(
    ! [D_1208,B_1209,C_45] :
      ( r1_orders_2('#skF_6',D_1208,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1209)),C_45))
      | ~ r3_waybel_9('#skF_6',B_1209,D_1208)
      | ~ v10_waybel_0(B_1209,'#skF_6')
      | ~ m1_subset_1(D_1208,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1209)
      | ~ v4_orders_2(B_1209)
      | v2_struct_0(B_1209)
      | ~ l1_waybel_0(B_1209,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1209)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1209)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_7404])).

tff(c_7411,plain,(
    ! [D_1211,B_1212,C_1213] :
      ( r1_orders_2('#skF_6',D_1211,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1212)),C_1213))
      | ~ r3_waybel_9('#skF_6',B_1212,D_1211)
      | ~ v10_waybel_0(B_1212,'#skF_6')
      | ~ m1_subset_1(D_1211,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1212)
      | ~ v4_orders_2(B_1212)
      | v2_struct_0(B_1212)
      | ~ l1_waybel_0(B_1212,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1212)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1212)),C_1213)
      | ~ m1_subset_1(C_1213,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_7407])).

tff(c_7415,plain,(
    ! [B_1212,C_1213] :
      ( ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ r3_waybel_9('#skF_6',B_1212,C_1213)
      | ~ v10_waybel_0(B_1212,'#skF_6')
      | ~ v7_waybel_0(B_1212)
      | ~ v4_orders_2(B_1212)
      | v2_struct_0(B_1212)
      | ~ l1_waybel_0(B_1212,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1212)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1212)),C_1213)
      | ~ m1_subset_1(C_1213,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_7411,c_30])).

tff(c_7419,plain,(
    ! [B_1214,C_1215] :
      ( ~ r3_waybel_9('#skF_6',B_1214,C_1215)
      | ~ v10_waybel_0(B_1214,'#skF_6')
      | ~ v7_waybel_0(B_1214)
      | ~ v4_orders_2(B_1214)
      | v2_struct_0(B_1214)
      | ~ l1_waybel_0(B_1214,'#skF_6')
      | r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1214)))
      | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1214)),C_1215)
      | ~ m1_subset_1(C_1215,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_7415])).

tff(c_7516,plain,(
    ! [B_1216,D_1217] :
      ( r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1216)))
      | ~ r3_waybel_9('#skF_6',B_1216,D_1217)
      | ~ v10_waybel_0(B_1216,'#skF_6')
      | ~ m1_subset_1(D_1217,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1216)
      | ~ v4_orders_2(B_1216)
      | v2_struct_0(B_1216)
      | ~ l1_waybel_0(B_1216,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_805,c_7419])).

tff(c_7518,plain,
    ( r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | ~ v10_waybel_0('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v7_waybel_0('#skF_8')
    | ~ v4_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l1_waybel_0('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_7516])).

tff(c_7521,plain,
    ( r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_74,c_62,c_7518])).

tff(c_7522,plain,(
    r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_7521])).

tff(c_42,plain,(
    ! [A_51,B_53] :
      ( k4_yellow_2(A_51,u1_waybel_0(A_51,B_53)) = k1_waybel_2(A_51,B_53)
      | ~ l1_waybel_0(B_53,A_51)
      | ~ l1_orders_2(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_167,B_168] :
      ( v1_relat_1(u1_waybel_0(A_167,B_168))
      | ~ l1_waybel_0(B_168,A_167)
      | ~ l1_struct_0(A_167) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_28,plain,(
    ! [A_24,B_38] :
      ( m1_subset_1('#skF_3'(A_24,B_38),u1_struct_0(A_24))
      | ~ r1_yellow_0(A_24,B_38)
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    ! [A_24,B_38] :
      ( r2_lattice3(A_24,B_38,'#skF_3'(A_24,B_38))
      | ~ r1_yellow_0(A_24,B_38)
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_18,plain,(
    ! [A_12,B_19,C_20] :
      ( m1_subset_1('#skF_1'(A_12,B_19,C_20),u1_struct_0(A_12))
      | k1_yellow_0(A_12,B_19) = C_20
      | ~ r2_lattice3(A_12,B_19,C_20)
      | ~ r1_yellow_0(A_12,B_19)
      | ~ m1_subset_1(C_20,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_12,B_19,C_20] :
      ( r2_lattice3(A_12,B_19,'#skF_1'(A_12,B_19,C_20))
      | k1_yellow_0(A_12,B_19) = C_20
      | ~ r2_lattice3(A_12,B_19,C_20)
      | ~ r1_yellow_0(A_12,B_19)
      | ~ m1_subset_1(C_20,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_24,B_38,D_48] :
      ( r1_orders_2(A_24,'#skF_3'(A_24,B_38),D_48)
      | ~ r2_lattice3(A_24,B_38,D_48)
      | ~ m1_subset_1(D_48,u1_struct_0(A_24))
      | ~ r1_yellow_0(A_24,B_38)
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_659,plain,(
    ! [A_305,C_306,B_307] :
      ( ~ r1_orders_2(A_305,C_306,'#skF_1'(A_305,B_307,C_306))
      | k1_yellow_0(A_305,B_307) = C_306
      | ~ r2_lattice3(A_305,B_307,C_306)
      | ~ r1_yellow_0(A_305,B_307)
      | ~ m1_subset_1(C_306,u1_struct_0(A_305))
      | ~ l1_orders_2(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_898,plain,(
    ! [A_376,B_377,B_378] :
      ( k1_yellow_0(A_376,B_377) = '#skF_3'(A_376,B_378)
      | ~ r2_lattice3(A_376,B_377,'#skF_3'(A_376,B_378))
      | ~ r1_yellow_0(A_376,B_377)
      | ~ m1_subset_1('#skF_3'(A_376,B_378),u1_struct_0(A_376))
      | ~ r2_lattice3(A_376,B_378,'#skF_1'(A_376,B_377,'#skF_3'(A_376,B_378)))
      | ~ m1_subset_1('#skF_1'(A_376,B_377,'#skF_3'(A_376,B_378)),u1_struct_0(A_376))
      | ~ r1_yellow_0(A_376,B_378)
      | ~ l1_orders_2(A_376)
      | ~ v5_orders_2(A_376) ) ),
    inference(resolution,[status(thm)],[c_24,c_659])).

tff(c_923,plain,(
    ! [A_383,B_384] :
      ( ~ m1_subset_1('#skF_1'(A_383,B_384,'#skF_3'(A_383,B_384)),u1_struct_0(A_383))
      | ~ v5_orders_2(A_383)
      | k1_yellow_0(A_383,B_384) = '#skF_3'(A_383,B_384)
      | ~ r2_lattice3(A_383,B_384,'#skF_3'(A_383,B_384))
      | ~ r1_yellow_0(A_383,B_384)
      | ~ m1_subset_1('#skF_3'(A_383,B_384),u1_struct_0(A_383))
      | ~ l1_orders_2(A_383) ) ),
    inference(resolution,[status(thm)],[c_16,c_898])).

tff(c_929,plain,(
    ! [A_385,B_386] :
      ( ~ v5_orders_2(A_385)
      | k1_yellow_0(A_385,B_386) = '#skF_3'(A_385,B_386)
      | ~ r2_lattice3(A_385,B_386,'#skF_3'(A_385,B_386))
      | ~ r1_yellow_0(A_385,B_386)
      | ~ m1_subset_1('#skF_3'(A_385,B_386),u1_struct_0(A_385))
      | ~ l1_orders_2(A_385) ) ),
    inference(resolution,[status(thm)],[c_18,c_923])).

tff(c_946,plain,(
    ! [A_387,B_388] :
      ( k1_yellow_0(A_387,B_388) = '#skF_3'(A_387,B_388)
      | ~ m1_subset_1('#skF_3'(A_387,B_388),u1_struct_0(A_387))
      | ~ r1_yellow_0(A_387,B_388)
      | ~ l1_orders_2(A_387)
      | ~ v5_orders_2(A_387) ) ),
    inference(resolution,[status(thm)],[c_26,c_929])).

tff(c_950,plain,(
    ! [A_24,B_38] :
      ( k1_yellow_0(A_24,B_38) = '#skF_3'(A_24,B_38)
      | ~ r1_yellow_0(A_24,B_38)
      | ~ l1_orders_2(A_24)
      | ~ v5_orders_2(A_24) ) ),
    inference(resolution,[status(thm)],[c_28,c_946])).

tff(c_7560,plain,
    ( k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = '#skF_3'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_7522,c_950])).

tff(c_7631,plain,(
    k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = '#skF_3'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_7560])).

tff(c_44,plain,(
    ! [A_54,B_56] :
      ( k1_yellow_0(A_54,k2_relat_1(B_56)) = k4_yellow_2(A_54,B_56)
      | ~ v1_relat_1(B_56)
      | ~ l1_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_7725,plain,
    ( '#skF_3'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = k4_yellow_2('#skF_6',u1_waybel_0('#skF_6','#skF_8'))
    | ~ v1_relat_1(u1_waybel_0('#skF_6','#skF_8'))
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7631,c_44])).

tff(c_7834,plain,
    ( '#skF_3'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = k4_yellow_2('#skF_6',u1_waybel_0('#skF_6','#skF_8'))
    | ~ v1_relat_1(u1_waybel_0('#skF_6','#skF_8'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_7725])).

tff(c_7835,plain,
    ( '#skF_3'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = k4_yellow_2('#skF_6',u1_waybel_0('#skF_6','#skF_8'))
    | ~ v1_relat_1(u1_waybel_0('#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_7834])).

tff(c_7848,plain,(
    ~ v1_relat_1(u1_waybel_0('#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_7835])).

tff(c_7851,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_129,c_7848])).

tff(c_7855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_66,c_7851])).

tff(c_7856,plain,(
    '#skF_3'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = k4_yellow_2('#skF_6',u1_waybel_0('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_7835])).

tff(c_7990,plain,
    ( m1_subset_1(k4_yellow_2('#skF_6',u1_waybel_0('#skF_6','#skF_8')),u1_struct_0('#skF_6'))
    | ~ r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7856,c_28])).

tff(c_8137,plain,(
    m1_subset_1(k4_yellow_2('#skF_6',u1_waybel_0('#skF_6','#skF_8')),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_7522,c_7990])).

tff(c_8182,plain,
    ( m1_subset_1(k1_waybel_2('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ l1_waybel_0('#skF_8','#skF_6')
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_8137])).

tff(c_8238,plain,
    ( m1_subset_1(k1_waybel_2('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_66,c_8182])).

tff(c_8239,plain,(
    m1_subset_1(k1_waybel_2('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_8238])).

tff(c_7858,plain,(
    k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = k4_yellow_2('#skF_6',u1_waybel_0('#skF_6','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7856,c_7631])).

tff(c_7857,plain,(
    v1_relat_1(u1_waybel_0('#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_7835])).

tff(c_140,plain,(
    ! [A_173,B_174] :
      ( r2_lattice3(A_173,B_174,k1_yellow_0(A_173,B_174))
      | ~ r1_yellow_0(A_173,B_174)
      | ~ m1_subset_1(k1_yellow_0(A_173,B_174),u1_struct_0(A_173))
      | ~ l1_orders_2(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_675,plain,(
    ! [A_313,B_314] :
      ( r2_lattice3(A_313,k2_relat_1(B_314),k1_yellow_0(A_313,k2_relat_1(B_314)))
      | ~ r1_yellow_0(A_313,k2_relat_1(B_314))
      | ~ m1_subset_1(k4_yellow_2(A_313,B_314),u1_struct_0(A_313))
      | ~ l1_orders_2(A_313)
      | ~ v1_relat_1(B_314)
      | ~ l1_orders_2(A_313)
      | v2_struct_0(A_313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_140])).

tff(c_704,plain,(
    ! [A_323,B_324] :
      ( r2_lattice3(A_323,k2_relat_1(B_324),k4_yellow_2(A_323,B_324))
      | ~ r1_yellow_0(A_323,k2_relat_1(B_324))
      | ~ m1_subset_1(k4_yellow_2(A_323,B_324),u1_struct_0(A_323))
      | ~ l1_orders_2(A_323)
      | ~ v1_relat_1(B_324)
      | ~ l1_orders_2(A_323)
      | v2_struct_0(A_323)
      | ~ v1_relat_1(B_324)
      | ~ l1_orders_2(A_323)
      | v2_struct_0(A_323) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_675])).

tff(c_707,plain,(
    ! [A_51,B_53] :
      ( r2_lattice3(A_51,k2_relat_1(u1_waybel_0(A_51,B_53)),k1_waybel_2(A_51,B_53))
      | ~ r1_yellow_0(A_51,k2_relat_1(u1_waybel_0(A_51,B_53)))
      | ~ m1_subset_1(k4_yellow_2(A_51,u1_waybel_0(A_51,B_53)),u1_struct_0(A_51))
      | ~ l1_orders_2(A_51)
      | ~ v1_relat_1(u1_waybel_0(A_51,B_53))
      | ~ l1_orders_2(A_51)
      | v2_struct_0(A_51)
      | ~ v1_relat_1(u1_waybel_0(A_51,B_53))
      | ~ l1_orders_2(A_51)
      | v2_struct_0(A_51)
      | ~ l1_waybel_0(B_53,A_51)
      | ~ l1_orders_2(A_51)
      | v2_struct_0(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_704])).

tff(c_665,plain,(
    ! [A_308,B_309,D_310] :
      ( r1_orders_2(A_308,k1_yellow_0(A_308,B_309),D_310)
      | ~ r2_lattice3(A_308,B_309,D_310)
      | ~ m1_subset_1(D_310,u1_struct_0(A_308))
      | ~ r1_yellow_0(A_308,B_309)
      | ~ m1_subset_1(k1_yellow_0(A_308,B_309),u1_struct_0(A_308))
      | ~ l1_orders_2(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_719,plain,(
    ! [A_327,B_328,D_329] :
      ( r1_orders_2(A_327,k1_yellow_0(A_327,k2_relat_1(B_328)),D_329)
      | ~ r2_lattice3(A_327,k2_relat_1(B_328),D_329)
      | ~ m1_subset_1(D_329,u1_struct_0(A_327))
      | ~ r1_yellow_0(A_327,k2_relat_1(B_328))
      | ~ m1_subset_1(k4_yellow_2(A_327,B_328),u1_struct_0(A_327))
      | ~ l1_orders_2(A_327)
      | ~ v1_relat_1(B_328)
      | ~ l1_orders_2(A_327)
      | v2_struct_0(A_327) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_665])).

tff(c_741,plain,(
    ! [A_338,B_339,D_340] :
      ( r1_orders_2(A_338,k4_yellow_2(A_338,B_339),D_340)
      | ~ r2_lattice3(A_338,k2_relat_1(B_339),D_340)
      | ~ m1_subset_1(D_340,u1_struct_0(A_338))
      | ~ r1_yellow_0(A_338,k2_relat_1(B_339))
      | ~ m1_subset_1(k4_yellow_2(A_338,B_339),u1_struct_0(A_338))
      | ~ l1_orders_2(A_338)
      | ~ v1_relat_1(B_339)
      | ~ l1_orders_2(A_338)
      | v2_struct_0(A_338)
      | ~ v1_relat_1(B_339)
      | ~ l1_orders_2(A_338)
      | v2_struct_0(A_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_719])).

tff(c_1192,plain,(
    ! [A_422,B_423,C_424] :
      ( r1_orders_2(A_422,k4_yellow_2(A_422,B_423),'#skF_1'(A_422,k2_relat_1(B_423),C_424))
      | ~ m1_subset_1('#skF_1'(A_422,k2_relat_1(B_423),C_424),u1_struct_0(A_422))
      | ~ m1_subset_1(k4_yellow_2(A_422,B_423),u1_struct_0(A_422))
      | ~ v1_relat_1(B_423)
      | v2_struct_0(A_422)
      | k1_yellow_0(A_422,k2_relat_1(B_423)) = C_424
      | ~ r2_lattice3(A_422,k2_relat_1(B_423),C_424)
      | ~ r1_yellow_0(A_422,k2_relat_1(B_423))
      | ~ m1_subset_1(C_424,u1_struct_0(A_422))
      | ~ l1_orders_2(A_422) ) ),
    inference(resolution,[status(thm)],[c_16,c_741])).

tff(c_3547,plain,(
    ! [A_790,B_791,C_792] :
      ( r1_orders_2(A_790,k1_waybel_2(A_790,B_791),'#skF_1'(A_790,k2_relat_1(u1_waybel_0(A_790,B_791)),C_792))
      | ~ m1_subset_1('#skF_1'(A_790,k2_relat_1(u1_waybel_0(A_790,B_791)),C_792),u1_struct_0(A_790))
      | ~ m1_subset_1(k4_yellow_2(A_790,u1_waybel_0(A_790,B_791)),u1_struct_0(A_790))
      | ~ v1_relat_1(u1_waybel_0(A_790,B_791))
      | v2_struct_0(A_790)
      | k1_yellow_0(A_790,k2_relat_1(u1_waybel_0(A_790,B_791))) = C_792
      | ~ r2_lattice3(A_790,k2_relat_1(u1_waybel_0(A_790,B_791)),C_792)
      | ~ r1_yellow_0(A_790,k2_relat_1(u1_waybel_0(A_790,B_791)))
      | ~ m1_subset_1(C_792,u1_struct_0(A_790))
      | ~ l1_orders_2(A_790)
      | ~ l1_waybel_0(B_791,A_790)
      | ~ l1_orders_2(A_790)
      | v2_struct_0(A_790) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_1192])).

tff(c_14,plain,(
    ! [A_12,C_20,B_19] :
      ( ~ r1_orders_2(A_12,C_20,'#skF_1'(A_12,B_19,C_20))
      | k1_yellow_0(A_12,B_19) = C_20
      | ~ r2_lattice3(A_12,B_19,C_20)
      | ~ r1_yellow_0(A_12,B_19)
      | ~ m1_subset_1(C_20,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3553,plain,(
    ! [A_793,B_794] :
      ( ~ m1_subset_1('#skF_1'(A_793,k2_relat_1(u1_waybel_0(A_793,B_794)),k1_waybel_2(A_793,B_794)),u1_struct_0(A_793))
      | ~ m1_subset_1(k4_yellow_2(A_793,u1_waybel_0(A_793,B_794)),u1_struct_0(A_793))
      | ~ v1_relat_1(u1_waybel_0(A_793,B_794))
      | k1_yellow_0(A_793,k2_relat_1(u1_waybel_0(A_793,B_794))) = k1_waybel_2(A_793,B_794)
      | ~ r2_lattice3(A_793,k2_relat_1(u1_waybel_0(A_793,B_794)),k1_waybel_2(A_793,B_794))
      | ~ r1_yellow_0(A_793,k2_relat_1(u1_waybel_0(A_793,B_794)))
      | ~ m1_subset_1(k1_waybel_2(A_793,B_794),u1_struct_0(A_793))
      | ~ l1_waybel_0(B_794,A_793)
      | ~ l1_orders_2(A_793)
      | v2_struct_0(A_793) ) ),
    inference(resolution,[status(thm)],[c_3547,c_14])).

tff(c_3578,plain,(
    ! [A_798,B_799] :
      ( ~ m1_subset_1(k4_yellow_2(A_798,u1_waybel_0(A_798,B_799)),u1_struct_0(A_798))
      | ~ v1_relat_1(u1_waybel_0(A_798,B_799))
      | ~ l1_waybel_0(B_799,A_798)
      | v2_struct_0(A_798)
      | k1_yellow_0(A_798,k2_relat_1(u1_waybel_0(A_798,B_799))) = k1_waybel_2(A_798,B_799)
      | ~ r2_lattice3(A_798,k2_relat_1(u1_waybel_0(A_798,B_799)),k1_waybel_2(A_798,B_799))
      | ~ r1_yellow_0(A_798,k2_relat_1(u1_waybel_0(A_798,B_799)))
      | ~ m1_subset_1(k1_waybel_2(A_798,B_799),u1_struct_0(A_798))
      | ~ l1_orders_2(A_798) ) ),
    inference(resolution,[status(thm)],[c_18,c_3553])).

tff(c_3592,plain,(
    ! [A_51,B_53] :
      ( k1_yellow_0(A_51,k2_relat_1(u1_waybel_0(A_51,B_53))) = k1_waybel_2(A_51,B_53)
      | ~ m1_subset_1(k1_waybel_2(A_51,B_53),u1_struct_0(A_51))
      | ~ r1_yellow_0(A_51,k2_relat_1(u1_waybel_0(A_51,B_53)))
      | ~ m1_subset_1(k4_yellow_2(A_51,u1_waybel_0(A_51,B_53)),u1_struct_0(A_51))
      | ~ v1_relat_1(u1_waybel_0(A_51,B_53))
      | ~ l1_waybel_0(B_53,A_51)
      | ~ l1_orders_2(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_707,c_3578])).

tff(c_8163,plain,
    ( k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = k1_waybel_2('#skF_6','#skF_8')
    | ~ m1_subset_1(k1_waybel_2('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | ~ r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | ~ v1_relat_1(u1_waybel_0('#skF_6','#skF_8'))
    | ~ l1_waybel_0('#skF_8','#skF_6')
    | ~ l1_orders_2('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_8137,c_3592])).

tff(c_8213,plain,
    ( k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = k1_waybel_2('#skF_6','#skF_8')
    | ~ m1_subset_1(k1_waybel_2('#skF_6','#skF_8'),u1_struct_0('#skF_6'))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_66,c_7857,c_7522,c_8163])).

tff(c_8214,plain,
    ( k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = k1_waybel_2('#skF_6','#skF_8')
    | ~ m1_subset_1(k1_waybel_2('#skF_6','#skF_8'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_8213])).

tff(c_9693,plain,(
    k4_yellow_2('#skF_6',u1_waybel_0('#skF_6','#skF_8')) = k1_waybel_2('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8239,c_7858,c_8214])).

tff(c_9700,plain,(
    k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = k1_waybel_2('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9693,c_7858])).

tff(c_1501,plain,(
    ! [A_488,B_489,D_490,C_491] :
      ( m1_subset_1('#skF_5'(A_488,B_489,D_490,D_490),u1_struct_0(A_488))
      | r3_orders_2(A_488,D_490,'#skF_1'(A_488,k2_relset_1(u1_struct_0(B_489),u1_struct_0(A_488),u1_waybel_0(A_488,B_489)),C_491))
      | ~ m1_subset_1('#skF_1'(A_488,k2_relset_1(u1_struct_0(B_489),u1_struct_0(A_488),u1_waybel_0(A_488,B_489)),C_491),u1_struct_0(A_488))
      | ~ r3_waybel_9(A_488,B_489,D_490)
      | ~ m1_subset_1(D_490,u1_struct_0(A_488))
      | ~ l1_waybel_0(B_489,A_488)
      | ~ v7_waybel_0(B_489)
      | ~ v4_orders_2(B_489)
      | v2_struct_0(B_489)
      | ~ l1_waybel_9(A_488)
      | ~ v1_compts_1(A_488)
      | ~ v2_lattice3(A_488)
      | ~ v1_lattice3(A_488)
      | ~ v5_orders_2(A_488)
      | ~ v4_orders_2(A_488)
      | ~ v3_orders_2(A_488)
      | ~ v8_pre_topc(A_488)
      | ~ v2_pre_topc(A_488)
      | k1_yellow_0(A_488,k2_relset_1(u1_struct_0(B_489),u1_struct_0(A_488),u1_waybel_0(A_488,B_489))) = C_491
      | ~ r2_lattice3(A_488,k2_relset_1(u1_struct_0(B_489),u1_struct_0(A_488),u1_waybel_0(A_488,B_489)),C_491)
      | ~ r1_yellow_0(A_488,k2_relset_1(u1_struct_0(B_489),u1_struct_0(A_488),u1_waybel_0(A_488,B_489)))
      | ~ m1_subset_1(C_491,u1_struct_0(A_488))
      | ~ l1_orders_2(A_488) ) ),
    inference(resolution,[status(thm)],[c_16,c_818])).

tff(c_2919,plain,(
    ! [A_698,B_699,D_700,C_701] :
      ( m1_subset_1('#skF_5'(A_698,B_699,D_700,D_700),u1_struct_0(A_698))
      | r3_orders_2(A_698,D_700,'#skF_1'(A_698,k2_relset_1(u1_struct_0(B_699),u1_struct_0(A_698),u1_waybel_0(A_698,B_699)),C_701))
      | ~ r3_waybel_9(A_698,B_699,D_700)
      | ~ m1_subset_1(D_700,u1_struct_0(A_698))
      | ~ l1_waybel_0(B_699,A_698)
      | ~ v7_waybel_0(B_699)
      | ~ v4_orders_2(B_699)
      | v2_struct_0(B_699)
      | ~ l1_waybel_9(A_698)
      | ~ v1_compts_1(A_698)
      | ~ v2_lattice3(A_698)
      | ~ v1_lattice3(A_698)
      | ~ v5_orders_2(A_698)
      | ~ v4_orders_2(A_698)
      | ~ v3_orders_2(A_698)
      | ~ v8_pre_topc(A_698)
      | ~ v2_pre_topc(A_698)
      | k1_yellow_0(A_698,k2_relset_1(u1_struct_0(B_699),u1_struct_0(A_698),u1_waybel_0(A_698,B_699))) = C_701
      | ~ r2_lattice3(A_698,k2_relset_1(u1_struct_0(B_699),u1_struct_0(A_698),u1_waybel_0(A_698,B_699)),C_701)
      | ~ r1_yellow_0(A_698,k2_relset_1(u1_struct_0(B_699),u1_struct_0(A_698),u1_waybel_0(A_698,B_699)))
      | ~ m1_subset_1(C_701,u1_struct_0(A_698))
      | ~ l1_orders_2(A_698) ) ),
    inference(resolution,[status(thm)],[c_18,c_1501])).

tff(c_8625,plain,(
    ! [A_1221,B_1222,D_1223,C_1224] :
      ( m1_subset_1('#skF_5'(A_1221,B_1222,D_1223,D_1223),u1_struct_0(A_1221))
      | r3_orders_2(A_1221,D_1223,'#skF_1'(A_1221,k2_relat_1(u1_waybel_0(A_1221,B_1222)),C_1224))
      | ~ r3_waybel_9(A_1221,B_1222,D_1223)
      | ~ m1_subset_1(D_1223,u1_struct_0(A_1221))
      | ~ l1_waybel_0(B_1222,A_1221)
      | ~ v7_waybel_0(B_1222)
      | ~ v4_orders_2(B_1222)
      | v2_struct_0(B_1222)
      | ~ l1_waybel_9(A_1221)
      | ~ v1_compts_1(A_1221)
      | ~ v2_lattice3(A_1221)
      | ~ v1_lattice3(A_1221)
      | ~ v5_orders_2(A_1221)
      | ~ v4_orders_2(A_1221)
      | ~ v3_orders_2(A_1221)
      | ~ v8_pre_topc(A_1221)
      | ~ v2_pre_topc(A_1221)
      | k1_yellow_0(A_1221,k2_relset_1(u1_struct_0(B_1222),u1_struct_0(A_1221),u1_waybel_0(A_1221,B_1222))) = C_1224
      | ~ r2_lattice3(A_1221,k2_relset_1(u1_struct_0(B_1222),u1_struct_0(A_1221),u1_waybel_0(A_1221,B_1222)),C_1224)
      | ~ r1_yellow_0(A_1221,k2_relset_1(u1_struct_0(B_1222),u1_struct_0(A_1221),u1_waybel_0(A_1221,B_1222)))
      | ~ m1_subset_1(C_1224,u1_struct_0(A_1221))
      | ~ l1_orders_2(A_1221)
      | ~ l1_waybel_0(B_1222,A_1221)
      | ~ l1_struct_0(A_1221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_2919])).

tff(c_8637,plain,(
    ! [B_74,D_1223,D_86] :
      ( m1_subset_1('#skF_5'('#skF_6',B_74,D_1223,D_1223),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1223,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_74)),D_86))
      | ~ r3_waybel_9('#skF_6',B_74,D_1223)
      | ~ m1_subset_1(D_1223,u1_struct_0('#skF_6'))
      | ~ l1_waybel_9('#skF_6')
      | ~ v1_compts_1('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ v8_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_74),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_74))) = D_86
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_74),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_74)))
      | ~ l1_orders_2('#skF_6')
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6',B_74,D_86)
      | ~ v10_waybel_0(B_74,'#skF_6')
      | ~ m1_subset_1(D_86,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_74,'#skF_6')
      | ~ v7_waybel_0(B_74)
      | ~ v4_orders_2(B_74)
      | v2_struct_0(B_74) ) ),
    inference(resolution,[status(thm)],[c_791,c_8625])).

tff(c_10831,plain,(
    ! [B_1258,D_1259,D_1260] :
      ( m1_subset_1('#skF_5'('#skF_6',B_1258,D_1259,D_1259),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1259,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1258)),D_1260))
      | ~ r3_waybel_9('#skF_6',B_1258,D_1259)
      | ~ m1_subset_1(D_1259,u1_struct_0('#skF_6'))
      | k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_1258),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1258))) = D_1260
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_1258),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1258)))
      | ~ r3_waybel_9('#skF_6',B_1258,D_1260)
      | ~ v10_waybel_0(B_1258,'#skF_6')
      | ~ m1_subset_1(D_1260,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_1258,'#skF_6')
      | ~ v7_waybel_0(B_1258)
      | ~ v4_orders_2(B_1258)
      | v2_struct_0(B_1258) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_97,c_92,c_90,c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_8637])).

tff(c_10840,plain,(
    ! [B_168,D_1259,D_1260] :
      ( m1_subset_1('#skF_5'('#skF_6',B_168,D_1259,D_1259),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1259,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)),D_1260))
      | ~ r3_waybel_9('#skF_6',B_168,D_1259)
      | ~ m1_subset_1(D_1259,u1_struct_0('#skF_6'))
      | k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_168),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_168))) = D_1260
      | ~ r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)))
      | ~ r3_waybel_9('#skF_6',B_168,D_1260)
      | ~ v10_waybel_0(B_168,'#skF_6')
      | ~ m1_subset_1(D_1260,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ v7_waybel_0(B_168)
      | ~ v4_orders_2(B_168)
      | v2_struct_0(B_168)
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_10831])).

tff(c_20755,plain,(
    ! [B_168,D_1259] :
      ( m1_subset_1('#skF_5'('#skF_6',B_168,D_1259,D_1259),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1259,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)),'#skF_7'))
      | ~ r3_waybel_9('#skF_6',B_168,D_1259)
      | ~ m1_subset_1(D_1259,u1_struct_0('#skF_6'))
      | k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_168),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_168))) = '#skF_7'
      | ~ r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)))
      | ~ r3_waybel_9('#skF_6',B_168,'#skF_7')
      | ~ v10_waybel_0(B_168,'#skF_6')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_168)
      | ~ v4_orders_2(B_168)
      | v2_struct_0(B_168)
      | ~ l1_waybel_0(B_168,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_10840])).

tff(c_962,plain,(
    ! [D_389,B_391,C_45] :
      ( r3_orders_2('#skF_6',D_389,'#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391)),C_45))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391)),C_45),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_391,D_389)
      | ~ m1_subset_1(D_389,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_391,'#skF_6')
      | ~ v7_waybel_0(B_391)
      | ~ v4_orders_2(B_391)
      | v2_struct_0(B_391)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_391,D_389,D_389),u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391)))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_951])).

tff(c_1962,plain,(
    ! [D_576,B_577,C_578] :
      ( r3_orders_2('#skF_6',D_576,'#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)),C_578))
      | ~ m1_subset_1('#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)),C_578),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_577,D_576)
      | ~ m1_subset_1(D_576,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_577,'#skF_6')
      | ~ v7_waybel_0(B_577)
      | ~ v4_orders_2(B_577)
      | v2_struct_0(B_577)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_577,D_576,D_576),u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)),C_578)
      | ~ m1_subset_1(C_578,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_962])).

tff(c_1965,plain,(
    ! [D_576,B_577,C_45] :
      ( r3_orders_2('#skF_6',D_576,'#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)),C_45))
      | ~ r3_waybel_9('#skF_6',B_577,D_576)
      | ~ m1_subset_1(D_576,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_577,'#skF_6')
      | ~ v7_waybel_0(B_577)
      | ~ v4_orders_2(B_577)
      | v2_struct_0(B_577)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_577,D_576,D_576),u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_1962])).

tff(c_1971,plain,(
    ! [D_576,B_577,C_45] :
      ( r3_orders_2('#skF_6',D_576,'#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)),C_45))
      | ~ r3_waybel_9('#skF_6',B_577,D_576)
      | ~ m1_subset_1(D_576,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_577,'#skF_6')
      | ~ v7_waybel_0(B_577)
      | ~ v4_orders_2(B_577)
      | v2_struct_0(B_577)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_577,D_576,D_576),u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_577),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_577)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_1965])).

tff(c_2603,plain,(
    ! [D_673,B_672,C_45,C_674] :
      ( r3_orders_2('#skF_6',D_673,'#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)),C_45))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_673,'#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)),C_674))
      | ~ r3_waybel_9('#skF_6',B_672,D_673)
      | ~ m1_subset_1(D_673,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_672,'#skF_6')
      | ~ v7_waybel_0(B_672)
      | ~ v4_orders_2(B_672)
      | v2_struct_0(B_672)
      | ~ l1_waybel_9('#skF_6')
      | ~ v1_compts_1('#skF_6')
      | ~ v2_lattice3('#skF_6')
      | ~ v1_lattice3('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | ~ v8_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)),C_674)
      | ~ m1_subset_1(C_674,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2600,c_1971])).

tff(c_2636,plain,(
    ! [D_673,B_672,C_45,C_674] :
      ( r3_orders_2('#skF_6',D_673,'#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)),C_45))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)),C_45)
      | ~ m1_subset_1(C_45,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_673,'#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)),C_674))
      | ~ r3_waybel_9('#skF_6',B_672,D_673)
      | ~ m1_subset_1(D_673,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_672,'#skF_6')
      | ~ v7_waybel_0(B_672)
      | ~ v4_orders_2(B_672)
      | v2_struct_0(B_672)
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_672),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_672)),C_674)
      | ~ m1_subset_1(C_674,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_92,c_90,c_88,c_86,c_82,c_80,c_78,c_76,c_2603])).

tff(c_11747,plain,(
    ! [B_1329,D_1330,C_1331] :
      ( ~ r3_waybel_9('#skF_6',B_1329,D_1330)
      | ~ m1_subset_1(D_1330,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_1329,'#skF_6')
      | ~ v7_waybel_0(B_1329)
      | ~ v4_orders_2(B_1329)
      | v2_struct_0(B_1329)
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_1329),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1329)))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_1329),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1329)),C_1331)
      | ~ m1_subset_1(C_1331,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1330,'#skF_2'('#skF_6',k2_relset_1(u1_struct_0(B_1329),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1329)),C_1331)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2636])).

tff(c_11753,plain,(
    ! [B_168,D_1330,C_1331] :
      ( ~ r3_waybel_9('#skF_6',B_168,D_1330)
      | ~ m1_subset_1(D_1330,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ v7_waybel_0(B_168)
      | ~ v4_orders_2(B_168)
      | v2_struct_0(B_168)
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_168),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_168)))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_168),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_168)),C_1331)
      | ~ m1_subset_1(C_1331,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1330,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)),C_1331))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_11747])).

tff(c_11760,plain,(
    ! [B_1332,D_1333,C_1334] :
      ( ~ r3_waybel_9('#skF_6',B_1332,D_1333)
      | ~ m1_subset_1(D_1333,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1332)
      | ~ v4_orders_2(B_1332)
      | v2_struct_0(B_1332)
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_1332),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1332)))
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_1332),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1332)),C_1334)
      | ~ m1_subset_1(C_1334,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1333,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1332)),C_1334))
      | ~ l1_waybel_0(B_1332,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_11753])).

tff(c_11812,plain,(
    ! [B_1335,D_1336,D_1337] :
      ( ~ r3_waybel_9('#skF_6',B_1335,D_1336)
      | ~ m1_subset_1(D_1336,u1_struct_0('#skF_6'))
      | r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_1335),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1335)))
      | r3_orders_2('#skF_6',D_1336,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1335)),D_1337))
      | ~ r3_waybel_9('#skF_6',B_1335,D_1337)
      | ~ v10_waybel_0(B_1335,'#skF_6')
      | ~ m1_subset_1(D_1337,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_1335,'#skF_6')
      | ~ v7_waybel_0(B_1335)
      | ~ v4_orders_2(B_1335)
      | v2_struct_0(B_1335) ) ),
    inference(resolution,[status(thm)],[c_791,c_11760])).

tff(c_11830,plain,(
    ! [B_1335,D_1336,D_1337] :
      ( k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_1335),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1335))) = '#skF_3'('#skF_6',k2_relset_1(u1_struct_0(B_1335),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1335)))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ r3_waybel_9('#skF_6',B_1335,D_1336)
      | ~ m1_subset_1(D_1336,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1336,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1335)),D_1337))
      | ~ r3_waybel_9('#skF_6',B_1335,D_1337)
      | ~ v10_waybel_0(B_1335,'#skF_6')
      | ~ m1_subset_1(D_1337,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_1335,'#skF_6')
      | ~ v7_waybel_0(B_1335)
      | ~ v4_orders_2(B_1335)
      | v2_struct_0(B_1335) ) ),
    inference(resolution,[status(thm)],[c_11812,c_950])).

tff(c_12271,plain,(
    ! [B_1379,D_1380,D_1381] :
      ( k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_1379),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1379))) = '#skF_3'('#skF_6',k2_relset_1(u1_struct_0(B_1379),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1379)))
      | ~ r3_waybel_9('#skF_6',B_1379,D_1380)
      | ~ m1_subset_1(D_1380,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1380,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1379)),D_1381))
      | ~ r3_waybel_9('#skF_6',B_1379,D_1381)
      | ~ v10_waybel_0(B_1379,'#skF_6')
      | ~ m1_subset_1(D_1381,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_1379,'#skF_6')
      | ~ v7_waybel_0(B_1379)
      | ~ v4_orders_2(B_1379)
      | v2_struct_0(B_1379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_11830])).

tff(c_12301,plain,(
    ! [B_168,D_1380,D_1381] :
      ( '#skF_3'('#skF_6',k2_relset_1(u1_struct_0(B_168),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_168))) = k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)))
      | ~ r3_waybel_9('#skF_6',B_168,D_1380)
      | ~ m1_subset_1(D_1380,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1380,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_168)),D_1381))
      | ~ r3_waybel_9('#skF_6',B_168,D_1381)
      | ~ v10_waybel_0(B_168,'#skF_6')
      | ~ m1_subset_1(D_1381,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ v7_waybel_0(B_168)
      | ~ v4_orders_2(B_168)
      | v2_struct_0(B_168)
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_12271])).

tff(c_12379,plain,(
    ! [B_1386,D_1387,D_1388] :
      ( '#skF_3'('#skF_6',k2_relset_1(u1_struct_0(B_1386),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1386))) = k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1386)))
      | ~ r3_waybel_9('#skF_6',B_1386,D_1387)
      | ~ m1_subset_1(D_1387,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1387,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1386)),D_1388))
      | ~ r3_waybel_9('#skF_6',B_1386,D_1388)
      | ~ v10_waybel_0(B_1386,'#skF_6')
      | ~ m1_subset_1(D_1388,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1386)
      | ~ v4_orders_2(B_1386)
      | v2_struct_0(B_1386)
      | ~ l1_waybel_0(B_1386,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_12301])).

tff(c_12446,plain,(
    ! [B_1386,D_1387,D_1388] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_1386),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1386)),k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1386))))
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_1386),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_1386)))
      | ~ l1_orders_2('#skF_6')
      | ~ v5_orders_2('#skF_6')
      | ~ r3_waybel_9('#skF_6',B_1386,D_1387)
      | ~ m1_subset_1(D_1387,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1387,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_1386)),D_1388))
      | ~ r3_waybel_9('#skF_6',B_1386,D_1388)
      | ~ v10_waybel_0(B_1386,'#skF_6')
      | ~ m1_subset_1(D_1388,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_1386)
      | ~ v4_orders_2(B_1386)
      | v2_struct_0(B_1386)
      | ~ l1_waybel_0(B_1386,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12379,c_26])).

tff(c_20163,plain,(
    ! [B_15048,D_15049,D_15050] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_15048),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_15048)),k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_15048))))
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_15048),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_15048)))
      | ~ r3_waybel_9('#skF_6',B_15048,D_15049)
      | ~ m1_subset_1(D_15049,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_15049,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6',B_15048)),D_15050))
      | ~ r3_waybel_9('#skF_6',B_15048,D_15050)
      | ~ v10_waybel_0(B_15048,'#skF_6')
      | ~ m1_subset_1(D_15050,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0(B_15048)
      | ~ v4_orders_2(B_15048)
      | v2_struct_0(B_15048)
      | ~ l1_waybel_0(B_15048,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_12446])).

tff(c_20228,plain,(
    ! [D_15049,D_15050] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),k1_waybel_2('#skF_6','#skF_8'))
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15049)
      | ~ m1_subset_1(D_15049,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_15049,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_15050))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15050)
      | ~ v10_waybel_0('#skF_8','#skF_6')
      | ~ m1_subset_1(D_15050,u1_struct_0('#skF_6'))
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9700,c_20163])).

tff(c_20260,plain,(
    ! [D_15049,D_15050] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),k1_waybel_2('#skF_6','#skF_8'))
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15049)
      | ~ m1_subset_1(D_15049,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_15049,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_15050))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15050)
      | ~ m1_subset_1(D_15050,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_62,c_20228])).

tff(c_20261,plain,(
    ! [D_15049,D_15050] :
      ( r2_lattice3('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),k1_waybel_2('#skF_6','#skF_8'))
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15049)
      | ~ m1_subset_1(D_15049,u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_15049,'#skF_2'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_15050))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15050)
      | ~ m1_subset_1(D_15050,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_20260])).

tff(c_20267,plain,(
    ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_20261])).

tff(c_20282,plain,
    ( ~ r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | ~ l1_waybel_0('#skF_8','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_20267])).

tff(c_20301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_66,c_7522,c_20282])).

tff(c_20303,plain,(
    r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_20261])).

tff(c_20325,plain,
    ( k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8'))) = '#skF_3'('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')))
    | ~ l1_orders_2('#skF_6')
    | ~ v5_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_20303,c_950])).

tff(c_20367,plain,(
    k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8'))) = '#skF_3'('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_97,c_20325])).

tff(c_20458,plain,
    ( '#skF_3'('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8'))) = k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | ~ l1_waybel_0('#skF_8','#skF_6')
    | ~ l1_struct_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_20367])).

tff(c_20513,plain,(
    '#skF_3'('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8'))) = k1_waybel_2('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_66,c_9700,c_20458])).

tff(c_20514,plain,(
    k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8'))) = k1_waybel_2('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20513,c_20367])).

tff(c_20758,plain,(
    ! [D_1259] :
      ( k1_waybel_2('#skF_6','#skF_8') = '#skF_7'
      | m1_subset_1('#skF_5'('#skF_6','#skF_8',D_1259,D_1259),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1259,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_1259)
      | ~ m1_subset_1(D_1259,u1_struct_0('#skF_6'))
      | ~ r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
      | ~ r3_waybel_9('#skF_6','#skF_8','#skF_7')
      | ~ v10_waybel_0('#skF_8','#skF_6')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0('#skF_8','#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20755,c_20514])).

tff(c_20813,plain,(
    ! [D_1259] :
      ( k1_waybel_2('#skF_6','#skF_8') = '#skF_7'
      | m1_subset_1('#skF_5'('#skF_6','#skF_8',D_1259,D_1259),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_1259,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_1259)
      | ~ m1_subset_1(D_1259,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_74,c_62,c_60,c_7522,c_20758])).

tff(c_20826,plain,(
    ! [D_15255] :
      ( m1_subset_1('#skF_5'('#skF_6','#skF_8',D_15255,D_15255),u1_struct_0('#skF_6'))
      | r3_orders_2('#skF_6',D_15255,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15255)
      | ~ m1_subset_1(D_15255,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_58,c_20813])).

tff(c_20846,plain,(
    ! [D_15255] :
      ( r1_orders_2('#skF_6',D_15255,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'),u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | m1_subset_1('#skF_5'('#skF_6','#skF_8',D_15255,D_15255),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15255)
      | ~ m1_subset_1(D_15255,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_20826,c_10])).

tff(c_20878,plain,(
    ! [D_15255] :
      ( r1_orders_2('#skF_6',D_15255,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | m1_subset_1('#skF_5'('#skF_6','#skF_8',D_15255,D_15255),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15255)
      | ~ m1_subset_1(D_15255,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_97,c_20846])).

tff(c_20879,plain,(
    ! [D_15255] :
      ( r1_orders_2('#skF_6',D_15255,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'))
      | ~ m1_subset_1('#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'),u1_struct_0('#skF_6'))
      | m1_subset_1('#skF_5'('#skF_6','#skF_8',D_15255,D_15255),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15255)
      | ~ m1_subset_1(D_15255,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_20878])).

tff(c_21408,plain,(
    ~ m1_subset_1('#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_20879])).

tff(c_21411,plain,
    ( k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = '#skF_7'
    | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7')
    | ~ r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_21408])).

tff(c_21414,plain,
    ( k1_waybel_2('#skF_6','#skF_8') = '#skF_7'
    | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_74,c_7522,c_9700,c_21411])).

tff(c_21415,plain,(
    ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_21414])).

tff(c_21427,plain,
    ( ~ r3_waybel_9('#skF_6','#skF_8','#skF_7')
    | ~ v10_waybel_0('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v7_waybel_0('#skF_8')
    | ~ v4_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l1_waybel_0('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_805,c_21415])).

tff(c_21442,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_74,c_62,c_60,c_21427])).

tff(c_21444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_21442])).

tff(c_21484,plain,(
    ! [D_15812] :
      ( r1_orders_2('#skF_6',D_15812,'#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'))
      | m1_subset_1('#skF_5'('#skF_6','#skF_8',D_15812,D_15812),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6','#skF_8',D_15812)
      | ~ m1_subset_1(D_15812,u1_struct_0('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_20879])).

tff(c_21488,plain,
    ( k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = '#skF_7'
    | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7')
    | ~ r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | ~ l1_orders_2('#skF_6')
    | m1_subset_1('#skF_5'('#skF_6','#skF_8','#skF_7','#skF_7'),u1_struct_0('#skF_6'))
    | ~ r3_waybel_9('#skF_6','#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_21484,c_14])).

tff(c_21514,plain,
    ( k1_waybel_2('#skF_6','#skF_8') = '#skF_7'
    | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7')
    | m1_subset_1('#skF_5'('#skF_6','#skF_8','#skF_7','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_97,c_7522,c_9700,c_21488])).

tff(c_21515,plain,
    ( ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7')
    | m1_subset_1('#skF_5'('#skF_6','#skF_8','#skF_7','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_21514])).

tff(c_21605,plain,(
    ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_21515])).

tff(c_21617,plain,
    ( ~ r3_waybel_9('#skF_6','#skF_8','#skF_7')
    | ~ v10_waybel_0('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ v7_waybel_0('#skF_8')
    | ~ v4_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l1_waybel_0('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_805,c_21605])).

tff(c_21632,plain,(
    v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_70,c_68,c_74,c_62,c_60,c_21617])).

tff(c_21634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_21632])).

tff(c_21636,plain,(
    r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_21515])).

tff(c_21446,plain,(
    m1_subset_1('#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_20879])).

tff(c_21635,plain,(
    m1_subset_1('#skF_5'('#skF_6','#skF_8','#skF_7','#skF_7'),u1_struct_0('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_21515])).

tff(c_959,plain,(
    ! [D_389,B_391,C_20] :
      ( r3_orders_2('#skF_6',D_389,'#skF_1'('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391)),C_20))
      | ~ m1_subset_1('#skF_1'('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391)),C_20),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_391,D_389)
      | ~ m1_subset_1(D_389,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_391,'#skF_6')
      | ~ v7_waybel_0(B_391)
      | ~ v4_orders_2(B_391)
      | v2_struct_0(B_391)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_391,D_389,D_389),u1_struct_0('#skF_6'))
      | k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391))) = C_20
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391)),C_20)
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_391)))
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_16,c_951])).

tff(c_2793,plain,(
    ! [D_685,B_686,C_687] :
      ( r3_orders_2('#skF_6',D_685,'#skF_1'('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)),C_687))
      | ~ m1_subset_1('#skF_1'('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)),C_687),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6',B_686,D_685)
      | ~ m1_subset_1(D_685,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_686,'#skF_6')
      | ~ v7_waybel_0(B_686)
      | ~ v4_orders_2(B_686)
      | v2_struct_0(B_686)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_686,D_685,D_685),u1_struct_0('#skF_6'))
      | k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686))) = C_687
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)),C_687)
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)))
      | ~ m1_subset_1(C_687,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_959])).

tff(c_2796,plain,(
    ! [D_685,B_686,C_20] :
      ( r3_orders_2('#skF_6',D_685,'#skF_1'('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)),C_20))
      | ~ r3_waybel_9('#skF_6',B_686,D_685)
      | ~ m1_subset_1(D_685,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_686,'#skF_6')
      | ~ v7_waybel_0(B_686)
      | ~ v4_orders_2(B_686)
      | v2_struct_0(B_686)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_686,D_685,D_685),u1_struct_0('#skF_6'))
      | k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686))) = C_20
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)),C_20)
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)))
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_2793])).

tff(c_2802,plain,(
    ! [D_685,B_686,C_20] :
      ( r3_orders_2('#skF_6',D_685,'#skF_1'('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)),C_20))
      | ~ r3_waybel_9('#skF_6',B_686,D_685)
      | ~ m1_subset_1(D_685,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_686,'#skF_6')
      | ~ v7_waybel_0(B_686)
      | ~ v4_orders_2(B_686)
      | v2_struct_0(B_686)
      | ~ m1_subset_1('#skF_5'('#skF_6',B_686,D_685,D_685),u1_struct_0('#skF_6'))
      | k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686))) = C_20
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)),C_20)
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0(B_686),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6',B_686)))
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_2796])).

tff(c_21933,plain,(
    ! [C_20] :
      ( r3_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),C_20))
      | ~ r3_waybel_9('#skF_6','#skF_8','#skF_7')
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_8','#skF_6')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | k1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8'))) = C_20
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),C_20)
      | ~ r1_yellow_0('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')))
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_21635,c_2802])).

tff(c_21954,plain,(
    ! [C_20] :
      ( r3_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),C_20))
      | v2_struct_0('#skF_8')
      | k1_waybel_2('#skF_6','#skF_8') = C_20
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20303,c_20514,c_70,c_68,c_66,c_74,c_60,c_21933])).

tff(c_22592,plain,(
    ! [C_16478] :
      ( r3_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),C_16478))
      | k1_waybel_2('#skF_6','#skF_8') = C_16478
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),C_16478)
      | ~ m1_subset_1(C_16478,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_21954])).

tff(c_22600,plain,(
    ! [C_16478] :
      ( r3_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),C_16478))
      | k1_waybel_2('#skF_6','#skF_8') = C_16478
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),C_16478)
      | ~ m1_subset_1(C_16478,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_8','#skF_6')
      | ~ l1_struct_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_22592])).

tff(c_22607,plain,(
    ! [C_16513] :
      ( r3_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),C_16513))
      | k1_waybel_2('#skF_6','#skF_8') = C_16513
      | ~ r2_lattice3('#skF_6',k2_relset_1(u1_struct_0('#skF_8'),u1_struct_0('#skF_6'),u1_waybel_0('#skF_6','#skF_8')),C_16513)
      | ~ m1_subset_1(C_16513,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_806,c_66,c_22600])).

tff(c_22638,plain,(
    ! [D_86] :
      ( r3_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_86))
      | k1_waybel_2('#skF_6','#skF_8') = D_86
      | ~ r3_waybel_9('#skF_6','#skF_8',D_86)
      | ~ v10_waybel_0('#skF_8','#skF_6')
      | ~ m1_subset_1(D_86,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_8','#skF_6')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_791,c_22607])).

tff(c_22688,plain,(
    ! [D_86] :
      ( r3_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_86))
      | k1_waybel_2('#skF_6','#skF_8') = D_86
      | ~ r3_waybel_9('#skF_6','#skF_8',D_86)
      | ~ m1_subset_1(D_86,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_62,c_22638])).

tff(c_22705,plain,(
    ! [D_16548] :
      ( r3_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_16548))
      | k1_waybel_2('#skF_6','#skF_8') = D_16548
      | ~ r3_waybel_9('#skF_6','#skF_8',D_16548)
      | ~ m1_subset_1(D_16548,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_22688])).

tff(c_22707,plain,(
    ! [D_16548] :
      ( r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_16548))
      | ~ m1_subset_1('#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_16548),u1_struct_0('#skF_6'))
      | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
      | ~ l1_orders_2('#skF_6')
      | ~ v3_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | k1_waybel_2('#skF_6','#skF_8') = D_16548
      | ~ r3_waybel_9('#skF_6','#skF_8',D_16548)
      | ~ m1_subset_1(D_16548,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_22705,c_10])).

tff(c_22713,plain,(
    ! [D_16548] :
      ( r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_16548))
      | ~ m1_subset_1('#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_16548),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | k1_waybel_2('#skF_6','#skF_8') = D_16548
      | ~ r3_waybel_9('#skF_6','#skF_8',D_16548)
      | ~ m1_subset_1(D_16548,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_97,c_74,c_22707])).

tff(c_22715,plain,(
    ! [D_16583] :
      ( r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_16583))
      | ~ m1_subset_1('#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),D_16583),u1_struct_0('#skF_6'))
      | k1_waybel_2('#skF_6','#skF_8') = D_16583
      | ~ r3_waybel_9('#skF_6','#skF_8',D_16583)
      | ~ m1_subset_1(D_16583,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_22713])).

tff(c_22718,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'))
    | k1_waybel_2('#skF_6','#skF_8') = '#skF_7'
    | ~ r3_waybel_9('#skF_6','#skF_8','#skF_7')
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6')) ),
    inference(resolution,[status(thm)],[c_21446,c_22715])).

tff(c_22728,plain,
    ( r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7'))
    | k1_waybel_2('#skF_6','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_60,c_22718])).

tff(c_22729,plain,(
    r1_orders_2('#skF_6','#skF_7','#skF_1'('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_22728])).

tff(c_22735,plain,
    ( k1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8'))) = '#skF_7'
    | ~ r2_lattice3('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')),'#skF_7')
    | ~ r1_yellow_0('#skF_6',k2_relat_1(u1_waybel_0('#skF_6','#skF_8')))
    | ~ m1_subset_1('#skF_7',u1_struct_0('#skF_6'))
    | ~ l1_orders_2('#skF_6') ),
    inference(resolution,[status(thm)],[c_22729,c_14])).

tff(c_22738,plain,(
    k1_waybel_2('#skF_6','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_74,c_7522,c_21636,c_9700,c_22735])).

tff(c_22740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_22738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.28/10.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.41/10.38  
% 20.41/10.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.41/10.39  %$ v5_pre_topc > v1_funct_2 > r3_waybel_9 > r3_orders_2 > r2_lattice3 > r1_orders_2 > v10_waybel_0 > r1_yellow_0 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_relat_1 > v1_lattice3 > v1_funct_1 > v1_compts_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_yellow_2 > k4_waybel_1 > k2_zfmisc_1 > k1_yellow_0 > k1_waybel_2 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_5
% 20.41/10.39  
% 20.41/10.39  %Foreground sorts:
% 20.41/10.39  
% 20.41/10.39  
% 20.41/10.39  %Background operators:
% 20.41/10.39  
% 20.41/10.39  
% 20.41/10.39  %Foreground operators:
% 20.41/10.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 20.41/10.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 20.41/10.39  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 20.41/10.39  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 20.41/10.39  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 20.41/10.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 20.41/10.39  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 20.41/10.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.41/10.39  tff(k4_yellow_2, type, k4_yellow_2: ($i * $i) > $i).
% 20.41/10.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.41/10.39  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 20.41/10.39  tff(v10_waybel_0, type, v10_waybel_0: ($i * $i) > $o).
% 20.41/10.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 20.41/10.39  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 20.41/10.39  tff('#skF_7', type, '#skF_7': $i).
% 20.41/10.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 20.41/10.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.41/10.39  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 20.41/10.39  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 20.41/10.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 20.41/10.39  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 20.41/10.39  tff('#skF_6', type, '#skF_6': $i).
% 20.41/10.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.41/10.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 20.41/10.39  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 20.41/10.39  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 20.41/10.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 20.41/10.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 20.41/10.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 20.41/10.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 20.41/10.39  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 20.41/10.39  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 20.41/10.39  tff('#skF_8', type, '#skF_8': $i).
% 20.41/10.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.41/10.39  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 20.41/10.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 20.41/10.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.41/10.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 20.41/10.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.41/10.39  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 20.41/10.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 20.41/10.39  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 20.41/10.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 20.41/10.39  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 20.41/10.39  tff(k1_waybel_2, type, k1_waybel_2: ($i * $i) > $i).
% 20.41/10.39  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 20.41/10.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 20.41/10.39  
% 20.72/10.46  tff(f_272, negated_conjecture, ~(![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => ((((![D]: (m1_subset_1(D, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, D), A, A))) & v10_waybel_0(C, A)) & r3_waybel_9(A, C, B)) => (B = k1_waybel_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_waybel_9)).
% 20.72/10.46  tff(f_132, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 20.72/10.46  tff(f_37, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 20.72/10.46  tff(f_106, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 20.72/10.46  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 20.72/10.46  tff(f_179, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & v10_waybel_0(B, A)) & r3_waybel_9(A, B, C)) => r2_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l48_waybel_9)).
% 20.72/10.46  tff(f_96, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (r1_yellow_0(A, B) <=> (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r2_lattice3(A, B, C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow_0)).
% 20.72/10.46  tff(f_52, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 20.72/10.46  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 20.72/10.46  tff(f_229, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & r3_waybel_9(A, B, C)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r2_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), E) => r3_orders_2(A, D, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_waybel_9)).
% 20.72/10.46  tff(f_116, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (l1_waybel_0(B, A) => (k1_waybel_2(A, B) = k4_yellow_2(A, u1_waybel_0(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_waybel_2)).
% 20.72/10.46  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 20.72/10.46  tff(f_77, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r1_yellow_0(A, B) => ((C = k1_yellow_0(A, B)) <=> (r2_lattice3(A, B, C) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_yellow_0)).
% 20.72/10.46  tff(f_126, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (v1_relat_1(B) => (k4_yellow_2(A, B) = k1_yellow_0(A, k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_2)).
% 20.72/10.46  tff(c_58, plain, (k1_waybel_2('#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_76, plain, (l1_waybel_9('#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_93, plain, (![A_146]: (l1_orders_2(A_146) | ~l1_waybel_9(A_146))), inference(cnfTransformation, [status(thm)], [f_132])).
% 20.72/10.46  tff(c_97, plain, (l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_76, c_93])).
% 20.72/10.46  tff(c_74, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_72, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_66, plain, (l1_waybel_0('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_70, plain, (v4_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_68, plain, (v7_waybel_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_62, plain, (v10_waybel_0('#skF_8', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_60, plain, (r3_waybel_9('#skF_6', '#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_6, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 20.72/10.46  tff(c_121, plain, (![A_167, B_168]: (m1_subset_1(u1_waybel_0(A_167, B_168), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_168), u1_struct_0(A_167)))) | ~l1_waybel_0(B_168, A_167) | ~l1_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_106])).
% 20.72/10.46  tff(c_4, plain, (![A_4, B_5, C_6]: (k2_relset_1(A_4, B_5, C_6)=k2_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 20.72/10.46  tff(c_128, plain, (![B_168, A_167]: (k2_relset_1(u1_struct_0(B_168), u1_struct_0(A_167), u1_waybel_0(A_167, B_168))=k2_relat_1(u1_waybel_0(A_167, B_168)) | ~l1_waybel_0(B_168, A_167) | ~l1_struct_0(A_167))), inference(resolution, [status(thm)], [c_121, c_4])).
% 20.72/10.46  tff(c_92, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_90, plain, (v8_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_88, plain, (v3_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_86, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_84, plain, (v5_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_82, plain, (v1_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_80, plain, (v2_lattice3('#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_78, plain, (v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_52, plain, (![A_58, B_74, D_86]: (m1_subset_1('#skF_4'(A_58, B_74, D_86, D_86), u1_struct_0(A_58)) | r2_lattice3(A_58, k2_relset_1(u1_struct_0(B_74), u1_struct_0(A_58), u1_waybel_0(A_58, B_74)), D_86) | ~r3_waybel_9(A_58, B_74, D_86) | ~v10_waybel_0(B_74, A_58) | ~m1_subset_1(D_86, u1_struct_0(A_58)) | ~l1_waybel_0(B_74, A_58) | ~v7_waybel_0(B_74) | ~v4_orders_2(B_74) | v2_struct_0(B_74) | ~l1_waybel_9(A_58) | ~v1_compts_1(A_58) | ~v2_lattice3(A_58) | ~v1_lattice3(A_58) | ~v5_orders_2(A_58) | ~v4_orders_2(A_58) | ~v3_orders_2(A_58) | ~v8_pre_topc(A_58) | ~v2_pre_topc(A_58))), inference(cnfTransformation, [status(thm)], [f_179])).
% 20.72/10.46  tff(c_64, plain, (![D_145]: (v5_pre_topc(k4_waybel_1('#skF_6', D_145), '#skF_6', '#skF_6') | ~m1_subset_1(D_145, u1_struct_0('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_272])).
% 20.72/10.46  tff(c_767, plain, (![A_343, B_344, D_345]: (~v5_pre_topc(k4_waybel_1(A_343, '#skF_4'(A_343, B_344, D_345, D_345)), A_343, A_343) | r2_lattice3(A_343, k2_relset_1(u1_struct_0(B_344), u1_struct_0(A_343), u1_waybel_0(A_343, B_344)), D_345) | ~r3_waybel_9(A_343, B_344, D_345) | ~v10_waybel_0(B_344, A_343) | ~m1_subset_1(D_345, u1_struct_0(A_343)) | ~l1_waybel_0(B_344, A_343) | ~v7_waybel_0(B_344) | ~v4_orders_2(B_344) | v2_struct_0(B_344) | ~l1_waybel_9(A_343) | ~v1_compts_1(A_343) | ~v2_lattice3(A_343) | ~v1_lattice3(A_343) | ~v5_orders_2(A_343) | ~v4_orders_2(A_343) | ~v3_orders_2(A_343) | ~v8_pre_topc(A_343) | ~v2_pre_topc(A_343))), inference(cnfTransformation, [status(thm)], [f_179])).
% 20.72/10.46  tff(c_770, plain, (![B_344, D_345]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_344), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_344)), D_345) | ~r3_waybel_9('#skF_6', B_344, D_345) | ~v10_waybel_0(B_344, '#skF_6') | ~m1_subset_1(D_345, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_344, '#skF_6') | ~v7_waybel_0(B_344) | ~v4_orders_2(B_344) | v2_struct_0(B_344) | ~l1_waybel_9('#skF_6') | ~v1_compts_1('#skF_6') | ~v2_lattice3('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | ~v8_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | ~m1_subset_1('#skF_4'('#skF_6', B_344, D_345, D_345), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_64, c_767])).
% 20.72/10.46  tff(c_785, plain, (![B_350, D_351]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_350), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_350)), D_351) | ~r3_waybel_9('#skF_6', B_350, D_351) | ~v10_waybel_0(B_350, '#skF_6') | ~m1_subset_1(D_351, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_350, '#skF_6') | ~v7_waybel_0(B_350) | ~v4_orders_2(B_350) | v2_struct_0(B_350) | ~m1_subset_1('#skF_4'('#skF_6', B_350, D_351, D_351), u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_770])).
% 20.72/10.46  tff(c_788, plain, (![B_74, D_86]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_74), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_74)), D_86) | ~r3_waybel_9('#skF_6', B_74, D_86) | ~v10_waybel_0(B_74, '#skF_6') | ~m1_subset_1(D_86, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_74, '#skF_6') | ~v7_waybel_0(B_74) | ~v4_orders_2(B_74) | v2_struct_0(B_74) | ~l1_waybel_9('#skF_6') | ~v1_compts_1('#skF_6') | ~v2_lattice3('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | ~v8_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_785])).
% 20.72/10.46  tff(c_792, plain, (![B_352, D_353]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_352), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_352)), D_353) | ~r3_waybel_9('#skF_6', B_352, D_353) | ~v10_waybel_0(B_352, '#skF_6') | ~m1_subset_1(D_353, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_352, '#skF_6') | ~v7_waybel_0(B_352) | ~v4_orders_2(B_352) | v2_struct_0(B_352))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_788])).
% 20.72/10.46  tff(c_796, plain, (![B_168, D_353]: (r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168)), D_353) | ~r3_waybel_9('#skF_6', B_168, D_353) | ~v10_waybel_0(B_168, '#skF_6') | ~m1_subset_1(D_353, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_168, '#skF_6') | ~v7_waybel_0(B_168) | ~v4_orders_2(B_168) | v2_struct_0(B_168) | ~l1_waybel_0(B_168, '#skF_6') | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_792])).
% 20.72/10.46  tff(c_797, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_796])).
% 20.72/10.46  tff(c_800, plain, (~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_6, c_797])).
% 20.72/10.46  tff(c_804, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_800])).
% 20.72/10.46  tff(c_805, plain, (![B_168, D_353]: (r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168)), D_353) | ~r3_waybel_9('#skF_6', B_168, D_353) | ~v10_waybel_0(B_168, '#skF_6') | ~m1_subset_1(D_353, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_168, '#skF_6') | ~v7_waybel_0(B_168) | ~v4_orders_2(B_168) | v2_struct_0(B_168) | ~l1_waybel_0(B_168, '#skF_6'))), inference(splitRight, [status(thm)], [c_796])).
% 20.72/10.46  tff(c_34, plain, (![A_24, B_38, C_45]: (m1_subset_1('#skF_2'(A_24, B_38, C_45), u1_struct_0(A_24)) | r1_yellow_0(A_24, B_38) | ~r2_lattice3(A_24, B_38, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_24)) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 20.72/10.46  tff(c_156, plain, (![A_189, B_190, C_191]: (r3_orders_2(A_189, B_190, C_191) | ~r1_orders_2(A_189, B_190, C_191) | ~m1_subset_1(C_191, u1_struct_0(A_189)) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~l1_orders_2(A_189) | ~v3_orders_2(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.72/10.46  tff(c_162, plain, (![B_190]: (r3_orders_2('#skF_6', B_190, '#skF_7') | ~r1_orders_2('#skF_6', B_190, '#skF_7') | ~m1_subset_1(B_190, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_74, c_156])).
% 20.72/10.46  tff(c_167, plain, (![B_190]: (r3_orders_2('#skF_6', B_190, '#skF_7') | ~r1_orders_2('#skF_6', B_190, '#skF_7') | ~m1_subset_1(B_190, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_97, c_162])).
% 20.72/10.46  tff(c_168, plain, (v2_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_167])).
% 20.72/10.46  tff(c_12, plain, (![A_11]: (~v2_struct_0(A_11) | ~v1_lattice3(A_11) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 20.72/10.46  tff(c_171, plain, (~v1_lattice3('#skF_6') | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_168, c_12])).
% 20.72/10.46  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_82, c_171])).
% 20.72/10.46  tff(c_177, plain, (~v2_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_167])).
% 20.72/10.46  tff(c_806, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_796])).
% 20.72/10.46  tff(c_791, plain, (![B_74, D_86]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_74), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_74)), D_86) | ~r3_waybel_9('#skF_6', B_74, D_86) | ~v10_waybel_0(B_74, '#skF_6') | ~m1_subset_1(D_86, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_74, '#skF_6') | ~v7_waybel_0(B_74) | ~v4_orders_2(B_74) | v2_struct_0(B_74))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_788])).
% 20.72/10.46  tff(c_32, plain, (![A_24, B_38, C_45]: (r2_lattice3(A_24, B_38, '#skF_2'(A_24, B_38, C_45)) | r1_yellow_0(A_24, B_38) | ~r2_lattice3(A_24, B_38, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_24)) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 20.72/10.46  tff(c_818, plain, (![A_358, B_359, D_360, E_361]: (m1_subset_1('#skF_5'(A_358, B_359, D_360, D_360), u1_struct_0(A_358)) | r3_orders_2(A_358, D_360, E_361) | ~r2_lattice3(A_358, k2_relset_1(u1_struct_0(B_359), u1_struct_0(A_358), u1_waybel_0(A_358, B_359)), E_361) | ~m1_subset_1(E_361, u1_struct_0(A_358)) | ~r3_waybel_9(A_358, B_359, D_360) | ~m1_subset_1(D_360, u1_struct_0(A_358)) | ~l1_waybel_0(B_359, A_358) | ~v7_waybel_0(B_359) | ~v4_orders_2(B_359) | v2_struct_0(B_359) | ~l1_waybel_9(A_358) | ~v1_compts_1(A_358) | ~v2_lattice3(A_358) | ~v1_lattice3(A_358) | ~v5_orders_2(A_358) | ~v4_orders_2(A_358) | ~v3_orders_2(A_358) | ~v8_pre_topc(A_358) | ~v2_pre_topc(A_358))), inference(cnfTransformation, [status(thm)], [f_229])).
% 20.72/10.46  tff(c_1394, plain, (![A_463, B_464, D_465, C_466]: (m1_subset_1('#skF_5'(A_463, B_464, D_465, D_465), u1_struct_0(A_463)) | r3_orders_2(A_463, D_465, '#skF_2'(A_463, k2_relset_1(u1_struct_0(B_464), u1_struct_0(A_463), u1_waybel_0(A_463, B_464)), C_466)) | ~m1_subset_1('#skF_2'(A_463, k2_relset_1(u1_struct_0(B_464), u1_struct_0(A_463), u1_waybel_0(A_463, B_464)), C_466), u1_struct_0(A_463)) | ~r3_waybel_9(A_463, B_464, D_465) | ~m1_subset_1(D_465, u1_struct_0(A_463)) | ~l1_waybel_0(B_464, A_463) | ~v7_waybel_0(B_464) | ~v4_orders_2(B_464) | v2_struct_0(B_464) | ~l1_waybel_9(A_463) | ~v1_compts_1(A_463) | ~v2_lattice3(A_463) | ~v1_lattice3(A_463) | ~v4_orders_2(A_463) | ~v3_orders_2(A_463) | ~v8_pre_topc(A_463) | ~v2_pre_topc(A_463) | r1_yellow_0(A_463, k2_relset_1(u1_struct_0(B_464), u1_struct_0(A_463), u1_waybel_0(A_463, B_464))) | ~r2_lattice3(A_463, k2_relset_1(u1_struct_0(B_464), u1_struct_0(A_463), u1_waybel_0(A_463, B_464)), C_466) | ~m1_subset_1(C_466, u1_struct_0(A_463)) | ~l1_orders_2(A_463) | ~v5_orders_2(A_463))), inference(resolution, [status(thm)], [c_32, c_818])).
% 20.72/10.47  tff(c_2600, plain, (![A_671, B_672, D_673, C_674]: (m1_subset_1('#skF_5'(A_671, B_672, D_673, D_673), u1_struct_0(A_671)) | r3_orders_2(A_671, D_673, '#skF_2'(A_671, k2_relset_1(u1_struct_0(B_672), u1_struct_0(A_671), u1_waybel_0(A_671, B_672)), C_674)) | ~r3_waybel_9(A_671, B_672, D_673) | ~m1_subset_1(D_673, u1_struct_0(A_671)) | ~l1_waybel_0(B_672, A_671) | ~v7_waybel_0(B_672) | ~v4_orders_2(B_672) | v2_struct_0(B_672) | ~l1_waybel_9(A_671) | ~v1_compts_1(A_671) | ~v2_lattice3(A_671) | ~v1_lattice3(A_671) | ~v4_orders_2(A_671) | ~v3_orders_2(A_671) | ~v8_pre_topc(A_671) | ~v2_pre_topc(A_671) | r1_yellow_0(A_671, k2_relset_1(u1_struct_0(B_672), u1_struct_0(A_671), u1_waybel_0(A_671, B_672))) | ~r2_lattice3(A_671, k2_relset_1(u1_struct_0(B_672), u1_struct_0(A_671), u1_waybel_0(A_671, B_672)), C_674) | ~m1_subset_1(C_674, u1_struct_0(A_671)) | ~l1_orders_2(A_671) | ~v5_orders_2(A_671))), inference(resolution, [status(thm)], [c_34, c_1394])).
% 20.72/10.47  tff(c_6491, plain, (![A_1131, B_1132, D_1133, C_1134]: (m1_subset_1('#skF_5'(A_1131, B_1132, D_1133, D_1133), u1_struct_0(A_1131)) | r3_orders_2(A_1131, D_1133, '#skF_2'(A_1131, k2_relat_1(u1_waybel_0(A_1131, B_1132)), C_1134)) | ~r3_waybel_9(A_1131, B_1132, D_1133) | ~m1_subset_1(D_1133, u1_struct_0(A_1131)) | ~l1_waybel_0(B_1132, A_1131) | ~v7_waybel_0(B_1132) | ~v4_orders_2(B_1132) | v2_struct_0(B_1132) | ~l1_waybel_9(A_1131) | ~v1_compts_1(A_1131) | ~v2_lattice3(A_1131) | ~v1_lattice3(A_1131) | ~v4_orders_2(A_1131) | ~v3_orders_2(A_1131) | ~v8_pre_topc(A_1131) | ~v2_pre_topc(A_1131) | r1_yellow_0(A_1131, k2_relset_1(u1_struct_0(B_1132), u1_struct_0(A_1131), u1_waybel_0(A_1131, B_1132))) | ~r2_lattice3(A_1131, k2_relset_1(u1_struct_0(B_1132), u1_struct_0(A_1131), u1_waybel_0(A_1131, B_1132)), C_1134) | ~m1_subset_1(C_1134, u1_struct_0(A_1131)) | ~l1_orders_2(A_1131) | ~v5_orders_2(A_1131) | ~l1_waybel_0(B_1132, A_1131) | ~l1_struct_0(A_1131))), inference(superposition, [status(thm), theory('equality')], [c_128, c_2600])).
% 20.72/10.47  tff(c_6503, plain, (![B_74, D_1133, D_86]: (m1_subset_1('#skF_5'('#skF_6', B_74, D_1133, D_1133), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1133, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_74)), D_86)) | ~r3_waybel_9('#skF_6', B_74, D_1133) | ~m1_subset_1(D_1133, u1_struct_0('#skF_6')) | ~l1_waybel_9('#skF_6') | ~v1_compts_1('#skF_6') | ~v2_lattice3('#skF_6') | ~v1_lattice3('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | ~v8_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_74), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_74))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', B_74, D_86) | ~v10_waybel_0(B_74, '#skF_6') | ~m1_subset_1(D_86, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_74, '#skF_6') | ~v7_waybel_0(B_74) | ~v4_orders_2(B_74) | v2_struct_0(B_74))), inference(resolution, [status(thm)], [c_791, c_6491])).
% 20.72/10.47  tff(c_6537, plain, (![B_1135, D_1136, D_1137]: (m1_subset_1('#skF_5'('#skF_6', B_1135, D_1136, D_1136), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1136, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1135)), D_1137)) | ~r3_waybel_9('#skF_6', B_1135, D_1136) | ~m1_subset_1(D_1136, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_1135), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1135))) | ~r3_waybel_9('#skF_6', B_1135, D_1137) | ~v10_waybel_0(B_1135, '#skF_6') | ~m1_subset_1(D_1137, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_1135, '#skF_6') | ~v7_waybel_0(B_1135) | ~v4_orders_2(B_1135) | v2_struct_0(B_1135))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_84, c_97, c_92, c_90, c_88, c_86, c_82, c_80, c_78, c_76, c_6503])).
% 20.72/10.47  tff(c_6583, plain, (![B_168, D_1136, D_1137]: (m1_subset_1('#skF_5'('#skF_6', B_168, D_1136, D_1136), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1136, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168)), D_1137)) | ~r3_waybel_9('#skF_6', B_168, D_1136) | ~m1_subset_1(D_1136, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168))) | ~r3_waybel_9('#skF_6', B_168, D_1137) | ~v10_waybel_0(B_168, '#skF_6') | ~m1_subset_1(D_1137, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_168, '#skF_6') | ~v7_waybel_0(B_168) | ~v4_orders_2(B_168) | v2_struct_0(B_168) | ~l1_waybel_0(B_168, '#skF_6') | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_6537])).
% 20.72/10.47  tff(c_6618, plain, (![B_1138, D_1139, D_1140]: (m1_subset_1('#skF_5'('#skF_6', B_1138, D_1139, D_1139), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1139, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1138)), D_1140)) | ~r3_waybel_9('#skF_6', B_1138, D_1139) | ~m1_subset_1(D_1139, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1138))) | ~r3_waybel_9('#skF_6', B_1138, D_1140) | ~v10_waybel_0(B_1138, '#skF_6') | ~m1_subset_1(D_1140, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1138) | ~v4_orders_2(B_1138) | v2_struct_0(B_1138) | ~l1_waybel_0(B_1138, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_6583])).
% 20.72/10.47  tff(c_10, plain, (![A_8, B_9, C_10]: (r1_orders_2(A_8, B_9, C_10) | ~r3_orders_2(A_8, B_9, C_10) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 20.72/10.47  tff(c_6646, plain, (![D_1139, B_1138, D_1140]: (r1_orders_2('#skF_6', D_1139, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1138)), D_1140)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1138)), D_1140), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6') | m1_subset_1('#skF_5'('#skF_6', B_1138, D_1139, D_1139), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_1138, D_1139) | ~m1_subset_1(D_1139, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1138))) | ~r3_waybel_9('#skF_6', B_1138, D_1140) | ~v10_waybel_0(B_1138, '#skF_6') | ~m1_subset_1(D_1140, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1138) | ~v4_orders_2(B_1138) | v2_struct_0(B_1138) | ~l1_waybel_0(B_1138, '#skF_6'))), inference(resolution, [status(thm)], [c_6618, c_10])).
% 20.72/10.47  tff(c_6664, plain, (![D_1139, B_1138, D_1140]: (r1_orders_2('#skF_6', D_1139, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1138)), D_1140)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1138)), D_1140), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | m1_subset_1('#skF_5'('#skF_6', B_1138, D_1139, D_1139), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_1138, D_1139) | ~m1_subset_1(D_1139, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1138))) | ~r3_waybel_9('#skF_6', B_1138, D_1140) | ~v10_waybel_0(B_1138, '#skF_6') | ~m1_subset_1(D_1140, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1138) | ~v4_orders_2(B_1138) | v2_struct_0(B_1138) | ~l1_waybel_0(B_1138, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_97, c_6646])).
% 20.72/10.47  tff(c_6681, plain, (![D_1152, B_1153, D_1154]: (r1_orders_2('#skF_6', D_1152, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1153)), D_1154)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1153)), D_1154), u1_struct_0('#skF_6')) | m1_subset_1('#skF_5'('#skF_6', B_1153, D_1152, D_1152), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_1153, D_1152) | ~m1_subset_1(D_1152, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1153))) | ~r3_waybel_9('#skF_6', B_1153, D_1154) | ~v10_waybel_0(B_1153, '#skF_6') | ~m1_subset_1(D_1154, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1153) | ~v4_orders_2(B_1153) | v2_struct_0(B_1153) | ~l1_waybel_0(B_1153, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_177, c_6664])).
% 20.72/10.47  tff(c_6684, plain, (![D_1152, B_1153, C_45]: (r1_orders_2('#skF_6', D_1152, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1153)), C_45)) | m1_subset_1('#skF_5'('#skF_6', B_1153, D_1152, D_1152), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_1153, D_1152) | ~m1_subset_1(D_1152, u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_1153, C_45) | ~v10_waybel_0(B_1153, '#skF_6') | ~v7_waybel_0(B_1153) | ~v4_orders_2(B_1153) | v2_struct_0(B_1153) | ~l1_waybel_0(B_1153, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1153))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1153)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_6681])).
% 20.72/10.47  tff(c_6688, plain, (![D_1155, B_1156, C_1157]: (r1_orders_2('#skF_6', D_1155, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1156)), C_1157)) | m1_subset_1('#skF_5'('#skF_6', B_1156, D_1155, D_1155), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_1156, D_1155) | ~m1_subset_1(D_1155, u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_1156, C_1157) | ~v10_waybel_0(B_1156, '#skF_6') | ~v7_waybel_0(B_1156) | ~v4_orders_2(B_1156) | v2_struct_0(B_1156) | ~l1_waybel_0(B_1156, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1156))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1156)), C_1157) | ~m1_subset_1(C_1157, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_6684])).
% 20.72/10.47  tff(c_30, plain, (![A_24, C_45, B_38]: (~r1_orders_2(A_24, C_45, '#skF_2'(A_24, B_38, C_45)) | r1_yellow_0(A_24, B_38) | ~r2_lattice3(A_24, B_38, C_45) | ~m1_subset_1(C_45, u1_struct_0(A_24)) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 20.72/10.47  tff(c_6692, plain, (![B_1156, C_1157]: (~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | m1_subset_1('#skF_5'('#skF_6', B_1156, C_1157, C_1157), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_1156, C_1157) | ~v10_waybel_0(B_1156, '#skF_6') | ~v7_waybel_0(B_1156) | ~v4_orders_2(B_1156) | v2_struct_0(B_1156) | ~l1_waybel_0(B_1156, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1156))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1156)), C_1157) | ~m1_subset_1(C_1157, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_6688, c_30])).
% 20.72/10.47  tff(c_6737, plain, (![B_1158, C_1159]: (m1_subset_1('#skF_5'('#skF_6', B_1158, C_1159, C_1159), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_1158, C_1159) | ~v10_waybel_0(B_1158, '#skF_6') | ~v7_waybel_0(B_1158) | ~v4_orders_2(B_1158) | v2_struct_0(B_1158) | ~l1_waybel_0(B_1158, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1158))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1158)), C_1159) | ~m1_subset_1(C_1159, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_6692])).
% 20.72/10.47  tff(c_6817, plain, (![B_1160, D_1161]: (m1_subset_1('#skF_5'('#skF_6', B_1160, D_1161, D_1161), u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1160))) | ~r3_waybel_9('#skF_6', B_1160, D_1161) | ~v10_waybel_0(B_1160, '#skF_6') | ~m1_subset_1(D_1161, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1160) | ~v4_orders_2(B_1160) | v2_struct_0(B_1160) | ~l1_waybel_0(B_1160, '#skF_6'))), inference(resolution, [status(thm)], [c_805, c_6737])).
% 20.72/10.47  tff(c_916, plain, (![A_379, B_380, D_381, E_382]: (~v5_pre_topc(k4_waybel_1(A_379, '#skF_5'(A_379, B_380, D_381, D_381)), A_379, A_379) | r3_orders_2(A_379, D_381, E_382) | ~r2_lattice3(A_379, k2_relset_1(u1_struct_0(B_380), u1_struct_0(A_379), u1_waybel_0(A_379, B_380)), E_382) | ~m1_subset_1(E_382, u1_struct_0(A_379)) | ~r3_waybel_9(A_379, B_380, D_381) | ~m1_subset_1(D_381, u1_struct_0(A_379)) | ~l1_waybel_0(B_380, A_379) | ~v7_waybel_0(B_380) | ~v4_orders_2(B_380) | v2_struct_0(B_380) | ~l1_waybel_9(A_379) | ~v1_compts_1(A_379) | ~v2_lattice3(A_379) | ~v1_lattice3(A_379) | ~v5_orders_2(A_379) | ~v4_orders_2(A_379) | ~v3_orders_2(A_379) | ~v8_pre_topc(A_379) | ~v2_pre_topc(A_379))), inference(cnfTransformation, [status(thm)], [f_229])).
% 20.72/10.47  tff(c_919, plain, (![D_381, E_382, B_380]: (r3_orders_2('#skF_6', D_381, E_382) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_380), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_380)), E_382) | ~m1_subset_1(E_382, u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_380, D_381) | ~m1_subset_1(D_381, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_380, '#skF_6') | ~v7_waybel_0(B_380) | ~v4_orders_2(B_380) | v2_struct_0(B_380) | ~l1_waybel_9('#skF_6') | ~v1_compts_1('#skF_6') | ~v2_lattice3('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | ~v8_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | ~m1_subset_1('#skF_5'('#skF_6', B_380, D_381, D_381), u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_64, c_916])).
% 20.72/10.47  tff(c_951, plain, (![D_389, E_390, B_391]: (r3_orders_2('#skF_6', D_389, E_390) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391)), E_390) | ~m1_subset_1(E_390, u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_391, D_389) | ~m1_subset_1(D_389, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_391, '#skF_6') | ~v7_waybel_0(B_391) | ~v4_orders_2(B_391) | v2_struct_0(B_391) | ~m1_subset_1('#skF_5'('#skF_6', B_391, D_389, D_389), u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_919])).
% 20.72/10.47  tff(c_965, plain, (![D_389, E_390, B_168]: (r3_orders_2('#skF_6', D_389, E_390) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168)), E_390) | ~m1_subset_1(E_390, u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_168, D_389) | ~m1_subset_1(D_389, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_168, '#skF_6') | ~v7_waybel_0(B_168) | ~v4_orders_2(B_168) | v2_struct_0(B_168) | ~m1_subset_1('#skF_5'('#skF_6', B_168, D_389, D_389), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_168, '#skF_6') | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_951])).
% 20.72/10.47  tff(c_1107, plain, (![D_409, E_410, B_411]: (r3_orders_2('#skF_6', D_409, E_410) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_411)), E_410) | ~m1_subset_1(E_410, u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_411, D_409) | ~m1_subset_1(D_409, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_411) | ~v4_orders_2(B_411) | v2_struct_0(B_411) | ~m1_subset_1('#skF_5'('#skF_6', B_411, D_409, D_409), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_411, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_965])).
% 20.72/10.47  tff(c_1121, plain, (![D_409, B_411, C_45]: (r3_orders_2('#skF_6', D_409, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_411)), C_45)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_411)), C_45), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_411, D_409) | ~m1_subset_1(D_409, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_411) | ~v4_orders_2(B_411) | v2_struct_0(B_411) | ~m1_subset_1('#skF_5'('#skF_6', B_411, D_409, D_409), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_411, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_411))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_411)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_1107])).
% 20.72/10.47  tff(c_1539, plain, (![D_502, B_503, C_504]: (r3_orders_2('#skF_6', D_502, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503)), C_504)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503)), C_504), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_503, D_502) | ~m1_subset_1(D_502, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_503) | ~v4_orders_2(B_503) | v2_struct_0(B_503) | ~m1_subset_1('#skF_5'('#skF_6', B_503, D_502, D_502), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_503, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503)), C_504) | ~m1_subset_1(C_504, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_1121])).
% 20.72/10.47  tff(c_1542, plain, (![D_502, B_503, C_45]: (r3_orders_2('#skF_6', D_502, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503)), C_45)) | ~r3_waybel_9('#skF_6', B_503, D_502) | ~m1_subset_1(D_502, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_503) | ~v4_orders_2(B_503) | v2_struct_0(B_503) | ~m1_subset_1('#skF_5'('#skF_6', B_503, D_502, D_502), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_503, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1539])).
% 20.72/10.47  tff(c_1545, plain, (![D_502, B_503, C_45]: (r3_orders_2('#skF_6', D_502, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503)), C_45)) | ~r3_waybel_9('#skF_6', B_503, D_502) | ~m1_subset_1(D_502, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_503) | ~v4_orders_2(B_503) | v2_struct_0(B_503) | ~m1_subset_1('#skF_5'('#skF_6', B_503, D_502, D_502), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_503, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_503)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_1542])).
% 20.72/10.47  tff(c_7054, plain, (![D_1179, B_1180, C_1181]: (r3_orders_2('#skF_6', D_1179, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180)), C_1181)) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180)), C_1181) | ~m1_subset_1(C_1181, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180))) | ~r3_waybel_9('#skF_6', B_1180, D_1179) | ~v10_waybel_0(B_1180, '#skF_6') | ~m1_subset_1(D_1179, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1180) | ~v4_orders_2(B_1180) | v2_struct_0(B_1180) | ~l1_waybel_0(B_1180, '#skF_6'))), inference(resolution, [status(thm)], [c_6817, c_1545])).
% 20.72/10.47  tff(c_7056, plain, (![D_1179, B_1180, C_1181]: (r1_orders_2('#skF_6', D_1179, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180)), C_1181)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180)), C_1181), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180)), C_1181) | ~m1_subset_1(C_1181, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180))) | ~r3_waybel_9('#skF_6', B_1180, D_1179) | ~v10_waybel_0(B_1180, '#skF_6') | ~m1_subset_1(D_1179, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1180) | ~v4_orders_2(B_1180) | v2_struct_0(B_1180) | ~l1_waybel_0(B_1180, '#skF_6'))), inference(resolution, [status(thm)], [c_7054, c_10])).
% 20.72/10.47  tff(c_7059, plain, (![D_1179, B_1180, C_1181]: (r1_orders_2('#skF_6', D_1179, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180)), C_1181)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180)), C_1181), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180)), C_1181) | ~m1_subset_1(C_1181, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1180))) | ~r3_waybel_9('#skF_6', B_1180, D_1179) | ~v10_waybel_0(B_1180, '#skF_6') | ~m1_subset_1(D_1179, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1180) | ~v4_orders_2(B_1180) | v2_struct_0(B_1180) | ~l1_waybel_0(B_1180, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_97, c_7056])).
% 20.72/10.47  tff(c_7404, plain, (![D_1208, B_1209, C_1210]: (r1_orders_2('#skF_6', D_1208, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1209)), C_1210)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1209)), C_1210), u1_struct_0('#skF_6')) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1209)), C_1210) | ~m1_subset_1(C_1210, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1209))) | ~r3_waybel_9('#skF_6', B_1209, D_1208) | ~v10_waybel_0(B_1209, '#skF_6') | ~m1_subset_1(D_1208, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1209) | ~v4_orders_2(B_1209) | v2_struct_0(B_1209) | ~l1_waybel_0(B_1209, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_177, c_7059])).
% 20.72/10.47  tff(c_7407, plain, (![D_1208, B_1209, C_45]: (r1_orders_2('#skF_6', D_1208, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1209)), C_45)) | ~r3_waybel_9('#skF_6', B_1209, D_1208) | ~v10_waybel_0(B_1209, '#skF_6') | ~m1_subset_1(D_1208, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1209) | ~v4_orders_2(B_1209) | v2_struct_0(B_1209) | ~l1_waybel_0(B_1209, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1209))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1209)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_7404])).
% 20.72/10.47  tff(c_7411, plain, (![D_1211, B_1212, C_1213]: (r1_orders_2('#skF_6', D_1211, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1212)), C_1213)) | ~r3_waybel_9('#skF_6', B_1212, D_1211) | ~v10_waybel_0(B_1212, '#skF_6') | ~m1_subset_1(D_1211, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1212) | ~v4_orders_2(B_1212) | v2_struct_0(B_1212) | ~l1_waybel_0(B_1212, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1212))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1212)), C_1213) | ~m1_subset_1(C_1213, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_7407])).
% 20.72/10.47  tff(c_7415, plain, (![B_1212, C_1213]: (~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~r3_waybel_9('#skF_6', B_1212, C_1213) | ~v10_waybel_0(B_1212, '#skF_6') | ~v7_waybel_0(B_1212) | ~v4_orders_2(B_1212) | v2_struct_0(B_1212) | ~l1_waybel_0(B_1212, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1212))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1212)), C_1213) | ~m1_subset_1(C_1213, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_7411, c_30])).
% 20.72/10.47  tff(c_7419, plain, (![B_1214, C_1215]: (~r3_waybel_9('#skF_6', B_1214, C_1215) | ~v10_waybel_0(B_1214, '#skF_6') | ~v7_waybel_0(B_1214) | ~v4_orders_2(B_1214) | v2_struct_0(B_1214) | ~l1_waybel_0(B_1214, '#skF_6') | r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1214))) | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1214)), C_1215) | ~m1_subset_1(C_1215, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_7415])).
% 20.72/10.47  tff(c_7516, plain, (![B_1216, D_1217]: (r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1216))) | ~r3_waybel_9('#skF_6', B_1216, D_1217) | ~v10_waybel_0(B_1216, '#skF_6') | ~m1_subset_1(D_1217, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1216) | ~v4_orders_2(B_1216) | v2_struct_0(B_1216) | ~l1_waybel_0(B_1216, '#skF_6'))), inference(resolution, [status(thm)], [c_805, c_7419])).
% 20.72/10.47  tff(c_7518, plain, (r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~v10_waybel_0('#skF_8', '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_7516])).
% 20.72/10.47  tff(c_7521, plain, (r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_74, c_62, c_7518])).
% 20.72/10.47  tff(c_7522, plain, (r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_72, c_7521])).
% 20.72/10.47  tff(c_42, plain, (![A_51, B_53]: (k4_yellow_2(A_51, u1_waybel_0(A_51, B_53))=k1_waybel_2(A_51, B_53) | ~l1_waybel_0(B_53, A_51) | ~l1_orders_2(A_51) | v2_struct_0(A_51))), inference(cnfTransformation, [status(thm)], [f_116])).
% 20.72/10.47  tff(c_2, plain, (![C_3, A_1, B_2]: (v1_relat_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 20.72/10.47  tff(c_129, plain, (![A_167, B_168]: (v1_relat_1(u1_waybel_0(A_167, B_168)) | ~l1_waybel_0(B_168, A_167) | ~l1_struct_0(A_167))), inference(resolution, [status(thm)], [c_121, c_2])).
% 20.72/10.47  tff(c_28, plain, (![A_24, B_38]: (m1_subset_1('#skF_3'(A_24, B_38), u1_struct_0(A_24)) | ~r1_yellow_0(A_24, B_38) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 20.72/10.47  tff(c_26, plain, (![A_24, B_38]: (r2_lattice3(A_24, B_38, '#skF_3'(A_24, B_38)) | ~r1_yellow_0(A_24, B_38) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 20.72/10.47  tff(c_18, plain, (![A_12, B_19, C_20]: (m1_subset_1('#skF_1'(A_12, B_19, C_20), u1_struct_0(A_12)) | k1_yellow_0(A_12, B_19)=C_20 | ~r2_lattice3(A_12, B_19, C_20) | ~r1_yellow_0(A_12, B_19) | ~m1_subset_1(C_20, u1_struct_0(A_12)) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.72/10.47  tff(c_16, plain, (![A_12, B_19, C_20]: (r2_lattice3(A_12, B_19, '#skF_1'(A_12, B_19, C_20)) | k1_yellow_0(A_12, B_19)=C_20 | ~r2_lattice3(A_12, B_19, C_20) | ~r1_yellow_0(A_12, B_19) | ~m1_subset_1(C_20, u1_struct_0(A_12)) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.72/10.47  tff(c_24, plain, (![A_24, B_38, D_48]: (r1_orders_2(A_24, '#skF_3'(A_24, B_38), D_48) | ~r2_lattice3(A_24, B_38, D_48) | ~m1_subset_1(D_48, u1_struct_0(A_24)) | ~r1_yellow_0(A_24, B_38) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_96])).
% 20.72/10.47  tff(c_659, plain, (![A_305, C_306, B_307]: (~r1_orders_2(A_305, C_306, '#skF_1'(A_305, B_307, C_306)) | k1_yellow_0(A_305, B_307)=C_306 | ~r2_lattice3(A_305, B_307, C_306) | ~r1_yellow_0(A_305, B_307) | ~m1_subset_1(C_306, u1_struct_0(A_305)) | ~l1_orders_2(A_305))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.72/10.47  tff(c_898, plain, (![A_376, B_377, B_378]: (k1_yellow_0(A_376, B_377)='#skF_3'(A_376, B_378) | ~r2_lattice3(A_376, B_377, '#skF_3'(A_376, B_378)) | ~r1_yellow_0(A_376, B_377) | ~m1_subset_1('#skF_3'(A_376, B_378), u1_struct_0(A_376)) | ~r2_lattice3(A_376, B_378, '#skF_1'(A_376, B_377, '#skF_3'(A_376, B_378))) | ~m1_subset_1('#skF_1'(A_376, B_377, '#skF_3'(A_376, B_378)), u1_struct_0(A_376)) | ~r1_yellow_0(A_376, B_378) | ~l1_orders_2(A_376) | ~v5_orders_2(A_376))), inference(resolution, [status(thm)], [c_24, c_659])).
% 20.72/10.47  tff(c_923, plain, (![A_383, B_384]: (~m1_subset_1('#skF_1'(A_383, B_384, '#skF_3'(A_383, B_384)), u1_struct_0(A_383)) | ~v5_orders_2(A_383) | k1_yellow_0(A_383, B_384)='#skF_3'(A_383, B_384) | ~r2_lattice3(A_383, B_384, '#skF_3'(A_383, B_384)) | ~r1_yellow_0(A_383, B_384) | ~m1_subset_1('#skF_3'(A_383, B_384), u1_struct_0(A_383)) | ~l1_orders_2(A_383))), inference(resolution, [status(thm)], [c_16, c_898])).
% 20.72/10.47  tff(c_929, plain, (![A_385, B_386]: (~v5_orders_2(A_385) | k1_yellow_0(A_385, B_386)='#skF_3'(A_385, B_386) | ~r2_lattice3(A_385, B_386, '#skF_3'(A_385, B_386)) | ~r1_yellow_0(A_385, B_386) | ~m1_subset_1('#skF_3'(A_385, B_386), u1_struct_0(A_385)) | ~l1_orders_2(A_385))), inference(resolution, [status(thm)], [c_18, c_923])).
% 20.72/10.47  tff(c_946, plain, (![A_387, B_388]: (k1_yellow_0(A_387, B_388)='#skF_3'(A_387, B_388) | ~m1_subset_1('#skF_3'(A_387, B_388), u1_struct_0(A_387)) | ~r1_yellow_0(A_387, B_388) | ~l1_orders_2(A_387) | ~v5_orders_2(A_387))), inference(resolution, [status(thm)], [c_26, c_929])).
% 20.72/10.47  tff(c_950, plain, (![A_24, B_38]: (k1_yellow_0(A_24, B_38)='#skF_3'(A_24, B_38) | ~r1_yellow_0(A_24, B_38) | ~l1_orders_2(A_24) | ~v5_orders_2(A_24))), inference(resolution, [status(thm)], [c_28, c_946])).
% 20.72/10.47  tff(c_7560, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))='#skF_3'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_7522, c_950])).
% 20.72/10.47  tff(c_7631, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))='#skF_3'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_7560])).
% 20.72/10.47  tff(c_44, plain, (![A_54, B_56]: (k1_yellow_0(A_54, k2_relat_1(B_56))=k4_yellow_2(A_54, B_56) | ~v1_relat_1(B_56) | ~l1_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_126])).
% 20.72/10.47  tff(c_7725, plain, ('#skF_3'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))=k4_yellow_2('#skF_6', u1_waybel_0('#skF_6', '#skF_8')) | ~v1_relat_1(u1_waybel_0('#skF_6', '#skF_8')) | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7631, c_44])).
% 20.72/10.47  tff(c_7834, plain, ('#skF_3'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))=k4_yellow_2('#skF_6', u1_waybel_0('#skF_6', '#skF_8')) | ~v1_relat_1(u1_waybel_0('#skF_6', '#skF_8')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_7725])).
% 20.72/10.47  tff(c_7835, plain, ('#skF_3'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))=k4_yellow_2('#skF_6', u1_waybel_0('#skF_6', '#skF_8')) | ~v1_relat_1(u1_waybel_0('#skF_6', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_177, c_7834])).
% 20.72/10.47  tff(c_7848, plain, (~v1_relat_1(u1_waybel_0('#skF_6', '#skF_8'))), inference(splitLeft, [status(thm)], [c_7835])).
% 20.72/10.47  tff(c_7851, plain, (~l1_waybel_0('#skF_8', '#skF_6') | ~l1_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_129, c_7848])).
% 20.72/10.47  tff(c_7855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_806, c_66, c_7851])).
% 20.72/10.47  tff(c_7856, plain, ('#skF_3'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))=k4_yellow_2('#skF_6', u1_waybel_0('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_7835])).
% 20.72/10.47  tff(c_7990, plain, (m1_subset_1(k4_yellow_2('#skF_6', u1_waybel_0('#skF_6', '#skF_8')), u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7856, c_28])).
% 20.72/10.47  tff(c_8137, plain, (m1_subset_1(k4_yellow_2('#skF_6', u1_waybel_0('#skF_6', '#skF_8')), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_7522, c_7990])).
% 20.72/10.47  tff(c_8182, plain, (m1_subset_1(k1_waybel_2('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_8', '#skF_6') | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_42, c_8137])).
% 20.72/10.47  tff(c_8238, plain, (m1_subset_1(k1_waybel_2('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_66, c_8182])).
% 20.72/10.47  tff(c_8239, plain, (m1_subset_1(k1_waybel_2('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_177, c_8238])).
% 20.72/10.47  tff(c_7858, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))=k4_yellow_2('#skF_6', u1_waybel_0('#skF_6', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_7856, c_7631])).
% 20.72/10.47  tff(c_7857, plain, (v1_relat_1(u1_waybel_0('#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_7835])).
% 20.72/10.47  tff(c_140, plain, (![A_173, B_174]: (r2_lattice3(A_173, B_174, k1_yellow_0(A_173, B_174)) | ~r1_yellow_0(A_173, B_174) | ~m1_subset_1(k1_yellow_0(A_173, B_174), u1_struct_0(A_173)) | ~l1_orders_2(A_173))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.72/10.47  tff(c_675, plain, (![A_313, B_314]: (r2_lattice3(A_313, k2_relat_1(B_314), k1_yellow_0(A_313, k2_relat_1(B_314))) | ~r1_yellow_0(A_313, k2_relat_1(B_314)) | ~m1_subset_1(k4_yellow_2(A_313, B_314), u1_struct_0(A_313)) | ~l1_orders_2(A_313) | ~v1_relat_1(B_314) | ~l1_orders_2(A_313) | v2_struct_0(A_313))), inference(superposition, [status(thm), theory('equality')], [c_44, c_140])).
% 20.72/10.47  tff(c_704, plain, (![A_323, B_324]: (r2_lattice3(A_323, k2_relat_1(B_324), k4_yellow_2(A_323, B_324)) | ~r1_yellow_0(A_323, k2_relat_1(B_324)) | ~m1_subset_1(k4_yellow_2(A_323, B_324), u1_struct_0(A_323)) | ~l1_orders_2(A_323) | ~v1_relat_1(B_324) | ~l1_orders_2(A_323) | v2_struct_0(A_323) | ~v1_relat_1(B_324) | ~l1_orders_2(A_323) | v2_struct_0(A_323))), inference(superposition, [status(thm), theory('equality')], [c_44, c_675])).
% 20.72/10.47  tff(c_707, plain, (![A_51, B_53]: (r2_lattice3(A_51, k2_relat_1(u1_waybel_0(A_51, B_53)), k1_waybel_2(A_51, B_53)) | ~r1_yellow_0(A_51, k2_relat_1(u1_waybel_0(A_51, B_53))) | ~m1_subset_1(k4_yellow_2(A_51, u1_waybel_0(A_51, B_53)), u1_struct_0(A_51)) | ~l1_orders_2(A_51) | ~v1_relat_1(u1_waybel_0(A_51, B_53)) | ~l1_orders_2(A_51) | v2_struct_0(A_51) | ~v1_relat_1(u1_waybel_0(A_51, B_53)) | ~l1_orders_2(A_51) | v2_struct_0(A_51) | ~l1_waybel_0(B_53, A_51) | ~l1_orders_2(A_51) | v2_struct_0(A_51))), inference(superposition, [status(thm), theory('equality')], [c_42, c_704])).
% 20.72/10.47  tff(c_665, plain, (![A_308, B_309, D_310]: (r1_orders_2(A_308, k1_yellow_0(A_308, B_309), D_310) | ~r2_lattice3(A_308, B_309, D_310) | ~m1_subset_1(D_310, u1_struct_0(A_308)) | ~r1_yellow_0(A_308, B_309) | ~m1_subset_1(k1_yellow_0(A_308, B_309), u1_struct_0(A_308)) | ~l1_orders_2(A_308))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.72/10.47  tff(c_719, plain, (![A_327, B_328, D_329]: (r1_orders_2(A_327, k1_yellow_0(A_327, k2_relat_1(B_328)), D_329) | ~r2_lattice3(A_327, k2_relat_1(B_328), D_329) | ~m1_subset_1(D_329, u1_struct_0(A_327)) | ~r1_yellow_0(A_327, k2_relat_1(B_328)) | ~m1_subset_1(k4_yellow_2(A_327, B_328), u1_struct_0(A_327)) | ~l1_orders_2(A_327) | ~v1_relat_1(B_328) | ~l1_orders_2(A_327) | v2_struct_0(A_327))), inference(superposition, [status(thm), theory('equality')], [c_44, c_665])).
% 20.72/10.47  tff(c_741, plain, (![A_338, B_339, D_340]: (r1_orders_2(A_338, k4_yellow_2(A_338, B_339), D_340) | ~r2_lattice3(A_338, k2_relat_1(B_339), D_340) | ~m1_subset_1(D_340, u1_struct_0(A_338)) | ~r1_yellow_0(A_338, k2_relat_1(B_339)) | ~m1_subset_1(k4_yellow_2(A_338, B_339), u1_struct_0(A_338)) | ~l1_orders_2(A_338) | ~v1_relat_1(B_339) | ~l1_orders_2(A_338) | v2_struct_0(A_338) | ~v1_relat_1(B_339) | ~l1_orders_2(A_338) | v2_struct_0(A_338))), inference(superposition, [status(thm), theory('equality')], [c_44, c_719])).
% 20.72/10.47  tff(c_1192, plain, (![A_422, B_423, C_424]: (r1_orders_2(A_422, k4_yellow_2(A_422, B_423), '#skF_1'(A_422, k2_relat_1(B_423), C_424)) | ~m1_subset_1('#skF_1'(A_422, k2_relat_1(B_423), C_424), u1_struct_0(A_422)) | ~m1_subset_1(k4_yellow_2(A_422, B_423), u1_struct_0(A_422)) | ~v1_relat_1(B_423) | v2_struct_0(A_422) | k1_yellow_0(A_422, k2_relat_1(B_423))=C_424 | ~r2_lattice3(A_422, k2_relat_1(B_423), C_424) | ~r1_yellow_0(A_422, k2_relat_1(B_423)) | ~m1_subset_1(C_424, u1_struct_0(A_422)) | ~l1_orders_2(A_422))), inference(resolution, [status(thm)], [c_16, c_741])).
% 20.72/10.47  tff(c_3547, plain, (![A_790, B_791, C_792]: (r1_orders_2(A_790, k1_waybel_2(A_790, B_791), '#skF_1'(A_790, k2_relat_1(u1_waybel_0(A_790, B_791)), C_792)) | ~m1_subset_1('#skF_1'(A_790, k2_relat_1(u1_waybel_0(A_790, B_791)), C_792), u1_struct_0(A_790)) | ~m1_subset_1(k4_yellow_2(A_790, u1_waybel_0(A_790, B_791)), u1_struct_0(A_790)) | ~v1_relat_1(u1_waybel_0(A_790, B_791)) | v2_struct_0(A_790) | k1_yellow_0(A_790, k2_relat_1(u1_waybel_0(A_790, B_791)))=C_792 | ~r2_lattice3(A_790, k2_relat_1(u1_waybel_0(A_790, B_791)), C_792) | ~r1_yellow_0(A_790, k2_relat_1(u1_waybel_0(A_790, B_791))) | ~m1_subset_1(C_792, u1_struct_0(A_790)) | ~l1_orders_2(A_790) | ~l1_waybel_0(B_791, A_790) | ~l1_orders_2(A_790) | v2_struct_0(A_790))), inference(superposition, [status(thm), theory('equality')], [c_42, c_1192])).
% 20.72/10.47  tff(c_14, plain, (![A_12, C_20, B_19]: (~r1_orders_2(A_12, C_20, '#skF_1'(A_12, B_19, C_20)) | k1_yellow_0(A_12, B_19)=C_20 | ~r2_lattice3(A_12, B_19, C_20) | ~r1_yellow_0(A_12, B_19) | ~m1_subset_1(C_20, u1_struct_0(A_12)) | ~l1_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_77])).
% 20.72/10.47  tff(c_3553, plain, (![A_793, B_794]: (~m1_subset_1('#skF_1'(A_793, k2_relat_1(u1_waybel_0(A_793, B_794)), k1_waybel_2(A_793, B_794)), u1_struct_0(A_793)) | ~m1_subset_1(k4_yellow_2(A_793, u1_waybel_0(A_793, B_794)), u1_struct_0(A_793)) | ~v1_relat_1(u1_waybel_0(A_793, B_794)) | k1_yellow_0(A_793, k2_relat_1(u1_waybel_0(A_793, B_794)))=k1_waybel_2(A_793, B_794) | ~r2_lattice3(A_793, k2_relat_1(u1_waybel_0(A_793, B_794)), k1_waybel_2(A_793, B_794)) | ~r1_yellow_0(A_793, k2_relat_1(u1_waybel_0(A_793, B_794))) | ~m1_subset_1(k1_waybel_2(A_793, B_794), u1_struct_0(A_793)) | ~l1_waybel_0(B_794, A_793) | ~l1_orders_2(A_793) | v2_struct_0(A_793))), inference(resolution, [status(thm)], [c_3547, c_14])).
% 20.72/10.47  tff(c_3578, plain, (![A_798, B_799]: (~m1_subset_1(k4_yellow_2(A_798, u1_waybel_0(A_798, B_799)), u1_struct_0(A_798)) | ~v1_relat_1(u1_waybel_0(A_798, B_799)) | ~l1_waybel_0(B_799, A_798) | v2_struct_0(A_798) | k1_yellow_0(A_798, k2_relat_1(u1_waybel_0(A_798, B_799)))=k1_waybel_2(A_798, B_799) | ~r2_lattice3(A_798, k2_relat_1(u1_waybel_0(A_798, B_799)), k1_waybel_2(A_798, B_799)) | ~r1_yellow_0(A_798, k2_relat_1(u1_waybel_0(A_798, B_799))) | ~m1_subset_1(k1_waybel_2(A_798, B_799), u1_struct_0(A_798)) | ~l1_orders_2(A_798))), inference(resolution, [status(thm)], [c_18, c_3553])).
% 20.72/10.47  tff(c_3592, plain, (![A_51, B_53]: (k1_yellow_0(A_51, k2_relat_1(u1_waybel_0(A_51, B_53)))=k1_waybel_2(A_51, B_53) | ~m1_subset_1(k1_waybel_2(A_51, B_53), u1_struct_0(A_51)) | ~r1_yellow_0(A_51, k2_relat_1(u1_waybel_0(A_51, B_53))) | ~m1_subset_1(k4_yellow_2(A_51, u1_waybel_0(A_51, B_53)), u1_struct_0(A_51)) | ~v1_relat_1(u1_waybel_0(A_51, B_53)) | ~l1_waybel_0(B_53, A_51) | ~l1_orders_2(A_51) | v2_struct_0(A_51))), inference(resolution, [status(thm)], [c_707, c_3578])).
% 20.72/10.47  tff(c_8163, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))=k1_waybel_2('#skF_6', '#skF_8') | ~m1_subset_1(k1_waybel_2('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~v1_relat_1(u1_waybel_0('#skF_6', '#skF_8')) | ~l1_waybel_0('#skF_8', '#skF_6') | ~l1_orders_2('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_8137, c_3592])).
% 20.72/10.47  tff(c_8213, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))=k1_waybel_2('#skF_6', '#skF_8') | ~m1_subset_1(k1_waybel_2('#skF_6', '#skF_8'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_66, c_7857, c_7522, c_8163])).
% 20.72/10.47  tff(c_8214, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))=k1_waybel_2('#skF_6', '#skF_8') | ~m1_subset_1(k1_waybel_2('#skF_6', '#skF_8'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_177, c_8213])).
% 20.72/10.47  tff(c_9693, plain, (k4_yellow_2('#skF_6', u1_waybel_0('#skF_6', '#skF_8'))=k1_waybel_2('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_8239, c_7858, c_8214])).
% 20.72/10.47  tff(c_9700, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))=k1_waybel_2('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_9693, c_7858])).
% 20.72/10.47  tff(c_1501, plain, (![A_488, B_489, D_490, C_491]: (m1_subset_1('#skF_5'(A_488, B_489, D_490, D_490), u1_struct_0(A_488)) | r3_orders_2(A_488, D_490, '#skF_1'(A_488, k2_relset_1(u1_struct_0(B_489), u1_struct_0(A_488), u1_waybel_0(A_488, B_489)), C_491)) | ~m1_subset_1('#skF_1'(A_488, k2_relset_1(u1_struct_0(B_489), u1_struct_0(A_488), u1_waybel_0(A_488, B_489)), C_491), u1_struct_0(A_488)) | ~r3_waybel_9(A_488, B_489, D_490) | ~m1_subset_1(D_490, u1_struct_0(A_488)) | ~l1_waybel_0(B_489, A_488) | ~v7_waybel_0(B_489) | ~v4_orders_2(B_489) | v2_struct_0(B_489) | ~l1_waybel_9(A_488) | ~v1_compts_1(A_488) | ~v2_lattice3(A_488) | ~v1_lattice3(A_488) | ~v5_orders_2(A_488) | ~v4_orders_2(A_488) | ~v3_orders_2(A_488) | ~v8_pre_topc(A_488) | ~v2_pre_topc(A_488) | k1_yellow_0(A_488, k2_relset_1(u1_struct_0(B_489), u1_struct_0(A_488), u1_waybel_0(A_488, B_489)))=C_491 | ~r2_lattice3(A_488, k2_relset_1(u1_struct_0(B_489), u1_struct_0(A_488), u1_waybel_0(A_488, B_489)), C_491) | ~r1_yellow_0(A_488, k2_relset_1(u1_struct_0(B_489), u1_struct_0(A_488), u1_waybel_0(A_488, B_489))) | ~m1_subset_1(C_491, u1_struct_0(A_488)) | ~l1_orders_2(A_488))), inference(resolution, [status(thm)], [c_16, c_818])).
% 20.72/10.47  tff(c_2919, plain, (![A_698, B_699, D_700, C_701]: (m1_subset_1('#skF_5'(A_698, B_699, D_700, D_700), u1_struct_0(A_698)) | r3_orders_2(A_698, D_700, '#skF_1'(A_698, k2_relset_1(u1_struct_0(B_699), u1_struct_0(A_698), u1_waybel_0(A_698, B_699)), C_701)) | ~r3_waybel_9(A_698, B_699, D_700) | ~m1_subset_1(D_700, u1_struct_0(A_698)) | ~l1_waybel_0(B_699, A_698) | ~v7_waybel_0(B_699) | ~v4_orders_2(B_699) | v2_struct_0(B_699) | ~l1_waybel_9(A_698) | ~v1_compts_1(A_698) | ~v2_lattice3(A_698) | ~v1_lattice3(A_698) | ~v5_orders_2(A_698) | ~v4_orders_2(A_698) | ~v3_orders_2(A_698) | ~v8_pre_topc(A_698) | ~v2_pre_topc(A_698) | k1_yellow_0(A_698, k2_relset_1(u1_struct_0(B_699), u1_struct_0(A_698), u1_waybel_0(A_698, B_699)))=C_701 | ~r2_lattice3(A_698, k2_relset_1(u1_struct_0(B_699), u1_struct_0(A_698), u1_waybel_0(A_698, B_699)), C_701) | ~r1_yellow_0(A_698, k2_relset_1(u1_struct_0(B_699), u1_struct_0(A_698), u1_waybel_0(A_698, B_699))) | ~m1_subset_1(C_701, u1_struct_0(A_698)) | ~l1_orders_2(A_698))), inference(resolution, [status(thm)], [c_18, c_1501])).
% 20.72/10.47  tff(c_8625, plain, (![A_1221, B_1222, D_1223, C_1224]: (m1_subset_1('#skF_5'(A_1221, B_1222, D_1223, D_1223), u1_struct_0(A_1221)) | r3_orders_2(A_1221, D_1223, '#skF_1'(A_1221, k2_relat_1(u1_waybel_0(A_1221, B_1222)), C_1224)) | ~r3_waybel_9(A_1221, B_1222, D_1223) | ~m1_subset_1(D_1223, u1_struct_0(A_1221)) | ~l1_waybel_0(B_1222, A_1221) | ~v7_waybel_0(B_1222) | ~v4_orders_2(B_1222) | v2_struct_0(B_1222) | ~l1_waybel_9(A_1221) | ~v1_compts_1(A_1221) | ~v2_lattice3(A_1221) | ~v1_lattice3(A_1221) | ~v5_orders_2(A_1221) | ~v4_orders_2(A_1221) | ~v3_orders_2(A_1221) | ~v8_pre_topc(A_1221) | ~v2_pre_topc(A_1221) | k1_yellow_0(A_1221, k2_relset_1(u1_struct_0(B_1222), u1_struct_0(A_1221), u1_waybel_0(A_1221, B_1222)))=C_1224 | ~r2_lattice3(A_1221, k2_relset_1(u1_struct_0(B_1222), u1_struct_0(A_1221), u1_waybel_0(A_1221, B_1222)), C_1224) | ~r1_yellow_0(A_1221, k2_relset_1(u1_struct_0(B_1222), u1_struct_0(A_1221), u1_waybel_0(A_1221, B_1222))) | ~m1_subset_1(C_1224, u1_struct_0(A_1221)) | ~l1_orders_2(A_1221) | ~l1_waybel_0(B_1222, A_1221) | ~l1_struct_0(A_1221))), inference(superposition, [status(thm), theory('equality')], [c_128, c_2919])).
% 20.72/10.47  tff(c_8637, plain, (![B_74, D_1223, D_86]: (m1_subset_1('#skF_5'('#skF_6', B_74, D_1223, D_1223), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1223, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_74)), D_86)) | ~r3_waybel_9('#skF_6', B_74, D_1223) | ~m1_subset_1(D_1223, u1_struct_0('#skF_6')) | ~l1_waybel_9('#skF_6') | ~v1_compts_1('#skF_6') | ~v2_lattice3('#skF_6') | ~v1_lattice3('#skF_6') | ~v5_orders_2('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | ~v8_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_74), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_74)))=D_86 | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_74), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_74))) | ~l1_orders_2('#skF_6') | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', B_74, D_86) | ~v10_waybel_0(B_74, '#skF_6') | ~m1_subset_1(D_86, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_74, '#skF_6') | ~v7_waybel_0(B_74) | ~v4_orders_2(B_74) | v2_struct_0(B_74))), inference(resolution, [status(thm)], [c_791, c_8625])).
% 20.72/10.47  tff(c_10831, plain, (![B_1258, D_1259, D_1260]: (m1_subset_1('#skF_5'('#skF_6', B_1258, D_1259, D_1259), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1259, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1258)), D_1260)) | ~r3_waybel_9('#skF_6', B_1258, D_1259) | ~m1_subset_1(D_1259, u1_struct_0('#skF_6')) | k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_1258), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1258)))=D_1260 | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_1258), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1258))) | ~r3_waybel_9('#skF_6', B_1258, D_1260) | ~v10_waybel_0(B_1258, '#skF_6') | ~m1_subset_1(D_1260, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_1258, '#skF_6') | ~v7_waybel_0(B_1258) | ~v4_orders_2(B_1258) | v2_struct_0(B_1258))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_97, c_92, c_90, c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_8637])).
% 20.72/10.47  tff(c_10840, plain, (![B_168, D_1259, D_1260]: (m1_subset_1('#skF_5'('#skF_6', B_168, D_1259, D_1259), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1259, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168)), D_1260)) | ~r3_waybel_9('#skF_6', B_168, D_1259) | ~m1_subset_1(D_1259, u1_struct_0('#skF_6')) | k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_168), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_168)))=D_1260 | ~r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168))) | ~r3_waybel_9('#skF_6', B_168, D_1260) | ~v10_waybel_0(B_168, '#skF_6') | ~m1_subset_1(D_1260, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_168, '#skF_6') | ~v7_waybel_0(B_168) | ~v4_orders_2(B_168) | v2_struct_0(B_168) | ~l1_waybel_0(B_168, '#skF_6') | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_10831])).
% 20.72/10.47  tff(c_20755, plain, (![B_168, D_1259]: (m1_subset_1('#skF_5'('#skF_6', B_168, D_1259, D_1259), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1259, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168)), '#skF_7')) | ~r3_waybel_9('#skF_6', B_168, D_1259) | ~m1_subset_1(D_1259, u1_struct_0('#skF_6')) | k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_168), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_168)))='#skF_7' | ~r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168))) | ~r3_waybel_9('#skF_6', B_168, '#skF_7') | ~v10_waybel_0(B_168, '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v7_waybel_0(B_168) | ~v4_orders_2(B_168) | v2_struct_0(B_168) | ~l1_waybel_0(B_168, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_10840])).
% 20.72/10.47  tff(c_962, plain, (![D_389, B_391, C_45]: (r3_orders_2('#skF_6', D_389, '#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391)), C_45)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391)), C_45), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_391, D_389) | ~m1_subset_1(D_389, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_391, '#skF_6') | ~v7_waybel_0(B_391) | ~v4_orders_2(B_391) | v2_struct_0(B_391) | ~m1_subset_1('#skF_5'('#skF_6', B_391, D_389, D_389), u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391))) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_951])).
% 20.72/10.47  tff(c_1962, plain, (![D_576, B_577, C_578]: (r3_orders_2('#skF_6', D_576, '#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577)), C_578)) | ~m1_subset_1('#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577)), C_578), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_577, D_576) | ~m1_subset_1(D_576, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_577, '#skF_6') | ~v7_waybel_0(B_577) | ~v4_orders_2(B_577) | v2_struct_0(B_577) | ~m1_subset_1('#skF_5'('#skF_6', B_577, D_576, D_576), u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577))) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577)), C_578) | ~m1_subset_1(C_578, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_962])).
% 20.72/10.47  tff(c_1965, plain, (![D_576, B_577, C_45]: (r3_orders_2('#skF_6', D_576, '#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577)), C_45)) | ~r3_waybel_9('#skF_6', B_577, D_576) | ~m1_subset_1(D_576, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_577, '#skF_6') | ~v7_waybel_0(B_577) | ~v4_orders_2(B_577) | v2_struct_0(B_577) | ~m1_subset_1('#skF_5'('#skF_6', B_577, D_576, D_576), u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577))) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1962])).
% 20.72/10.47  tff(c_1971, plain, (![D_576, B_577, C_45]: (r3_orders_2('#skF_6', D_576, '#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577)), C_45)) | ~r3_waybel_9('#skF_6', B_577, D_576) | ~m1_subset_1(D_576, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_577, '#skF_6') | ~v7_waybel_0(B_577) | ~v4_orders_2(B_577) | v2_struct_0(B_577) | ~m1_subset_1('#skF_5'('#skF_6', B_577, D_576, D_576), u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577))) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_577), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_577)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_1965])).
% 20.72/10.47  tff(c_2603, plain, (![D_673, B_672, C_45, C_674]: (r3_orders_2('#skF_6', D_673, '#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672)), C_45)) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_673, '#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672)), C_674)) | ~r3_waybel_9('#skF_6', B_672, D_673) | ~m1_subset_1(D_673, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_672, '#skF_6') | ~v7_waybel_0(B_672) | ~v4_orders_2(B_672) | v2_struct_0(B_672) | ~l1_waybel_9('#skF_6') | ~v1_compts_1('#skF_6') | ~v2_lattice3('#skF_6') | ~v1_lattice3('#skF_6') | ~v4_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | ~v8_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672))) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672)), C_674) | ~m1_subset_1(C_674, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_2600, c_1971])).
% 20.72/10.47  tff(c_2636, plain, (![D_673, B_672, C_45, C_674]: (r3_orders_2('#skF_6', D_673, '#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672)), C_45)) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672)), C_45) | ~m1_subset_1(C_45, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_673, '#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672)), C_674)) | ~r3_waybel_9('#skF_6', B_672, D_673) | ~m1_subset_1(D_673, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_672, '#skF_6') | ~v7_waybel_0(B_672) | ~v4_orders_2(B_672) | v2_struct_0(B_672) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672))) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_672), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_672)), C_674) | ~m1_subset_1(C_674, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_92, c_90, c_88, c_86, c_82, c_80, c_78, c_76, c_2603])).
% 20.72/10.47  tff(c_11747, plain, (![B_1329, D_1330, C_1331]: (~r3_waybel_9('#skF_6', B_1329, D_1330) | ~m1_subset_1(D_1330, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_1329, '#skF_6') | ~v7_waybel_0(B_1329) | ~v4_orders_2(B_1329) | v2_struct_0(B_1329) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_1329), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1329))) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_1329), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1329)), C_1331) | ~m1_subset_1(C_1331, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1330, '#skF_2'('#skF_6', k2_relset_1(u1_struct_0(B_1329), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1329)), C_1331)))), inference(factorization, [status(thm), theory('equality')], [c_2636])).
% 20.72/10.47  tff(c_11753, plain, (![B_168, D_1330, C_1331]: (~r3_waybel_9('#skF_6', B_168, D_1330) | ~m1_subset_1(D_1330, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_168, '#skF_6') | ~v7_waybel_0(B_168) | ~v4_orders_2(B_168) | v2_struct_0(B_168) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_168), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_168))) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_168), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_168)), C_1331) | ~m1_subset_1(C_1331, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1330, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168)), C_1331)) | ~l1_waybel_0(B_168, '#skF_6') | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_11747])).
% 20.72/10.47  tff(c_11760, plain, (![B_1332, D_1333, C_1334]: (~r3_waybel_9('#skF_6', B_1332, D_1333) | ~m1_subset_1(D_1333, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1332) | ~v4_orders_2(B_1332) | v2_struct_0(B_1332) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_1332), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1332))) | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_1332), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1332)), C_1334) | ~m1_subset_1(C_1334, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1333, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1332)), C_1334)) | ~l1_waybel_0(B_1332, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_11753])).
% 20.72/10.47  tff(c_11812, plain, (![B_1335, D_1336, D_1337]: (~r3_waybel_9('#skF_6', B_1335, D_1336) | ~m1_subset_1(D_1336, u1_struct_0('#skF_6')) | r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_1335), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1335))) | r3_orders_2('#skF_6', D_1336, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1335)), D_1337)) | ~r3_waybel_9('#skF_6', B_1335, D_1337) | ~v10_waybel_0(B_1335, '#skF_6') | ~m1_subset_1(D_1337, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_1335, '#skF_6') | ~v7_waybel_0(B_1335) | ~v4_orders_2(B_1335) | v2_struct_0(B_1335))), inference(resolution, [status(thm)], [c_791, c_11760])).
% 20.72/10.47  tff(c_11830, plain, (![B_1335, D_1336, D_1337]: (k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_1335), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1335)))='#skF_3'('#skF_6', k2_relset_1(u1_struct_0(B_1335), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1335))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~r3_waybel_9('#skF_6', B_1335, D_1336) | ~m1_subset_1(D_1336, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1336, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1335)), D_1337)) | ~r3_waybel_9('#skF_6', B_1335, D_1337) | ~v10_waybel_0(B_1335, '#skF_6') | ~m1_subset_1(D_1337, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_1335, '#skF_6') | ~v7_waybel_0(B_1335) | ~v4_orders_2(B_1335) | v2_struct_0(B_1335))), inference(resolution, [status(thm)], [c_11812, c_950])).
% 20.72/10.47  tff(c_12271, plain, (![B_1379, D_1380, D_1381]: (k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_1379), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1379)))='#skF_3'('#skF_6', k2_relset_1(u1_struct_0(B_1379), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1379))) | ~r3_waybel_9('#skF_6', B_1379, D_1380) | ~m1_subset_1(D_1380, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1380, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1379)), D_1381)) | ~r3_waybel_9('#skF_6', B_1379, D_1381) | ~v10_waybel_0(B_1379, '#skF_6') | ~m1_subset_1(D_1381, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_1379, '#skF_6') | ~v7_waybel_0(B_1379) | ~v4_orders_2(B_1379) | v2_struct_0(B_1379))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_11830])).
% 20.72/10.47  tff(c_12301, plain, (![B_168, D_1380, D_1381]: ('#skF_3'('#skF_6', k2_relset_1(u1_struct_0(B_168), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_168)))=k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168))) | ~r3_waybel_9('#skF_6', B_168, D_1380) | ~m1_subset_1(D_1380, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1380, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_168)), D_1381)) | ~r3_waybel_9('#skF_6', B_168, D_1381) | ~v10_waybel_0(B_168, '#skF_6') | ~m1_subset_1(D_1381, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_168, '#skF_6') | ~v7_waybel_0(B_168) | ~v4_orders_2(B_168) | v2_struct_0(B_168) | ~l1_waybel_0(B_168, '#skF_6') | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_12271])).
% 20.72/10.47  tff(c_12379, plain, (![B_1386, D_1387, D_1388]: ('#skF_3'('#skF_6', k2_relset_1(u1_struct_0(B_1386), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1386)))=k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1386))) | ~r3_waybel_9('#skF_6', B_1386, D_1387) | ~m1_subset_1(D_1387, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1387, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1386)), D_1388)) | ~r3_waybel_9('#skF_6', B_1386, D_1388) | ~v10_waybel_0(B_1386, '#skF_6') | ~m1_subset_1(D_1388, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1386) | ~v4_orders_2(B_1386) | v2_struct_0(B_1386) | ~l1_waybel_0(B_1386, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_12301])).
% 20.72/10.47  tff(c_12446, plain, (![B_1386, D_1387, D_1388]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_1386), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1386)), k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1386)))) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_1386), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_1386))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6') | ~r3_waybel_9('#skF_6', B_1386, D_1387) | ~m1_subset_1(D_1387, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1387, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_1386)), D_1388)) | ~r3_waybel_9('#skF_6', B_1386, D_1388) | ~v10_waybel_0(B_1386, '#skF_6') | ~m1_subset_1(D_1388, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_1386) | ~v4_orders_2(B_1386) | v2_struct_0(B_1386) | ~l1_waybel_0(B_1386, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12379, c_26])).
% 20.72/10.47  tff(c_20163, plain, (![B_15048, D_15049, D_15050]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_15048), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_15048)), k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_15048)))) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_15048), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_15048))) | ~r3_waybel_9('#skF_6', B_15048, D_15049) | ~m1_subset_1(D_15049, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_15049, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', B_15048)), D_15050)) | ~r3_waybel_9('#skF_6', B_15048, D_15050) | ~v10_waybel_0(B_15048, '#skF_6') | ~m1_subset_1(D_15050, u1_struct_0('#skF_6')) | ~v7_waybel_0(B_15048) | ~v4_orders_2(B_15048) | v2_struct_0(B_15048) | ~l1_waybel_0(B_15048, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_12446])).
% 20.72/10.47  tff(c_20228, plain, (![D_15049, D_15050]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), k1_waybel_2('#skF_6', '#skF_8')) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8'))) | ~r3_waybel_9('#skF_6', '#skF_8', D_15049) | ~m1_subset_1(D_15049, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_15049, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_15050)) | ~r3_waybel_9('#skF_6', '#skF_8', D_15050) | ~v10_waybel_0('#skF_8', '#skF_6') | ~m1_subset_1(D_15050, u1_struct_0('#skF_6')) | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9700, c_20163])).
% 20.72/10.47  tff(c_20260, plain, (![D_15049, D_15050]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), k1_waybel_2('#skF_6', '#skF_8')) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8'))) | ~r3_waybel_9('#skF_6', '#skF_8', D_15049) | ~m1_subset_1(D_15049, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_15049, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_15050)) | ~r3_waybel_9('#skF_6', '#skF_8', D_15050) | ~m1_subset_1(D_15050, u1_struct_0('#skF_6')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_62, c_20228])).
% 20.72/10.47  tff(c_20261, plain, (![D_15049, D_15050]: (r2_lattice3('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), k1_waybel_2('#skF_6', '#skF_8')) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8'))) | ~r3_waybel_9('#skF_6', '#skF_8', D_15049) | ~m1_subset_1(D_15049, u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_15049, '#skF_2'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_15050)) | ~r3_waybel_9('#skF_6', '#skF_8', D_15050) | ~m1_subset_1(D_15050, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_72, c_20260])).
% 20.72/10.47  tff(c_20267, plain, (~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')))), inference(splitLeft, [status(thm)], [c_20261])).
% 20.72/10.47  tff(c_20282, plain, (~r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~l1_waybel_0('#skF_8', '#skF_6') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_128, c_20267])).
% 20.72/10.47  tff(c_20301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_806, c_66, c_7522, c_20282])).
% 20.72/10.47  tff(c_20303, plain, (r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')))), inference(splitRight, [status(thm)], [c_20261])).
% 20.72/10.47  tff(c_20325, plain, (k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')))='#skF_3'('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8'))) | ~l1_orders_2('#skF_6') | ~v5_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_20303, c_950])).
% 20.72/10.47  tff(c_20367, plain, (k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')))='#skF_3'('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_97, c_20325])).
% 20.72/10.47  tff(c_20458, plain, ('#skF_3'('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')))=k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~l1_waybel_0('#skF_8', '#skF_6') | ~l1_struct_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_128, c_20367])).
% 20.72/10.47  tff(c_20513, plain, ('#skF_3'('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')))=k1_waybel_2('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_806, c_66, c_9700, c_20458])).
% 20.72/10.47  tff(c_20514, plain, (k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')))=k1_waybel_2('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_20513, c_20367])).
% 20.72/10.47  tff(c_20758, plain, (![D_1259]: (k1_waybel_2('#skF_6', '#skF_8')='#skF_7' | m1_subset_1('#skF_5'('#skF_6', '#skF_8', D_1259, D_1259), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1259, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')) | ~r3_waybel_9('#skF_6', '#skF_8', D_1259) | ~m1_subset_1(D_1259, u1_struct_0('#skF_6')) | ~r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~r3_waybel_9('#skF_6', '#skF_8', '#skF_7') | ~v10_waybel_0('#skF_8', '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_20755, c_20514])).
% 20.72/10.47  tff(c_20813, plain, (![D_1259]: (k1_waybel_2('#skF_6', '#skF_8')='#skF_7' | m1_subset_1('#skF_5'('#skF_6', '#skF_8', D_1259, D_1259), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_1259, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')) | ~r3_waybel_9('#skF_6', '#skF_8', D_1259) | ~m1_subset_1(D_1259, u1_struct_0('#skF_6')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_74, c_62, c_60, c_7522, c_20758])).
% 20.72/10.47  tff(c_20826, plain, (![D_15255]: (m1_subset_1('#skF_5'('#skF_6', '#skF_8', D_15255, D_15255), u1_struct_0('#skF_6')) | r3_orders_2('#skF_6', D_15255, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')) | ~r3_waybel_9('#skF_6', '#skF_8', D_15255) | ~m1_subset_1(D_15255, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_72, c_58, c_20813])).
% 20.72/10.47  tff(c_20846, plain, (![D_15255]: (r1_orders_2('#skF_6', D_15255, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7'), u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6') | m1_subset_1('#skF_5'('#skF_6', '#skF_8', D_15255, D_15255), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', '#skF_8', D_15255) | ~m1_subset_1(D_15255, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_20826, c_10])).
% 20.72/10.47  tff(c_20878, plain, (![D_15255]: (r1_orders_2('#skF_6', D_15255, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7'), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | m1_subset_1('#skF_5'('#skF_6', '#skF_8', D_15255, D_15255), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', '#skF_8', D_15255) | ~m1_subset_1(D_15255, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_97, c_20846])).
% 20.72/10.47  tff(c_20879, plain, (![D_15255]: (r1_orders_2('#skF_6', D_15255, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')) | ~m1_subset_1('#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7'), u1_struct_0('#skF_6')) | m1_subset_1('#skF_5'('#skF_6', '#skF_8', D_15255, D_15255), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', '#skF_8', D_15255) | ~m1_subset_1(D_15255, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_177, c_20878])).
% 20.72/10.47  tff(c_21408, plain, (~m1_subset_1('#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7'), u1_struct_0('#skF_6'))), inference(splitLeft, [status(thm)], [c_20879])).
% 20.72/10.47  tff(c_21411, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))='#skF_7' | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7') | ~r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_18, c_21408])).
% 20.72/10.47  tff(c_21414, plain, (k1_waybel_2('#skF_6', '#skF_8')='#skF_7' | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_74, c_7522, c_9700, c_21411])).
% 20.72/10.47  tff(c_21415, plain, (~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_21414])).
% 20.72/10.47  tff(c_21427, plain, (~r3_waybel_9('#skF_6', '#skF_8', '#skF_7') | ~v10_waybel_0('#skF_8', '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_805, c_21415])).
% 20.72/10.47  tff(c_21442, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_74, c_62, c_60, c_21427])).
% 20.72/10.47  tff(c_21444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_21442])).
% 20.72/10.47  tff(c_21484, plain, (![D_15812]: (r1_orders_2('#skF_6', D_15812, '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')) | m1_subset_1('#skF_5'('#skF_6', '#skF_8', D_15812, D_15812), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', '#skF_8', D_15812) | ~m1_subset_1(D_15812, u1_struct_0('#skF_6')))), inference(splitRight, [status(thm)], [c_20879])).
% 20.72/10.47  tff(c_21488, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))='#skF_7' | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7') | ~r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~l1_orders_2('#skF_6') | m1_subset_1('#skF_5'('#skF_6', '#skF_8', '#skF_7', '#skF_7'), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', '#skF_8', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_21484, c_14])).
% 20.72/10.47  tff(c_21514, plain, (k1_waybel_2('#skF_6', '#skF_8')='#skF_7' | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7') | m1_subset_1('#skF_5'('#skF_6', '#skF_8', '#skF_7', '#skF_7'), u1_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_97, c_7522, c_9700, c_21488])).
% 20.72/10.47  tff(c_21515, plain, (~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7') | m1_subset_1('#skF_5'('#skF_6', '#skF_8', '#skF_7', '#skF_7'), u1_struct_0('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_58, c_21514])).
% 20.72/10.47  tff(c_21605, plain, (~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')), inference(splitLeft, [status(thm)], [c_21515])).
% 20.72/10.47  tff(c_21617, plain, (~r3_waybel_9('#skF_6', '#skF_8', '#skF_7') | ~v10_waybel_0('#skF_8', '#skF_6') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_805, c_21605])).
% 20.72/10.47  tff(c_21632, plain, (v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_70, c_68, c_74, c_62, c_60, c_21617])).
% 20.72/10.47  tff(c_21634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_21632])).
% 20.72/10.47  tff(c_21636, plain, (r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')), inference(splitRight, [status(thm)], [c_21515])).
% 20.72/10.47  tff(c_21446, plain, (m1_subset_1('#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_20879])).
% 20.72/10.47  tff(c_21635, plain, (m1_subset_1('#skF_5'('#skF_6', '#skF_8', '#skF_7', '#skF_7'), u1_struct_0('#skF_6'))), inference(splitRight, [status(thm)], [c_21515])).
% 20.72/10.47  tff(c_959, plain, (![D_389, B_391, C_20]: (r3_orders_2('#skF_6', D_389, '#skF_1'('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391)), C_20)) | ~m1_subset_1('#skF_1'('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391)), C_20), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_391, D_389) | ~m1_subset_1(D_389, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_391, '#skF_6') | ~v7_waybel_0(B_391) | ~v4_orders_2(B_391) | v2_struct_0(B_391) | ~m1_subset_1('#skF_5'('#skF_6', B_391, D_389, D_389), u1_struct_0('#skF_6')) | k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391)))=C_20 | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391)), C_20) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_391))) | ~m1_subset_1(C_20, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_16, c_951])).
% 20.72/10.47  tff(c_2793, plain, (![D_685, B_686, C_687]: (r3_orders_2('#skF_6', D_685, '#skF_1'('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)), C_687)) | ~m1_subset_1('#skF_1'('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)), C_687), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', B_686, D_685) | ~m1_subset_1(D_685, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_686, '#skF_6') | ~v7_waybel_0(B_686) | ~v4_orders_2(B_686) | v2_struct_0(B_686) | ~m1_subset_1('#skF_5'('#skF_6', B_686, D_685, D_685), u1_struct_0('#skF_6')) | k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)))=C_687 | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)), C_687) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686))) | ~m1_subset_1(C_687, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_959])).
% 20.72/10.47  tff(c_2796, plain, (![D_685, B_686, C_20]: (r3_orders_2('#skF_6', D_685, '#skF_1'('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)), C_20)) | ~r3_waybel_9('#skF_6', B_686, D_685) | ~m1_subset_1(D_685, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_686, '#skF_6') | ~v7_waybel_0(B_686) | ~v4_orders_2(B_686) | v2_struct_0(B_686) | ~m1_subset_1('#skF_5'('#skF_6', B_686, D_685, D_685), u1_struct_0('#skF_6')) | k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)))=C_20 | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)), C_20) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686))) | ~m1_subset_1(C_20, u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6'))), inference(resolution, [status(thm)], [c_18, c_2793])).
% 20.72/10.47  tff(c_2802, plain, (![D_685, B_686, C_20]: (r3_orders_2('#skF_6', D_685, '#skF_1'('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)), C_20)) | ~r3_waybel_9('#skF_6', B_686, D_685) | ~m1_subset_1(D_685, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_686, '#skF_6') | ~v7_waybel_0(B_686) | ~v4_orders_2(B_686) | v2_struct_0(B_686) | ~m1_subset_1('#skF_5'('#skF_6', B_686, D_685, D_685), u1_struct_0('#skF_6')) | k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)))=C_20 | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686)), C_20) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0(B_686), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', B_686))) | ~m1_subset_1(C_20, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_2796])).
% 20.72/10.47  tff(c_21933, plain, (![C_20]: (r3_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), C_20)) | ~r3_waybel_9('#skF_6', '#skF_8', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_8', '#skF_6') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | k1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')))=C_20 | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), C_20) | ~r1_yellow_0('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8'))) | ~m1_subset_1(C_20, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_21635, c_2802])).
% 20.72/10.47  tff(c_21954, plain, (![C_20]: (r3_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), C_20)) | v2_struct_0('#skF_8') | k1_waybel_2('#skF_6', '#skF_8')=C_20 | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_20303, c_20514, c_70, c_68, c_66, c_74, c_60, c_21933])).
% 20.72/10.47  tff(c_22592, plain, (![C_16478]: (r3_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), C_16478)) | k1_waybel_2('#skF_6', '#skF_8')=C_16478 | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), C_16478) | ~m1_subset_1(C_16478, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_72, c_21954])).
% 20.72/10.47  tff(c_22600, plain, (![C_16478]: (r3_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), C_16478)) | k1_waybel_2('#skF_6', '#skF_8')=C_16478 | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), C_16478) | ~m1_subset_1(C_16478, u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_8', '#skF_6') | ~l1_struct_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_128, c_22592])).
% 20.72/10.47  tff(c_22607, plain, (![C_16513]: (r3_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), C_16513)) | k1_waybel_2('#skF_6', '#skF_8')=C_16513 | ~r2_lattice3('#skF_6', k2_relset_1(u1_struct_0('#skF_8'), u1_struct_0('#skF_6'), u1_waybel_0('#skF_6', '#skF_8')), C_16513) | ~m1_subset_1(C_16513, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_806, c_66, c_22600])).
% 20.72/10.47  tff(c_22638, plain, (![D_86]: (r3_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_86)) | k1_waybel_2('#skF_6', '#skF_8')=D_86 | ~r3_waybel_9('#skF_6', '#skF_8', D_86) | ~v10_waybel_0('#skF_8', '#skF_6') | ~m1_subset_1(D_86, u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_8', '#skF_6') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_791, c_22607])).
% 20.72/10.47  tff(c_22688, plain, (![D_86]: (r3_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_86)) | k1_waybel_2('#skF_6', '#skF_8')=D_86 | ~r3_waybel_9('#skF_6', '#skF_8', D_86) | ~m1_subset_1(D_86, u1_struct_0('#skF_6')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_62, c_22638])).
% 20.72/10.47  tff(c_22705, plain, (![D_16548]: (r3_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_16548)) | k1_waybel_2('#skF_6', '#skF_8')=D_16548 | ~r3_waybel_9('#skF_6', '#skF_8', D_16548) | ~m1_subset_1(D_16548, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_72, c_22688])).
% 20.72/10.47  tff(c_22707, plain, (![D_16548]: (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_16548)) | ~m1_subset_1('#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_16548), u1_struct_0('#skF_6')) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6') | ~v3_orders_2('#skF_6') | v2_struct_0('#skF_6') | k1_waybel_2('#skF_6', '#skF_8')=D_16548 | ~r3_waybel_9('#skF_6', '#skF_8', D_16548) | ~m1_subset_1(D_16548, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_22705, c_10])).
% 20.72/10.47  tff(c_22713, plain, (![D_16548]: (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_16548)) | ~m1_subset_1('#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_16548), u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | k1_waybel_2('#skF_6', '#skF_8')=D_16548 | ~r3_waybel_9('#skF_6', '#skF_8', D_16548) | ~m1_subset_1(D_16548, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_97, c_74, c_22707])).
% 20.72/10.47  tff(c_22715, plain, (![D_16583]: (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_16583)) | ~m1_subset_1('#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), D_16583), u1_struct_0('#skF_6')) | k1_waybel_2('#skF_6', '#skF_8')=D_16583 | ~r3_waybel_9('#skF_6', '#skF_8', D_16583) | ~m1_subset_1(D_16583, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_177, c_22713])).
% 20.72/10.47  tff(c_22718, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')) | k1_waybel_2('#skF_6', '#skF_8')='#skF_7' | ~r3_waybel_9('#skF_6', '#skF_8', '#skF_7') | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_21446, c_22715])).
% 20.72/10.47  tff(c_22728, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7')) | k1_waybel_2('#skF_6', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_60, c_22718])).
% 20.72/10.47  tff(c_22729, plain, (r1_orders_2('#skF_6', '#skF_7', '#skF_1'('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_58, c_22728])).
% 20.72/10.47  tff(c_22735, plain, (k1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')))='#skF_7' | ~r2_lattice3('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8')), '#skF_7') | ~r1_yellow_0('#skF_6', k2_relat_1(u1_waybel_0('#skF_6', '#skF_8'))) | ~m1_subset_1('#skF_7', u1_struct_0('#skF_6')) | ~l1_orders_2('#skF_6')), inference(resolution, [status(thm)], [c_22729, c_14])).
% 20.72/10.47  tff(c_22738, plain, (k1_waybel_2('#skF_6', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_74, c_7522, c_21636, c_9700, c_22735])).
% 20.72/10.47  tff(c_22740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_22738])).
% 20.72/10.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.72/10.47  
% 20.72/10.47  Inference rules
% 20.72/10.47  ----------------------
% 20.72/10.47  #Ref     : 0
% 20.72/10.47  #Sup     : 4233
% 20.72/10.47  #Fact    : 26
% 20.72/10.47  #Define  : 0
% 20.72/10.47  #Split   : 16
% 20.72/10.47  #Chain   : 0
% 20.72/10.47  #Close   : 0
% 20.72/10.47  
% 20.72/10.47  Ordering : KBO
% 20.72/10.47  
% 20.72/10.47  Simplification rules
% 20.72/10.47  ----------------------
% 20.72/10.47  #Subsume      : 1064
% 20.72/10.47  #Demod        : 11075
% 20.72/10.47  #Tautology    : 513
% 20.72/10.47  #SimpNegUnit  : 1272
% 20.72/10.47  #BackRed      : 22
% 20.72/10.47  
% 20.72/10.47  #Partial instantiations: 7938
% 20.72/10.47  #Strategies tried      : 1
% 20.72/10.47  
% 20.72/10.47  Timing (in seconds)
% 20.72/10.47  ----------------------
% 20.72/10.47  Preprocessing        : 0.39
% 20.72/10.47  Parsing              : 0.20
% 20.72/10.47  CNF conversion       : 0.03
% 20.72/10.47  Main loop            : 9.23
% 20.72/10.47  Inferencing          : 2.85
% 20.72/10.47  Reduction            : 2.12
% 20.72/10.47  Demodulation         : 1.57
% 20.72/10.47  BG Simplification    : 0.16
% 20.72/10.47  Subsumption          : 3.80
% 20.72/10.47  Abstraction          : 0.29
% 20.72/10.47  MUC search           : 0.00
% 20.72/10.47  Cooper               : 0.00
% 20.72/10.47  Total                : 9.75
% 20.72/10.47  Index Insertion      : 0.00
% 20.72/10.47  Index Deletion       : 0.00
% 20.72/10.47  Index Matching       : 0.00
% 20.72/10.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
