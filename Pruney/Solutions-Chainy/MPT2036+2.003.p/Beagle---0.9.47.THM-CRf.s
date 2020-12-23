%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:21 EST 2020

% Result     : Theorem 23.07s
% Output     : CNFRefutation 23.22s
% Verified   : 
% Statistics : Number of formulae       :  200 (1702 expanded)
%              Number of leaves         :   58 ( 710 expanded)
%              Depth                    :   36
%              Number of atoms          : 1279 (15223 expanded)
%              Number of equality atoms :   58 ( 705 expanded)
%              Maximal formula depth    :   29 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v1_funct_2 > r3_waybel_9 > r3_orders_2 > r2_lattice3 > r1_orders_2 > v10_waybel_0 > r1_yellow_0 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_relat_1 > v1_lattice3 > v1_funct_1 > v1_compts_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_yellow_2 > k4_waybel_1 > k2_zfmisc_1 > k1_yellow_0 > k1_waybel_2 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff(k4_waybel_1,type,(
    k4_waybel_1: ( $i * $i ) > $i )).

tff(u1_waybel_0,type,(
    u1_waybel_0: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_waybel_2,type,(
    k1_waybel_2: ( $i * $i ) > $i )).

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_269,negated_conjecture,(
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

tff(f_129,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

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

tff(f_37,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_103,axiom,(
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

tff(f_176,axiom,(
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

tff(f_29,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) )
               => ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) )
              & ( ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) )
               => ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_226,axiom,(
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

tff(f_113,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( l1_waybel_0(B,A)
         => k1_waybel_2(A,B) = k4_yellow_2(A,u1_waybel_0(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_waybel_2)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( v1_relat_1(B)
         => k4_yellow_2(A,B) = k1_yellow_0(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_2)).

tff(c_70,plain,(
    l1_waybel_9('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_88,plain,(
    ! [A_132] :
      ( l1_orders_2(A_132)
      | ~ l1_waybel_9(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_92,plain,(
    l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_88])).

tff(c_76,plain,(
    v1_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_82,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_145,plain,(
    ! [A_161,B_162,C_163] :
      ( r3_orders_2(A_161,B_162,C_163)
      | ~ r1_orders_2(A_161,B_162,C_163)
      | ~ m1_subset_1(C_163,u1_struct_0(A_161))
      | ~ m1_subset_1(B_162,u1_struct_0(A_161))
      | ~ l1_orders_2(A_161)
      | ~ v3_orders_2(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_147,plain,(
    ! [B_162] :
      ( r3_orders_2('#skF_4',B_162,'#skF_5')
      | ~ r1_orders_2('#skF_4',B_162,'#skF_5')
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_68,c_145])).

tff(c_150,plain,(
    ! [B_162] :
      ( r3_orders_2('#skF_4',B_162,'#skF_5')
      | ~ r1_orders_2('#skF_4',B_162,'#skF_5')
      | ~ m1_subset_1(B_162,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_92,c_147])).

tff(c_151,plain,(
    v2_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_12,plain,(
    ! [A_11] :
      ( ~ v2_struct_0(A_11)
      | ~ v1_lattice3(A_11)
      | ~ l1_orders_2(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_154,plain,
    ( ~ v1_lattice3('#skF_4')
    | ~ l1_orders_2('#skF_4') ),
    inference(resolution,[status(thm)],[c_151,c_12])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_76,c_154])).

tff(c_160,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_52,plain,(
    k1_waybel_2('#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_60,plain,(
    l1_waybel_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_93,plain,(
    ! [A_133] :
      ( l1_pre_topc(A_133)
      | ~ l1_waybel_9(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_97,plain,(
    l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_93])).

tff(c_6,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [A_148,B_149] :
      ( m1_subset_1(u1_waybel_0(A_148,B_149),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_149),u1_struct_0(A_148))))
      | ~ l1_waybel_0(B_149,A_148)
      | ~ l1_struct_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( k2_relset_1(A_4,B_5,C_6) = k2_relat_1(C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(A_4,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [B_149,A_148] :
      ( k2_relset_1(u1_struct_0(B_149),u1_struct_0(A_148),u1_waybel_0(A_148,B_149)) = k2_relat_1(u1_waybel_0(A_148,B_149))
      | ~ l1_waybel_0(B_149,A_148)
      | ~ l1_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_113,c_4])).

tff(c_86,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_84,plain,(
    v8_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_80,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_78,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_74,plain,(
    v2_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_72,plain,(
    v1_compts_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_46,plain,(
    ! [A_43,B_59,D_71] :
      ( m1_subset_1('#skF_2'(A_43,B_59,D_71,D_71),u1_struct_0(A_43))
      | r2_lattice3(A_43,k2_relset_1(u1_struct_0(B_59),u1_struct_0(A_43),u1_waybel_0(A_43,B_59)),D_71)
      | ~ r3_waybel_9(A_43,B_59,D_71)
      | ~ v10_waybel_0(B_59,A_43)
      | ~ m1_subset_1(D_71,u1_struct_0(A_43))
      | ~ l1_waybel_0(B_59,A_43)
      | ~ v7_waybel_0(B_59)
      | ~ v4_orders_2(B_59)
      | v2_struct_0(B_59)
      | ~ l1_waybel_9(A_43)
      | ~ v1_compts_1(A_43)
      | ~ v2_lattice3(A_43)
      | ~ v1_lattice3(A_43)
      | ~ v5_orders_2(A_43)
      | ~ v4_orders_2(A_43)
      | ~ v3_orders_2(A_43)
      | ~ v8_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_58,plain,(
    ! [D_130] :
      ( v5_pre_topc(k4_waybel_1('#skF_4',D_130),'#skF_4','#skF_4')
      | ~ m1_subset_1(D_130,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_710,plain,(
    ! [A_331,B_332,D_333] :
      ( ~ v5_pre_topc(k4_waybel_1(A_331,'#skF_2'(A_331,B_332,D_333,D_333)),A_331,A_331)
      | r2_lattice3(A_331,k2_relset_1(u1_struct_0(B_332),u1_struct_0(A_331),u1_waybel_0(A_331,B_332)),D_333)
      | ~ r3_waybel_9(A_331,B_332,D_333)
      | ~ v10_waybel_0(B_332,A_331)
      | ~ m1_subset_1(D_333,u1_struct_0(A_331))
      | ~ l1_waybel_0(B_332,A_331)
      | ~ v7_waybel_0(B_332)
      | ~ v4_orders_2(B_332)
      | v2_struct_0(B_332)
      | ~ l1_waybel_9(A_331)
      | ~ v1_compts_1(A_331)
      | ~ v2_lattice3(A_331)
      | ~ v1_lattice3(A_331)
      | ~ v5_orders_2(A_331)
      | ~ v4_orders_2(A_331)
      | ~ v3_orders_2(A_331)
      | ~ v8_pre_topc(A_331)
      | ~ v2_pre_topc(A_331) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_713,plain,(
    ! [B_332,D_333] :
      ( r2_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_332),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_332)),D_333)
      | ~ r3_waybel_9('#skF_4',B_332,D_333)
      | ~ v10_waybel_0(B_332,'#skF_4')
      | ~ m1_subset_1(D_333,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_332,'#skF_4')
      | ~ v7_waybel_0(B_332)
      | ~ v4_orders_2(B_332)
      | v2_struct_0(B_332)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_332,D_333,D_333),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_58,c_710])).

tff(c_717,plain,(
    ! [B_334,D_335] :
      ( r2_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_334),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_334)),D_335)
      | ~ r3_waybel_9('#skF_4',B_334,D_335)
      | ~ v10_waybel_0(B_334,'#skF_4')
      | ~ m1_subset_1(D_335,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_334,'#skF_4')
      | ~ v7_waybel_0(B_334)
      | ~ v4_orders_2(B_334)
      | v2_struct_0(B_334)
      | ~ m1_subset_1('#skF_2'('#skF_4',B_334,D_335,D_335),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_713])).

tff(c_720,plain,(
    ! [B_59,D_71] :
      ( r2_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_59),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_59)),D_71)
      | ~ r3_waybel_9('#skF_4',B_59,D_71)
      | ~ v10_waybel_0(B_59,'#skF_4')
      | ~ m1_subset_1(D_71,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_59,'#skF_4')
      | ~ v7_waybel_0(B_59)
      | ~ v4_orders_2(B_59)
      | v2_struct_0(B_59)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_46,c_717])).

tff(c_724,plain,(
    ! [B_336,D_337] :
      ( r2_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_336),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_336)),D_337)
      | ~ r3_waybel_9('#skF_4',B_336,D_337)
      | ~ v10_waybel_0(B_336,'#skF_4')
      | ~ m1_subset_1(D_337,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_336,'#skF_4')
      | ~ v7_waybel_0(B_336)
      | ~ v4_orders_2(B_336)
      | v2_struct_0(B_336) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_720])).

tff(c_728,plain,(
    ! [B_149,D_337] :
      ( r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_149)),D_337)
      | ~ r3_waybel_9('#skF_4',B_149,D_337)
      | ~ v10_waybel_0(B_149,'#skF_4')
      | ~ m1_subset_1(D_337,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_149,'#skF_4')
      | ~ v7_waybel_0(B_149)
      | ~ v4_orders_2(B_149)
      | v2_struct_0(B_149)
      | ~ l1_waybel_0(B_149,'#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_724])).

tff(c_729,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_728])).

tff(c_732,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_729])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_732])).

tff(c_738,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_2,plain,(
    ! [C_3,A_1,B_2] :
      ( v1_relat_1(C_3)
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(A_1,B_2))) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_121,plain,(
    ! [A_148,B_149] :
      ( v1_relat_1(u1_waybel_0(A_148,B_149))
      | ~ l1_waybel_0(B_149,A_148)
      | ~ l1_struct_0(A_148) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_64,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_62,plain,(
    v7_waybel_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_56,plain,(
    v10_waybel_0('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_54,plain,(
    r3_waybel_9('#skF_4','#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_737,plain,(
    ! [B_149,D_337] :
      ( r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_149)),D_337)
      | ~ r3_waybel_9('#skF_4',B_149,D_337)
      | ~ v10_waybel_0(B_149,'#skF_4')
      | ~ m1_subset_1(D_337,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_149,'#skF_4')
      | ~ v7_waybel_0(B_149)
      | ~ v4_orders_2(B_149)
      | v2_struct_0(B_149)
      | ~ l1_waybel_0(B_149,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_22,plain,(
    ! [A_12,B_24,C_30] :
      ( m1_subset_1('#skF_1'(A_12,B_24,C_30),u1_struct_0(A_12))
      | r1_yellow_0(A_12,C_30)
      | ~ r2_lattice3(A_12,C_30,B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    ! [A_12,C_30,B_24] :
      ( r2_lattice3(A_12,C_30,'#skF_1'(A_12,B_24,C_30))
      | r1_yellow_0(A_12,C_30)
      | ~ r2_lattice3(A_12,C_30,B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_776,plain,(
    ! [A_346,B_347,D_348,E_349] :
      ( m1_subset_1('#skF_3'(A_346,B_347,D_348,D_348),u1_struct_0(A_346))
      | r3_orders_2(A_346,D_348,E_349)
      | ~ r2_lattice3(A_346,k2_relset_1(u1_struct_0(B_347),u1_struct_0(A_346),u1_waybel_0(A_346,B_347)),E_349)
      | ~ m1_subset_1(E_349,u1_struct_0(A_346))
      | ~ r3_waybel_9(A_346,B_347,D_348)
      | ~ m1_subset_1(D_348,u1_struct_0(A_346))
      | ~ l1_waybel_0(B_347,A_346)
      | ~ v7_waybel_0(B_347)
      | ~ v4_orders_2(B_347)
      | v2_struct_0(B_347)
      | ~ l1_waybel_9(A_346)
      | ~ v1_compts_1(A_346)
      | ~ v2_lattice3(A_346)
      | ~ v1_lattice3(A_346)
      | ~ v5_orders_2(A_346)
      | ~ v4_orders_2(A_346)
      | ~ v3_orders_2(A_346)
      | ~ v8_pre_topc(A_346)
      | ~ v2_pre_topc(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_1288,plain,(
    ! [A_444,B_445,D_446,E_447] :
      ( m1_subset_1('#skF_3'(A_444,B_445,D_446,D_446),u1_struct_0(A_444))
      | r3_orders_2(A_444,D_446,E_447)
      | ~ r2_lattice3(A_444,k2_relat_1(u1_waybel_0(A_444,B_445)),E_447)
      | ~ m1_subset_1(E_447,u1_struct_0(A_444))
      | ~ r3_waybel_9(A_444,B_445,D_446)
      | ~ m1_subset_1(D_446,u1_struct_0(A_444))
      | ~ l1_waybel_0(B_445,A_444)
      | ~ v7_waybel_0(B_445)
      | ~ v4_orders_2(B_445)
      | v2_struct_0(B_445)
      | ~ l1_waybel_9(A_444)
      | ~ v1_compts_1(A_444)
      | ~ v2_lattice3(A_444)
      | ~ v1_lattice3(A_444)
      | ~ v5_orders_2(A_444)
      | ~ v4_orders_2(A_444)
      | ~ v3_orders_2(A_444)
      | ~ v8_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | ~ l1_waybel_0(B_445,A_444)
      | ~ l1_struct_0(A_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_776])).

tff(c_12631,plain,(
    ! [A_23257,B_23258,D_23259,B_23260] :
      ( m1_subset_1('#skF_3'(A_23257,B_23258,D_23259,D_23259),u1_struct_0(A_23257))
      | r3_orders_2(A_23257,D_23259,'#skF_1'(A_23257,B_23260,k2_relat_1(u1_waybel_0(A_23257,B_23258))))
      | ~ m1_subset_1('#skF_1'(A_23257,B_23260,k2_relat_1(u1_waybel_0(A_23257,B_23258))),u1_struct_0(A_23257))
      | ~ r3_waybel_9(A_23257,B_23258,D_23259)
      | ~ m1_subset_1(D_23259,u1_struct_0(A_23257))
      | ~ v7_waybel_0(B_23258)
      | ~ v4_orders_2(B_23258)
      | v2_struct_0(B_23258)
      | ~ l1_waybel_9(A_23257)
      | ~ v1_compts_1(A_23257)
      | ~ v2_lattice3(A_23257)
      | ~ v1_lattice3(A_23257)
      | ~ v4_orders_2(A_23257)
      | ~ v3_orders_2(A_23257)
      | ~ v8_pre_topc(A_23257)
      | ~ v2_pre_topc(A_23257)
      | ~ l1_waybel_0(B_23258,A_23257)
      | ~ l1_struct_0(A_23257)
      | r1_yellow_0(A_23257,k2_relat_1(u1_waybel_0(A_23257,B_23258)))
      | ~ r2_lattice3(A_23257,k2_relat_1(u1_waybel_0(A_23257,B_23258)),B_23260)
      | ~ m1_subset_1(B_23260,u1_struct_0(A_23257))
      | ~ l1_orders_2(A_23257)
      | ~ v5_orders_2(A_23257) ) ),
    inference(resolution,[status(thm)],[c_20,c_1288])).

tff(c_12668,plain,(
    ! [A_23348,B_23349,D_23350,B_23351] :
      ( m1_subset_1('#skF_3'(A_23348,B_23349,D_23350,D_23350),u1_struct_0(A_23348))
      | r3_orders_2(A_23348,D_23350,'#skF_1'(A_23348,B_23351,k2_relat_1(u1_waybel_0(A_23348,B_23349))))
      | ~ r3_waybel_9(A_23348,B_23349,D_23350)
      | ~ m1_subset_1(D_23350,u1_struct_0(A_23348))
      | ~ v7_waybel_0(B_23349)
      | ~ v4_orders_2(B_23349)
      | v2_struct_0(B_23349)
      | ~ l1_waybel_9(A_23348)
      | ~ v1_compts_1(A_23348)
      | ~ v2_lattice3(A_23348)
      | ~ v1_lattice3(A_23348)
      | ~ v4_orders_2(A_23348)
      | ~ v3_orders_2(A_23348)
      | ~ v8_pre_topc(A_23348)
      | ~ v2_pre_topc(A_23348)
      | ~ l1_waybel_0(B_23349,A_23348)
      | ~ l1_struct_0(A_23348)
      | r1_yellow_0(A_23348,k2_relat_1(u1_waybel_0(A_23348,B_23349)))
      | ~ r2_lattice3(A_23348,k2_relat_1(u1_waybel_0(A_23348,B_23349)),B_23351)
      | ~ m1_subset_1(B_23351,u1_struct_0(A_23348))
      | ~ l1_orders_2(A_23348)
      | ~ v5_orders_2(A_23348) ) ),
    inference(resolution,[status(thm)],[c_22,c_12631])).

tff(c_865,plain,(
    ! [A_366,B_367,D_368,E_369] :
      ( ~ v5_pre_topc(k4_waybel_1(A_366,'#skF_3'(A_366,B_367,D_368,D_368)),A_366,A_366)
      | r3_orders_2(A_366,D_368,E_369)
      | ~ r2_lattice3(A_366,k2_relset_1(u1_struct_0(B_367),u1_struct_0(A_366),u1_waybel_0(A_366,B_367)),E_369)
      | ~ m1_subset_1(E_369,u1_struct_0(A_366))
      | ~ r3_waybel_9(A_366,B_367,D_368)
      | ~ m1_subset_1(D_368,u1_struct_0(A_366))
      | ~ l1_waybel_0(B_367,A_366)
      | ~ v7_waybel_0(B_367)
      | ~ v4_orders_2(B_367)
      | v2_struct_0(B_367)
      | ~ l1_waybel_9(A_366)
      | ~ v1_compts_1(A_366)
      | ~ v2_lattice3(A_366)
      | ~ v1_lattice3(A_366)
      | ~ v5_orders_2(A_366)
      | ~ v4_orders_2(A_366)
      | ~ v3_orders_2(A_366)
      | ~ v8_pre_topc(A_366)
      | ~ v2_pre_topc(A_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_868,plain,(
    ! [D_368,E_369,B_367] :
      ( r3_orders_2('#skF_4',D_368,E_369)
      | ~ r2_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_367),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_367)),E_369)
      | ~ m1_subset_1(E_369,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_367,D_368)
      | ~ m1_subset_1(D_368,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_367,'#skF_4')
      | ~ v7_waybel_0(B_367)
      | ~ v4_orders_2(B_367)
      | v2_struct_0(B_367)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4',B_367,D_368,D_368),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_58,c_865])).

tff(c_872,plain,(
    ! [D_370,E_371,B_372] :
      ( r3_orders_2('#skF_4',D_370,E_371)
      | ~ r2_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_372),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_372)),E_371)
      | ~ m1_subset_1(E_371,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_372,D_370)
      | ~ m1_subset_1(D_370,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_372,'#skF_4')
      | ~ v7_waybel_0(B_372)
      | ~ v4_orders_2(B_372)
      | v2_struct_0(B_372)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_372,D_370,D_370),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_868])).

tff(c_886,plain,(
    ! [D_370,E_371,B_149] :
      ( r3_orders_2('#skF_4',D_370,E_371)
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_149)),E_371)
      | ~ m1_subset_1(E_371,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_149,D_370)
      | ~ m1_subset_1(D_370,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_149,'#skF_4')
      | ~ v7_waybel_0(B_149)
      | ~ v4_orders_2(B_149)
      | v2_struct_0(B_149)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_149,D_370,D_370),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_149,'#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_872])).

tff(c_963,plain,(
    ! [D_383,E_384,B_385] :
      ( r3_orders_2('#skF_4',D_383,E_384)
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_385)),E_384)
      | ~ m1_subset_1(E_384,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_385,D_383)
      | ~ m1_subset_1(D_383,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_385)
      | ~ v4_orders_2(B_385)
      | v2_struct_0(B_385)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_385,D_383,D_383),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_385,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_886])).

tff(c_982,plain,(
    ! [D_383,B_24,B_385] :
      ( r3_orders_2('#skF_4',D_383,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_385))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_385))),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_385,D_383)
      | ~ m1_subset_1(D_383,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_385)
      | ~ v4_orders_2(B_385)
      | v2_struct_0(B_385)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_385,D_383,D_383),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_385,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_385)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_385)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_963])).

tff(c_1257,plain,(
    ! [D_434,B_435,B_436] :
      ( r3_orders_2('#skF_4',D_434,'#skF_1'('#skF_4',B_435,k2_relat_1(u1_waybel_0('#skF_4',B_436))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_435,k2_relat_1(u1_waybel_0('#skF_4',B_436))),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_436,D_434)
      | ~ m1_subset_1(D_434,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_436)
      | ~ v4_orders_2(B_436)
      | v2_struct_0(B_436)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_436,D_434,D_434),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_436,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_436)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_436)),B_435)
      | ~ m1_subset_1(B_435,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_982])).

tff(c_1263,plain,(
    ! [D_434,B_24,B_436] :
      ( r3_orders_2('#skF_4',D_434,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_436))))
      | ~ r3_waybel_9('#skF_4',B_436,D_434)
      | ~ m1_subset_1(D_434,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_436)
      | ~ v4_orders_2(B_436)
      | v2_struct_0(B_436)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_436,D_434,D_434),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_436,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_436)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_436)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_1257])).

tff(c_1269,plain,(
    ! [D_434,B_24,B_436] :
      ( r3_orders_2('#skF_4',D_434,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_436))))
      | ~ r3_waybel_9('#skF_4',B_436,D_434)
      | ~ m1_subset_1(D_434,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_436)
      | ~ v4_orders_2(B_436)
      | v2_struct_0(B_436)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_436,D_434,D_434),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_436,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_436)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_436)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_1263])).

tff(c_12683,plain,(
    ! [D_23350,B_24,B_23349,B_23351] :
      ( r3_orders_2('#skF_4',D_23350,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_23349))))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23349)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4'))
      | r3_orders_2('#skF_4',D_23350,'#skF_1'('#skF_4',B_23351,k2_relat_1(u1_waybel_0('#skF_4',B_23349))))
      | ~ r3_waybel_9('#skF_4',B_23349,D_23350)
      | ~ m1_subset_1(D_23350,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_23349)
      | ~ v4_orders_2(B_23349)
      | v2_struct_0(B_23349)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_waybel_0(B_23349,'#skF_4')
      | ~ l1_struct_0('#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23349)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23349)),B_23351)
      | ~ m1_subset_1(B_23351,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12668,c_1269])).

tff(c_12757,plain,(
    ! [D_23350,B_24,B_23349,B_23351] :
      ( r3_orders_2('#skF_4',D_23350,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_23349))))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23349)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4'))
      | r3_orders_2('#skF_4',D_23350,'#skF_1'('#skF_4',B_23351,k2_relat_1(u1_waybel_0('#skF_4',B_23349))))
      | ~ r3_waybel_9('#skF_4',B_23349,D_23350)
      | ~ m1_subset_1(D_23350,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_23349)
      | ~ v4_orders_2(B_23349)
      | v2_struct_0(B_23349)
      | ~ l1_waybel_0(B_23349,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23349)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23349)),B_23351)
      | ~ m1_subset_1(B_23351,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_738,c_86,c_84,c_82,c_80,c_76,c_74,c_72,c_70,c_12683])).

tff(c_12971,plain,(
    ! [B_23803,D_23804,B_23805] :
      ( ~ r3_waybel_9('#skF_4',B_23803,D_23804)
      | ~ m1_subset_1(D_23804,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_23803)
      | ~ v4_orders_2(B_23803)
      | v2_struct_0(B_23803)
      | ~ l1_waybel_0(B_23803,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23803)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23803)),B_23805)
      | ~ m1_subset_1(B_23805,u1_struct_0('#skF_4'))
      | r3_orders_2('#skF_4',D_23804,'#skF_1'('#skF_4',B_23805,k2_relat_1(u1_waybel_0('#skF_4',B_23803)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12757])).

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

tff(c_12973,plain,(
    ! [D_23804,B_23805,B_23803] :
      ( r1_orders_2('#skF_4',D_23804,'#skF_1'('#skF_4',B_23805,k2_relat_1(u1_waybel_0('#skF_4',B_23803))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_23805,k2_relat_1(u1_waybel_0('#skF_4',B_23803))),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_23803,D_23804)
      | ~ m1_subset_1(D_23804,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_23803)
      | ~ v4_orders_2(B_23803)
      | v2_struct_0(B_23803)
      | ~ l1_waybel_0(B_23803,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23803)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23803)),B_23805)
      | ~ m1_subset_1(B_23805,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_12971,c_10])).

tff(c_12997,plain,(
    ! [D_23804,B_23805,B_23803] :
      ( r1_orders_2('#skF_4',D_23804,'#skF_1'('#skF_4',B_23805,k2_relat_1(u1_waybel_0('#skF_4',B_23803))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_23805,k2_relat_1(u1_waybel_0('#skF_4',B_23803))),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_23803,D_23804)
      | ~ m1_subset_1(D_23804,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_23803)
      | ~ v4_orders_2(B_23803)
      | v2_struct_0(B_23803)
      | ~ l1_waybel_0(B_23803,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23803)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23803)),B_23805)
      | ~ m1_subset_1(B_23805,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_92,c_12973])).

tff(c_12999,plain,(
    ! [D_23893,B_23894,B_23895] :
      ( r1_orders_2('#skF_4',D_23893,'#skF_1'('#skF_4',B_23894,k2_relat_1(u1_waybel_0('#skF_4',B_23895))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_23894,k2_relat_1(u1_waybel_0('#skF_4',B_23895))),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_23895,D_23893)
      | ~ m1_subset_1(D_23893,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_23895)
      | ~ v4_orders_2(B_23895)
      | v2_struct_0(B_23895)
      | ~ l1_waybel_0(B_23895,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23895)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23895)),B_23894)
      | ~ m1_subset_1(B_23894,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_12997])).

tff(c_13026,plain,(
    ! [D_23893,B_24,B_23895] :
      ( r1_orders_2('#skF_4',D_23893,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_23895))))
      | ~ r3_waybel_9('#skF_4',B_23895,D_23893)
      | ~ m1_subset_1(D_23893,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_23895)
      | ~ v4_orders_2(B_23895)
      | v2_struct_0(B_23895)
      | ~ l1_waybel_0(B_23895,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23895)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23895)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_12999])).

tff(c_13033,plain,(
    ! [D_23983,B_23984,B_23985] :
      ( r1_orders_2('#skF_4',D_23983,'#skF_1'('#skF_4',B_23984,k2_relat_1(u1_waybel_0('#skF_4',B_23985))))
      | ~ r3_waybel_9('#skF_4',B_23985,D_23983)
      | ~ m1_subset_1(D_23983,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_23985)
      | ~ v4_orders_2(B_23985)
      | v2_struct_0(B_23985)
      | ~ l1_waybel_0(B_23985,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23985)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23985)),B_23984)
      | ~ m1_subset_1(B_23984,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_13026])).

tff(c_18,plain,(
    ! [A_12,B_24,C_30] :
      ( ~ r1_orders_2(A_12,B_24,'#skF_1'(A_12,B_24,C_30))
      | r1_yellow_0(A_12,C_30)
      | ~ r2_lattice3(A_12,C_30,B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_13041,plain,(
    ! [B_23985,B_23984] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_23985,B_23984)
      | ~ v7_waybel_0(B_23985)
      | ~ v4_orders_2(B_23985)
      | v2_struct_0(B_23985)
      | ~ l1_waybel_0(B_23985,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23985)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_23985)),B_23984)
      | ~ m1_subset_1(B_23984,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_13033,c_18])).

tff(c_13069,plain,(
    ! [B_24073,B_24074] :
      ( ~ r3_waybel_9('#skF_4',B_24073,B_24074)
      | ~ v7_waybel_0(B_24073)
      | ~ v4_orders_2(B_24073)
      | v2_struct_0(B_24073)
      | ~ l1_waybel_0(B_24073,'#skF_4')
      | r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_24073)))
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_24073)),B_24074)
      | ~ m1_subset_1(B_24074,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_13041])).

tff(c_13169,plain,(
    ! [B_24162,D_24163] :
      ( r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_24162)))
      | ~ r3_waybel_9('#skF_4',B_24162,D_24163)
      | ~ v10_waybel_0(B_24162,'#skF_4')
      | ~ m1_subset_1(D_24163,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_24162)
      | ~ v4_orders_2(B_24162)
      | v2_struct_0(B_24162)
      | ~ l1_waybel_0(B_24162,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_737,c_13069])).

tff(c_13171,plain,
    ( r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6')))
    | ~ v10_waybel_0('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_waybel_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_13169])).

tff(c_13174,plain,
    ( r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_62,c_68,c_56,c_13171])).

tff(c_13175,plain,(
    r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_13174])).

tff(c_36,plain,(
    ! [A_36,B_38] :
      ( k4_yellow_2(A_36,u1_waybel_0(A_36,B_38)) = k1_waybel_2(A_36,B_38)
      | ~ l1_waybel_0(B_38,A_36)
      | ~ l1_orders_2(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_739,plain,(
    ! [B_338,D_339] :
      ( r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_338)),D_339)
      | ~ r3_waybel_9('#skF_4',B_338,D_339)
      | ~ v10_waybel_0(B_338,'#skF_4')
      | ~ m1_subset_1(D_339,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_338,'#skF_4')
      | ~ v7_waybel_0(B_338)
      | ~ v4_orders_2(B_338)
      | v2_struct_0(B_338)
      | ~ l1_waybel_0(B_338,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_38,plain,(
    ! [A_39,B_41] :
      ( k1_yellow_0(A_39,k2_relat_1(B_41)) = k4_yellow_2(A_39,B_41)
      | ~ v1_relat_1(B_41)
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_612,plain,(
    ! [A_295,C_296,D_297] :
      ( r1_orders_2(A_295,k1_yellow_0(A_295,C_296),D_297)
      | ~ r2_lattice3(A_295,C_296,D_297)
      | ~ m1_subset_1(D_297,u1_struct_0(A_295))
      | ~ r1_yellow_0(A_295,C_296)
      | ~ m1_subset_1(k1_yellow_0(A_295,C_296),u1_struct_0(A_295))
      | ~ l1_orders_2(A_295)
      | ~ v5_orders_2(A_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_623,plain,(
    ! [A_302,B_303,D_304] :
      ( r1_orders_2(A_302,k1_yellow_0(A_302,k2_relat_1(B_303)),D_304)
      | ~ r2_lattice3(A_302,k2_relat_1(B_303),D_304)
      | ~ m1_subset_1(D_304,u1_struct_0(A_302))
      | ~ r1_yellow_0(A_302,k2_relat_1(B_303))
      | ~ m1_subset_1(k4_yellow_2(A_302,B_303),u1_struct_0(A_302))
      | ~ l1_orders_2(A_302)
      | ~ v5_orders_2(A_302)
      | ~ v1_relat_1(B_303)
      | ~ l1_orders_2(A_302)
      | v2_struct_0(A_302) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_612])).

tff(c_634,plain,(
    ! [A_39,B_41,D_304] :
      ( r1_orders_2(A_39,k4_yellow_2(A_39,B_41),D_304)
      | ~ r2_lattice3(A_39,k2_relat_1(B_41),D_304)
      | ~ m1_subset_1(D_304,u1_struct_0(A_39))
      | ~ r1_yellow_0(A_39,k2_relat_1(B_41))
      | ~ m1_subset_1(k4_yellow_2(A_39,B_41),u1_struct_0(A_39))
      | ~ l1_orders_2(A_39)
      | ~ v5_orders_2(A_39)
      | ~ v1_relat_1(B_41)
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39)
      | ~ v1_relat_1(B_41)
      | ~ l1_orders_2(A_39)
      | v2_struct_0(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_623])).

tff(c_741,plain,(
    ! [B_338,D_339] :
      ( r1_orders_2('#skF_4',k4_yellow_2('#skF_4',u1_waybel_0('#skF_4',B_338)),D_339)
      | ~ r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_338)))
      | ~ m1_subset_1(k4_yellow_2('#skF_4',u1_waybel_0('#skF_4',B_338)),u1_struct_0('#skF_4'))
      | ~ v5_orders_2('#skF_4')
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_338))
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_338,D_339)
      | ~ v10_waybel_0(B_338,'#skF_4')
      | ~ m1_subset_1(D_339,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_338)
      | ~ v4_orders_2(B_338)
      | v2_struct_0(B_338)
      | ~ l1_waybel_0(B_338,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_739,c_634])).

tff(c_744,plain,(
    ! [B_338,D_339] :
      ( r1_orders_2('#skF_4',k4_yellow_2('#skF_4',u1_waybel_0('#skF_4',B_338)),D_339)
      | ~ r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_338)))
      | ~ m1_subset_1(k4_yellow_2('#skF_4',u1_waybel_0('#skF_4',B_338)),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_338))
      | v2_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_338,D_339)
      | ~ v10_waybel_0(B_338,'#skF_4')
      | ~ m1_subset_1(D_339,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_338)
      | ~ v4_orders_2(B_338)
      | v2_struct_0(B_338)
      | ~ l1_waybel_0(B_338,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_78,c_741])).

tff(c_746,plain,(
    ! [B_340,D_341] :
      ( r1_orders_2('#skF_4',k4_yellow_2('#skF_4',u1_waybel_0('#skF_4',B_340)),D_341)
      | ~ r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_340)))
      | ~ m1_subset_1(k4_yellow_2('#skF_4',u1_waybel_0('#skF_4',B_340)),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_340))
      | ~ r3_waybel_9('#skF_4',B_340,D_341)
      | ~ v10_waybel_0(B_340,'#skF_4')
      | ~ m1_subset_1(D_341,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_340)
      | ~ v4_orders_2(B_340)
      | v2_struct_0(B_340)
      | ~ l1_waybel_0(B_340,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_744])).

tff(c_749,plain,(
    ! [B_38,D_341] :
      ( r1_orders_2('#skF_4',k4_yellow_2('#skF_4',u1_waybel_0('#skF_4',B_38)),D_341)
      | ~ r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_38)))
      | ~ m1_subset_1(k1_waybel_2('#skF_4',B_38),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_38))
      | ~ r3_waybel_9('#skF_4',B_38,D_341)
      | ~ v10_waybel_0(B_38,'#skF_4')
      | ~ m1_subset_1(D_341,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_38)
      | ~ v4_orders_2(B_38)
      | v2_struct_0(B_38)
      | ~ l1_waybel_0(B_38,'#skF_4')
      | ~ l1_waybel_0(B_38,'#skF_4')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_746])).

tff(c_751,plain,(
    ! [B_38,D_341] :
      ( r1_orders_2('#skF_4',k4_yellow_2('#skF_4',u1_waybel_0('#skF_4',B_38)),D_341)
      | ~ r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_38)))
      | ~ m1_subset_1(k1_waybel_2('#skF_4',B_38),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_38))
      | ~ r3_waybel_9('#skF_4',B_38,D_341)
      | ~ v10_waybel_0(B_38,'#skF_4')
      | ~ m1_subset_1(D_341,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_38)
      | ~ v4_orders_2(B_38)
      | v2_struct_0(B_38)
      | ~ l1_waybel_0(B_38,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_749])).

tff(c_753,plain,(
    ! [B_342,D_343] :
      ( r1_orders_2('#skF_4',k4_yellow_2('#skF_4',u1_waybel_0('#skF_4',B_342)),D_343)
      | ~ r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_342)))
      | ~ m1_subset_1(k1_waybel_2('#skF_4',B_342),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_342))
      | ~ r3_waybel_9('#skF_4',B_342,D_343)
      | ~ v10_waybel_0(B_342,'#skF_4')
      | ~ m1_subset_1(D_343,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_342)
      | ~ v4_orders_2(B_342)
      | v2_struct_0(B_342)
      | ~ l1_waybel_0(B_342,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_751])).

tff(c_765,plain,(
    ! [B_38,D_343] :
      ( r1_orders_2('#skF_4',k1_waybel_2('#skF_4',B_38),D_343)
      | ~ r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_38)))
      | ~ m1_subset_1(k1_waybel_2('#skF_4',B_38),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_38))
      | ~ r3_waybel_9('#skF_4',B_38,D_343)
      | ~ v10_waybel_0(B_38,'#skF_4')
      | ~ m1_subset_1(D_343,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_38)
      | ~ v4_orders_2(B_38)
      | v2_struct_0(B_38)
      | ~ l1_waybel_0(B_38,'#skF_4')
      | ~ l1_waybel_0(B_38,'#skF_4')
      | ~ l1_orders_2('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_753])).

tff(c_773,plain,(
    ! [B_38,D_343] :
      ( r1_orders_2('#skF_4',k1_waybel_2('#skF_4',B_38),D_343)
      | ~ r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_38)))
      | ~ m1_subset_1(k1_waybel_2('#skF_4',B_38),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_38))
      | ~ r3_waybel_9('#skF_4',B_38,D_343)
      | ~ v10_waybel_0(B_38,'#skF_4')
      | ~ m1_subset_1(D_343,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_38)
      | ~ v4_orders_2(B_38)
      | v2_struct_0(B_38)
      | ~ l1_waybel_0(B_38,'#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_765])).

tff(c_774,plain,(
    ! [B_38,D_343] :
      ( r1_orders_2('#skF_4',k1_waybel_2('#skF_4',B_38),D_343)
      | ~ r1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_38)))
      | ~ m1_subset_1(k1_waybel_2('#skF_4',B_38),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4',B_38))
      | ~ r3_waybel_9('#skF_4',B_38,D_343)
      | ~ v10_waybel_0(B_38,'#skF_4')
      | ~ m1_subset_1(D_343,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_38)
      | ~ v4_orders_2(B_38)
      | v2_struct_0(B_38)
      | ~ l1_waybel_0(B_38,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_773])).

tff(c_13215,plain,(
    ! [D_343] :
      ( r1_orders_2('#skF_4',k1_waybel_2('#skF_4','#skF_6'),D_343)
      | ~ m1_subset_1(k1_waybel_2('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6'))
      | ~ r3_waybel_9('#skF_4','#skF_6',D_343)
      | ~ v10_waybel_0('#skF_6','#skF_4')
      | ~ m1_subset_1(D_343,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0('#skF_6','#skF_4') ) ),
    inference(resolution,[status(thm)],[c_13175,c_774])).

tff(c_13286,plain,(
    ! [D_343] :
      ( r1_orders_2('#skF_4',k1_waybel_2('#skF_4','#skF_6'),D_343)
      | ~ m1_subset_1(k1_waybel_2('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6'))
      | ~ r3_waybel_9('#skF_4','#skF_6',D_343)
      | ~ m1_subset_1(D_343,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_62,c_56,c_13215])).

tff(c_13287,plain,(
    ! [D_343] :
      ( r1_orders_2('#skF_4',k1_waybel_2('#skF_4','#skF_6'),D_343)
      | ~ m1_subset_1(k1_waybel_2('#skF_4','#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6'))
      | ~ r3_waybel_9('#skF_4','#skF_6',D_343)
      | ~ m1_subset_1(D_343,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_13286])).

tff(c_13288,plain,(
    ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_13287])).

tff(c_13291,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_4')
    | ~ l1_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_121,c_13288])).

tff(c_13295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_60,c_13291])).

tff(c_13297,plain,(
    v1_relat_1(u1_waybel_0('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_13287])).

tff(c_28,plain,(
    ! [A_12,B_24,C_30] :
      ( m1_subset_1('#skF_1'(A_12,B_24,C_30),u1_struct_0(A_12))
      | k1_yellow_0(A_12,C_30) = B_24
      | ~ r2_lattice3(A_12,C_30,B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_723,plain,(
    ! [B_59,D_71] :
      ( r2_lattice3('#skF_4',k2_relset_1(u1_struct_0(B_59),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_59)),D_71)
      | ~ r3_waybel_9('#skF_4',B_59,D_71)
      | ~ v10_waybel_0(B_59,'#skF_4')
      | ~ m1_subset_1(D_71,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_59,'#skF_4')
      | ~ v7_waybel_0(B_59)
      | ~ v4_orders_2(B_59)
      | v2_struct_0(B_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_720])).

tff(c_26,plain,(
    ! [A_12,C_30,B_24] :
      ( r2_lattice3(A_12,C_30,'#skF_1'(A_12,B_24,C_30))
      | k1_yellow_0(A_12,C_30) = B_24
      | ~ r2_lattice3(A_12,C_30,B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1380,plain,(
    ! [A_463,B_464,D_465,B_466] :
      ( m1_subset_1('#skF_3'(A_463,B_464,D_465,D_465),u1_struct_0(A_463))
      | r3_orders_2(A_463,D_465,'#skF_1'(A_463,B_466,k2_relset_1(u1_struct_0(B_464),u1_struct_0(A_463),u1_waybel_0(A_463,B_464))))
      | ~ m1_subset_1('#skF_1'(A_463,B_466,k2_relset_1(u1_struct_0(B_464),u1_struct_0(A_463),u1_waybel_0(A_463,B_464))),u1_struct_0(A_463))
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
      | k1_yellow_0(A_463,k2_relset_1(u1_struct_0(B_464),u1_struct_0(A_463),u1_waybel_0(A_463,B_464))) = B_466
      | ~ r2_lattice3(A_463,k2_relset_1(u1_struct_0(B_464),u1_struct_0(A_463),u1_waybel_0(A_463,B_464)),B_466)
      | ~ m1_subset_1(B_466,u1_struct_0(A_463))
      | ~ l1_orders_2(A_463)
      | ~ v5_orders_2(A_463) ) ),
    inference(resolution,[status(thm)],[c_26,c_776])).

tff(c_2716,plain,(
    ! [A_718,B_719,D_720,B_721] :
      ( m1_subset_1('#skF_3'(A_718,B_719,D_720,D_720),u1_struct_0(A_718))
      | r3_orders_2(A_718,D_720,'#skF_1'(A_718,B_721,k2_relset_1(u1_struct_0(B_719),u1_struct_0(A_718),u1_waybel_0(A_718,B_719))))
      | ~ r3_waybel_9(A_718,B_719,D_720)
      | ~ m1_subset_1(D_720,u1_struct_0(A_718))
      | ~ l1_waybel_0(B_719,A_718)
      | ~ v7_waybel_0(B_719)
      | ~ v4_orders_2(B_719)
      | v2_struct_0(B_719)
      | ~ l1_waybel_9(A_718)
      | ~ v1_compts_1(A_718)
      | ~ v2_lattice3(A_718)
      | ~ v1_lattice3(A_718)
      | ~ v4_orders_2(A_718)
      | ~ v3_orders_2(A_718)
      | ~ v8_pre_topc(A_718)
      | ~ v2_pre_topc(A_718)
      | k1_yellow_0(A_718,k2_relset_1(u1_struct_0(B_719),u1_struct_0(A_718),u1_waybel_0(A_718,B_719))) = B_721
      | ~ r2_lattice3(A_718,k2_relset_1(u1_struct_0(B_719),u1_struct_0(A_718),u1_waybel_0(A_718,B_719)),B_721)
      | ~ m1_subset_1(B_721,u1_struct_0(A_718))
      | ~ l1_orders_2(A_718)
      | ~ v5_orders_2(A_718) ) ),
    inference(resolution,[status(thm)],[c_28,c_1380])).

tff(c_13717,plain,(
    ! [A_25406,B_25407,D_25408,B_25409] :
      ( m1_subset_1('#skF_3'(A_25406,B_25407,D_25408,D_25408),u1_struct_0(A_25406))
      | r3_orders_2(A_25406,D_25408,'#skF_1'(A_25406,B_25409,k2_relat_1(u1_waybel_0(A_25406,B_25407))))
      | ~ r3_waybel_9(A_25406,B_25407,D_25408)
      | ~ m1_subset_1(D_25408,u1_struct_0(A_25406))
      | ~ l1_waybel_0(B_25407,A_25406)
      | ~ v7_waybel_0(B_25407)
      | ~ v4_orders_2(B_25407)
      | v2_struct_0(B_25407)
      | ~ l1_waybel_9(A_25406)
      | ~ v1_compts_1(A_25406)
      | ~ v2_lattice3(A_25406)
      | ~ v1_lattice3(A_25406)
      | ~ v4_orders_2(A_25406)
      | ~ v3_orders_2(A_25406)
      | ~ v8_pre_topc(A_25406)
      | ~ v2_pre_topc(A_25406)
      | k1_yellow_0(A_25406,k2_relset_1(u1_struct_0(B_25407),u1_struct_0(A_25406),u1_waybel_0(A_25406,B_25407))) = B_25409
      | ~ r2_lattice3(A_25406,k2_relset_1(u1_struct_0(B_25407),u1_struct_0(A_25406),u1_waybel_0(A_25406,B_25407)),B_25409)
      | ~ m1_subset_1(B_25409,u1_struct_0(A_25406))
      | ~ l1_orders_2(A_25406)
      | ~ v5_orders_2(A_25406)
      | ~ l1_waybel_0(B_25407,A_25406)
      | ~ l1_struct_0(A_25406) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_2716])).

tff(c_13797,plain,(
    ! [B_59,D_25408,D_71] :
      ( m1_subset_1('#skF_3'('#skF_4',B_59,D_25408,D_25408),u1_struct_0('#skF_4'))
      | r3_orders_2('#skF_4',D_25408,'#skF_1'('#skF_4',D_71,k2_relat_1(u1_waybel_0('#skF_4',B_59))))
      | ~ r3_waybel_9('#skF_4',B_59,D_25408)
      | ~ m1_subset_1(D_25408,u1_struct_0('#skF_4'))
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | k1_yellow_0('#skF_4',k2_relset_1(u1_struct_0(B_59),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_59))) = D_71
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ l1_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_59,D_71)
      | ~ v10_waybel_0(B_59,'#skF_4')
      | ~ m1_subset_1(D_71,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_59,'#skF_4')
      | ~ v7_waybel_0(B_59)
      | ~ v4_orders_2(B_59)
      | v2_struct_0(B_59) ) ),
    inference(resolution,[status(thm)],[c_723,c_13717])).

tff(c_13815,plain,(
    ! [B_25497,D_25498,D_25499] :
      ( m1_subset_1('#skF_3'('#skF_4',B_25497,D_25498,D_25498),u1_struct_0('#skF_4'))
      | r3_orders_2('#skF_4',D_25498,'#skF_1'('#skF_4',D_25499,k2_relat_1(u1_waybel_0('#skF_4',B_25497))))
      | ~ r3_waybel_9('#skF_4',B_25497,D_25498)
      | ~ m1_subset_1(D_25498,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relset_1(u1_struct_0(B_25497),u1_struct_0('#skF_4'),u1_waybel_0('#skF_4',B_25497))) = D_25499
      | ~ r3_waybel_9('#skF_4',B_25497,D_25499)
      | ~ v10_waybel_0(B_25497,'#skF_4')
      | ~ m1_subset_1(D_25499,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_25497,'#skF_4')
      | ~ v7_waybel_0(B_25497)
      | ~ v4_orders_2(B_25497)
      | v2_struct_0(B_25497) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_78,c_92,c_86,c_84,c_82,c_80,c_76,c_74,c_72,c_70,c_13797])).

tff(c_17323,plain,(
    ! [B_149,D_25498,D_25499] :
      ( m1_subset_1('#skF_3'('#skF_4',B_149,D_25498,D_25498),u1_struct_0('#skF_4'))
      | r3_orders_2('#skF_4',D_25498,'#skF_1'('#skF_4',D_25499,k2_relat_1(u1_waybel_0('#skF_4',B_149))))
      | ~ r3_waybel_9('#skF_4',B_149,D_25498)
      | ~ m1_subset_1(D_25498,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_149))) = D_25499
      | ~ r3_waybel_9('#skF_4',B_149,D_25499)
      | ~ v10_waybel_0(B_149,'#skF_4')
      | ~ m1_subset_1(D_25499,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_149,'#skF_4')
      | ~ v7_waybel_0(B_149)
      | ~ v4_orders_2(B_149)
      | v2_struct_0(B_149)
      | ~ l1_waybel_0(B_149,'#skF_4')
      | ~ l1_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_13815])).

tff(c_17364,plain,(
    ! [B_33127,D_33128,D_33129] :
      ( m1_subset_1('#skF_3'('#skF_4',B_33127,D_33128,D_33128),u1_struct_0('#skF_4'))
      | r3_orders_2('#skF_4',D_33128,'#skF_1'('#skF_4',D_33129,k2_relat_1(u1_waybel_0('#skF_4',B_33127))))
      | ~ r3_waybel_9('#skF_4',B_33127,D_33128)
      | ~ m1_subset_1(D_33128,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33127))) = D_33129
      | ~ r3_waybel_9('#skF_4',B_33127,D_33129)
      | ~ v10_waybel_0(B_33127,'#skF_4')
      | ~ m1_subset_1(D_33129,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_33127)
      | ~ v4_orders_2(B_33127)
      | v2_struct_0(B_33127)
      | ~ l1_waybel_0(B_33127,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_738,c_17323])).

tff(c_17390,plain,(
    ! [D_33128,D_33129,B_33127] :
      ( r1_orders_2('#skF_4',D_33128,'#skF_1'('#skF_4',D_33129,k2_relat_1(u1_waybel_0('#skF_4',B_33127))))
      | ~ m1_subset_1('#skF_1'('#skF_4',D_33129,k2_relat_1(u1_waybel_0('#skF_4',B_33127))),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | m1_subset_1('#skF_3'('#skF_4',B_33127,D_33128,D_33128),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_33127,D_33128)
      | ~ m1_subset_1(D_33128,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33127))) = D_33129
      | ~ r3_waybel_9('#skF_4',B_33127,D_33129)
      | ~ v10_waybel_0(B_33127,'#skF_4')
      | ~ m1_subset_1(D_33129,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_33127)
      | ~ v4_orders_2(B_33127)
      | v2_struct_0(B_33127)
      | ~ l1_waybel_0(B_33127,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_17364,c_10])).

tff(c_17511,plain,(
    ! [D_33128,D_33129,B_33127] :
      ( r1_orders_2('#skF_4',D_33128,'#skF_1'('#skF_4',D_33129,k2_relat_1(u1_waybel_0('#skF_4',B_33127))))
      | ~ m1_subset_1('#skF_1'('#skF_4',D_33129,k2_relat_1(u1_waybel_0('#skF_4',B_33127))),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | m1_subset_1('#skF_3'('#skF_4',B_33127,D_33128,D_33128),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_33127,D_33128)
      | ~ m1_subset_1(D_33128,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33127))) = D_33129
      | ~ r3_waybel_9('#skF_4',B_33127,D_33129)
      | ~ v10_waybel_0(B_33127,'#skF_4')
      | ~ m1_subset_1(D_33129,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_33127)
      | ~ v4_orders_2(B_33127)
      | v2_struct_0(B_33127)
      | ~ l1_waybel_0(B_33127,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_92,c_17390])).

tff(c_18133,plain,(
    ! [D_33724,D_33725,B_33726] :
      ( r1_orders_2('#skF_4',D_33724,'#skF_1'('#skF_4',D_33725,k2_relat_1(u1_waybel_0('#skF_4',B_33726))))
      | ~ m1_subset_1('#skF_1'('#skF_4',D_33725,k2_relat_1(u1_waybel_0('#skF_4',B_33726))),u1_struct_0('#skF_4'))
      | m1_subset_1('#skF_3'('#skF_4',B_33726,D_33724,D_33724),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_33726,D_33724)
      | ~ m1_subset_1(D_33724,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33726))) = D_33725
      | ~ r3_waybel_9('#skF_4',B_33726,D_33725)
      | ~ v10_waybel_0(B_33726,'#skF_4')
      | ~ m1_subset_1(D_33725,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_33726)
      | ~ v4_orders_2(B_33726)
      | v2_struct_0(B_33726)
      | ~ l1_waybel_0(B_33726,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_17511])).

tff(c_18230,plain,(
    ! [D_33724,B_24,B_33726] :
      ( r1_orders_2('#skF_4',D_33724,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_33726))))
      | m1_subset_1('#skF_3'('#skF_4',B_33726,D_33724,D_33724),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_33726,D_33724)
      | ~ m1_subset_1(D_33724,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_33726,B_24)
      | ~ v10_waybel_0(B_33726,'#skF_4')
      | ~ v7_waybel_0(B_33726)
      | ~ v4_orders_2(B_33726)
      | v2_struct_0(B_33726)
      | ~ l1_waybel_0(B_33726,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33726))) = B_24
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33726)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_18133])).

tff(c_18240,plain,(
    ! [D_33843,B_33844,B_33845] :
      ( r1_orders_2('#skF_4',D_33843,'#skF_1'('#skF_4',B_33844,k2_relat_1(u1_waybel_0('#skF_4',B_33845))))
      | m1_subset_1('#skF_3'('#skF_4',B_33845,D_33843,D_33843),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_33845,D_33843)
      | ~ m1_subset_1(D_33843,u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_33845,B_33844)
      | ~ v10_waybel_0(B_33845,'#skF_4')
      | ~ v7_waybel_0(B_33845)
      | ~ v4_orders_2(B_33845)
      | v2_struct_0(B_33845)
      | ~ l1_waybel_0(B_33845,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33845))) = B_33844
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33845)),B_33844)
      | ~ m1_subset_1(B_33844,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_18230])).

tff(c_24,plain,(
    ! [A_12,B_24,C_30] :
      ( ~ r1_orders_2(A_12,B_24,'#skF_1'(A_12,B_24,C_30))
      | k1_yellow_0(A_12,C_30) = B_24
      | ~ r2_lattice3(A_12,C_30,B_24)
      | ~ m1_subset_1(B_24,u1_struct_0(A_12))
      | ~ l1_orders_2(A_12)
      | ~ v5_orders_2(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18244,plain,(
    ! [B_33845,B_33844] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | m1_subset_1('#skF_3'('#skF_4',B_33845,B_33844,B_33844),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_33845,B_33844)
      | ~ v10_waybel_0(B_33845,'#skF_4')
      | ~ v7_waybel_0(B_33845)
      | ~ v4_orders_2(B_33845)
      | v2_struct_0(B_33845)
      | ~ l1_waybel_0(B_33845,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33845))) = B_33844
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33845)),B_33844)
      | ~ m1_subset_1(B_33844,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18240,c_24])).

tff(c_18397,plain,(
    ! [B_33962,B_33963] :
      ( m1_subset_1('#skF_3'('#skF_4',B_33962,B_33963,B_33963),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_33962,B_33963)
      | ~ v10_waybel_0(B_33962,'#skF_4')
      | ~ v7_waybel_0(B_33962)
      | ~ v4_orders_2(B_33962)
      | v2_struct_0(B_33962)
      | ~ l1_waybel_0(B_33962,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33962))) = B_33963
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_33962)),B_33963)
      | ~ m1_subset_1(B_33963,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_18244])).

tff(c_18588,plain,(
    ! [B_34200,D_34201] :
      ( m1_subset_1('#skF_3'('#skF_4',B_34200,D_34201,D_34201),u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_34200))) = D_34201
      | ~ r3_waybel_9('#skF_4',B_34200,D_34201)
      | ~ v10_waybel_0(B_34200,'#skF_4')
      | ~ m1_subset_1(D_34201,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_34200)
      | ~ v4_orders_2(B_34200)
      | v2_struct_0(B_34200)
      | ~ l1_waybel_0(B_34200,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_737,c_18397])).

tff(c_979,plain,(
    ! [D_383,B_24,B_385] :
      ( r3_orders_2('#skF_4',D_383,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_385))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_385))),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_385,D_383)
      | ~ m1_subset_1(D_383,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_385)
      | ~ v4_orders_2(B_385)
      | v2_struct_0(B_385)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_385,D_383,D_383),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_385,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_385))) = B_24
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_385)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_963])).

tff(c_1322,plain,(
    ! [D_451,B_452,B_453] :
      ( r3_orders_2('#skF_4',D_451,'#skF_1'('#skF_4',B_452,k2_relat_1(u1_waybel_0('#skF_4',B_453))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_452,k2_relat_1(u1_waybel_0('#skF_4',B_453))),u1_struct_0('#skF_4'))
      | ~ r3_waybel_9('#skF_4',B_453,D_451)
      | ~ m1_subset_1(D_451,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_453)
      | ~ v4_orders_2(B_453)
      | v2_struct_0(B_453)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_453,D_451,D_451),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_453,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_453))) = B_452
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_453)),B_452)
      | ~ m1_subset_1(B_452,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_979])).

tff(c_1325,plain,(
    ! [D_451,B_24,B_453] :
      ( r3_orders_2('#skF_4',D_451,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_453))))
      | ~ r3_waybel_9('#skF_4',B_453,D_451)
      | ~ m1_subset_1(D_451,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_453)
      | ~ v4_orders_2(B_453)
      | v2_struct_0(B_453)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_453,D_451,D_451),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_453,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_453))) = B_24
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_453)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_1322])).

tff(c_1331,plain,(
    ! [D_451,B_24,B_453] :
      ( r3_orders_2('#skF_4',D_451,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_453))))
      | ~ r3_waybel_9('#skF_4',B_453,D_451)
      | ~ m1_subset_1(D_451,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_453)
      | ~ v4_orders_2(B_453)
      | v2_struct_0(B_453)
      | ~ m1_subset_1('#skF_3'('#skF_4',B_453,D_451,D_451),u1_struct_0('#skF_4'))
      | ~ l1_waybel_0(B_453,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_453))) = B_24
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_453)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_1325])).

tff(c_22093,plain,(
    ! [D_43893,B_43894,B_43895] :
      ( r3_orders_2('#skF_4',D_43893,'#skF_1'('#skF_4',B_43894,k2_relat_1(u1_waybel_0('#skF_4',B_43895))))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_43895))) = B_43894
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_43895)),B_43894)
      | ~ m1_subset_1(B_43894,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_43895))) = D_43893
      | ~ r3_waybel_9('#skF_4',B_43895,D_43893)
      | ~ v10_waybel_0(B_43895,'#skF_4')
      | ~ m1_subset_1(D_43893,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_43895)
      | ~ v4_orders_2(B_43895)
      | v2_struct_0(B_43895)
      | ~ l1_waybel_0(B_43895,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18588,c_1331])).

tff(c_22095,plain,(
    ! [D_43893,B_43894,B_43895] :
      ( r1_orders_2('#skF_4',D_43893,'#skF_1'('#skF_4',B_43894,k2_relat_1(u1_waybel_0('#skF_4',B_43895))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_43894,k2_relat_1(u1_waybel_0('#skF_4',B_43895))),u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | v2_struct_0('#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_43895))) = B_43894
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_43895)),B_43894)
      | ~ m1_subset_1(B_43894,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_43895))) = D_43893
      | ~ r3_waybel_9('#skF_4',B_43895,D_43893)
      | ~ v10_waybel_0(B_43895,'#skF_4')
      | ~ m1_subset_1(D_43893,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_43895)
      | ~ v4_orders_2(B_43895)
      | v2_struct_0(B_43895)
      | ~ l1_waybel_0(B_43895,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22093,c_10])).

tff(c_22291,plain,(
    ! [D_43893,B_43894,B_43895] :
      ( r1_orders_2('#skF_4',D_43893,'#skF_1'('#skF_4',B_43894,k2_relat_1(u1_waybel_0('#skF_4',B_43895))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_43894,k2_relat_1(u1_waybel_0('#skF_4',B_43895))),u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_43895))) = B_43894
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_43895)),B_43894)
      | ~ m1_subset_1(B_43894,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_43895))) = D_43893
      | ~ r3_waybel_9('#skF_4',B_43895,D_43893)
      | ~ v10_waybel_0(B_43895,'#skF_4')
      | ~ m1_subset_1(D_43893,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_43895)
      | ~ v4_orders_2(B_43895)
      | v2_struct_0(B_43895)
      | ~ l1_waybel_0(B_43895,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_92,c_22095])).

tff(c_25344,plain,(
    ! [D_47147,B_47148,B_47149] :
      ( r1_orders_2('#skF_4',D_47147,'#skF_1'('#skF_4',B_47148,k2_relat_1(u1_waybel_0('#skF_4',B_47149))))
      | ~ m1_subset_1('#skF_1'('#skF_4',B_47148,k2_relat_1(u1_waybel_0('#skF_4',B_47149))),u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47149))) = B_47148
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47149)),B_47148)
      | ~ m1_subset_1(B_47148,u1_struct_0('#skF_4'))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47149))) = D_47147
      | ~ r3_waybel_9('#skF_4',B_47149,D_47147)
      | ~ v10_waybel_0(B_47149,'#skF_4')
      | ~ m1_subset_1(D_47147,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_47149)
      | ~ v4_orders_2(B_47149)
      | v2_struct_0(B_47149)
      | ~ l1_waybel_0(B_47149,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_22291])).

tff(c_25540,plain,(
    ! [D_47147,B_24,B_47149] :
      ( r1_orders_2('#skF_4',D_47147,'#skF_1'('#skF_4',B_24,k2_relat_1(u1_waybel_0('#skF_4',B_47149))))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47149))) = D_47147
      | ~ r3_waybel_9('#skF_4',B_47149,D_47147)
      | ~ v10_waybel_0(B_47149,'#skF_4')
      | ~ m1_subset_1(D_47147,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_47149)
      | ~ v4_orders_2(B_47149)
      | v2_struct_0(B_47149)
      | ~ l1_waybel_0(B_47149,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47149))) = B_24
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47149)),B_24)
      | ~ m1_subset_1(B_24,u1_struct_0('#skF_4'))
      | ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_25344])).

tff(c_25550,plain,(
    ! [D_47295,B_47296,B_47297] :
      ( r1_orders_2('#skF_4',D_47295,'#skF_1'('#skF_4',B_47296,k2_relat_1(u1_waybel_0('#skF_4',B_47297))))
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47297))) = D_47295
      | ~ r3_waybel_9('#skF_4',B_47297,D_47295)
      | ~ v10_waybel_0(B_47297,'#skF_4')
      | ~ m1_subset_1(D_47295,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_47297)
      | ~ v4_orders_2(B_47297)
      | v2_struct_0(B_47297)
      | ~ l1_waybel_0(B_47297,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47297))) = B_47296
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47297)),B_47296)
      | ~ m1_subset_1(B_47296,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_25540])).

tff(c_25554,plain,(
    ! [B_47297,B_47296] :
      ( ~ l1_orders_2('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_47297,B_47296)
      | ~ v10_waybel_0(B_47297,'#skF_4')
      | ~ v7_waybel_0(B_47297)
      | ~ v4_orders_2(B_47297)
      | v2_struct_0(B_47297)
      | ~ l1_waybel_0(B_47297,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47297))) = B_47296
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47297)),B_47296)
      | ~ m1_subset_1(B_47296,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_25550,c_24])).

tff(c_26270,plain,(
    ! [B_47592,B_47593] :
      ( ~ r3_waybel_9('#skF_4',B_47592,B_47593)
      | ~ v10_waybel_0(B_47592,'#skF_4')
      | ~ v7_waybel_0(B_47592)
      | ~ v4_orders_2(B_47592)
      | v2_struct_0(B_47592)
      | ~ l1_waybel_0(B_47592,'#skF_4')
      | k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47592))) = B_47593
      | ~ r2_lattice3('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47592)),B_47593)
      | ~ m1_subset_1(B_47593,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_92,c_25554])).

tff(c_26479,plain,(
    ! [B_47739,D_47740] :
      ( k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4',B_47739))) = D_47740
      | ~ r3_waybel_9('#skF_4',B_47739,D_47740)
      | ~ v10_waybel_0(B_47739,'#skF_4')
      | ~ m1_subset_1(D_47740,u1_struct_0('#skF_4'))
      | ~ v7_waybel_0(B_47739)
      | ~ v4_orders_2(B_47739)
      | v2_struct_0(B_47739)
      | ~ l1_waybel_0(B_47739,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_737,c_26270])).

tff(c_26529,plain,
    ( k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) = '#skF_5'
    | ~ v10_waybel_0('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_waybel_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_26479])).

tff(c_26532,plain,
    ( k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) = '#skF_5'
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_64,c_62,c_68,c_56,c_26529])).

tff(c_26533,plain,(
    k1_yellow_0('#skF_4',k2_relat_1(u1_waybel_0('#skF_4','#skF_6'))) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_26532])).

tff(c_26579,plain,
    ( k4_yellow_2('#skF_4',u1_waybel_0('#skF_4','#skF_6')) = '#skF_5'
    | ~ v1_relat_1(u1_waybel_0('#skF_4','#skF_6'))
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26533,c_38])).

tff(c_26677,plain,
    ( k4_yellow_2('#skF_4',u1_waybel_0('#skF_4','#skF_6')) = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_13297,c_26579])).

tff(c_26678,plain,(
    k4_yellow_2('#skF_4',u1_waybel_0('#skF_4','#skF_6')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_26677])).

tff(c_26806,plain,
    ( k1_waybel_2('#skF_4','#skF_6') = '#skF_5'
    | ~ l1_waybel_0('#skF_6','#skF_4')
    | ~ l1_orders_2('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26678,c_36])).

tff(c_26948,plain,
    ( k1_waybel_2('#skF_4','#skF_6') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_60,c_26806])).

tff(c_26950,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_52,c_26948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:33:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.07/12.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.22/12.53  
% 23.22/12.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.22/12.53  %$ v5_pre_topc > v1_funct_2 > r3_waybel_9 > r3_orders_2 > r2_lattice3 > r1_orders_2 > v10_waybel_0 > r1_yellow_0 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_relat_1 > v1_lattice3 > v1_funct_1 > v1_compts_1 > l1_waybel_9 > l1_struct_0 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_yellow_2 > k4_waybel_1 > k2_zfmisc_1 > k1_yellow_0 > k1_waybel_2 > #nlpp > u1_struct_0 > k2_relat_1 > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 23.22/12.53  
% 23.22/12.53  %Foreground sorts:
% 23.22/12.53  
% 23.22/12.53  
% 23.22/12.53  %Background operators:
% 23.22/12.53  
% 23.22/12.53  
% 23.22/12.53  %Foreground operators:
% 23.22/12.53  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 23.22/12.53  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 23.22/12.53  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 23.22/12.53  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 23.22/12.53  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 23.22/12.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 23.22/12.53  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 23.22/12.53  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.22/12.53  tff(k4_yellow_2, type, k4_yellow_2: ($i * $i) > $i).
% 23.22/12.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.22/12.53  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 23.22/12.53  tff(v10_waybel_0, type, v10_waybel_0: ($i * $i) > $o).
% 23.22/12.53  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 23.22/12.53  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 23.22/12.53  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.22/12.53  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 23.22/12.53  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 23.22/12.53  tff('#skF_5', type, '#skF_5': $i).
% 23.22/12.53  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 23.22/12.53  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 23.22/12.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 23.22/12.53  tff('#skF_6', type, '#skF_6': $i).
% 23.22/12.53  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 23.22/12.53  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 23.22/12.53  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 23.22/12.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.22/12.53  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 23.22/12.53  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 23.22/12.53  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 23.22/12.53  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 23.22/12.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.22/12.53  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 23.22/12.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.22/12.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.22/12.53  tff('#skF_4', type, '#skF_4': $i).
% 23.22/12.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.22/12.53  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 23.22/12.53  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 23.22/12.53  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 23.22/12.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 23.22/12.53  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 23.22/12.53  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 23.22/12.53  tff(k1_waybel_2, type, k1_waybel_2: ($i * $i) > $i).
% 23.22/12.53  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 23.22/12.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.22/12.53  
% 23.22/12.57  tff(f_269, negated_conjecture, ~(![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => ((((![D]: (m1_subset_1(D, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, D), A, A))) & v10_waybel_0(C, A)) & r3_waybel_9(A, C, B)) => (B = k1_waybel_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_waybel_9)).
% 23.22/12.57  tff(f_129, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 23.22/12.57  tff(f_52, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 23.22/12.57  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 23.22/12.57  tff(f_37, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 23.22/12.57  tff(f_103, axiom, (![A, B]: ((l1_struct_0(A) & l1_waybel_0(B, A)) => ((v1_funct_1(u1_waybel_0(A, B)) & v1_funct_2(u1_waybel_0(A, B), u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(u1_waybel_0(A, B), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_waybel_0)).
% 23.22/12.57  tff(f_33, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 23.22/12.57  tff(f_176, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & v10_waybel_0(B, A)) & r3_waybel_9(A, B, C)) => r2_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l48_waybel_9)).
% 23.22/12.57  tff(f_29, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 23.22/12.57  tff(f_93, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 23.22/12.57  tff(f_226, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & r3_waybel_9(A, B, C)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r2_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), E) => r3_orders_2(A, D, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_waybel_9)).
% 23.22/12.57  tff(f_113, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (l1_waybel_0(B, A) => (k1_waybel_2(A, B) = k4_yellow_2(A, u1_waybel_0(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_waybel_2)).
% 23.22/12.57  tff(f_123, axiom, (![A]: ((~v2_struct_0(A) & l1_orders_2(A)) => (![B]: (v1_relat_1(B) => (k4_yellow_2(A, B) = k1_yellow_0(A, k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_yellow_2)).
% 23.22/12.57  tff(c_70, plain, (l1_waybel_9('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_88, plain, (![A_132]: (l1_orders_2(A_132) | ~l1_waybel_9(A_132))), inference(cnfTransformation, [status(thm)], [f_129])).
% 23.22/12.57  tff(c_92, plain, (l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_70, c_88])).
% 23.22/12.57  tff(c_76, plain, (v1_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_82, plain, (v3_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_68, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_145, plain, (![A_161, B_162, C_163]: (r3_orders_2(A_161, B_162, C_163) | ~r1_orders_2(A_161, B_162, C_163) | ~m1_subset_1(C_163, u1_struct_0(A_161)) | ~m1_subset_1(B_162, u1_struct_0(A_161)) | ~l1_orders_2(A_161) | ~v3_orders_2(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_52])).
% 23.22/12.57  tff(c_147, plain, (![B_162]: (r3_orders_2('#skF_4', B_162, '#skF_5') | ~r1_orders_2('#skF_4', B_162, '#skF_5') | ~m1_subset_1(B_162, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_145])).
% 23.22/12.57  tff(c_150, plain, (![B_162]: (r3_orders_2('#skF_4', B_162, '#skF_5') | ~r1_orders_2('#skF_4', B_162, '#skF_5') | ~m1_subset_1(B_162, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_92, c_147])).
% 23.22/12.57  tff(c_151, plain, (v2_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_150])).
% 23.22/12.57  tff(c_12, plain, (![A_11]: (~v2_struct_0(A_11) | ~v1_lattice3(A_11) | ~l1_orders_2(A_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.22/12.57  tff(c_154, plain, (~v1_lattice3('#skF_4') | ~l1_orders_2('#skF_4')), inference(resolution, [status(thm)], [c_151, c_12])).
% 23.22/12.57  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_76, c_154])).
% 23.22/12.57  tff(c_160, plain, (~v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_150])).
% 23.22/12.57  tff(c_52, plain, (k1_waybel_2('#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_60, plain, (l1_waybel_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_93, plain, (![A_133]: (l1_pre_topc(A_133) | ~l1_waybel_9(A_133))), inference(cnfTransformation, [status(thm)], [f_129])).
% 23.22/12.57  tff(c_97, plain, (l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_70, c_93])).
% 23.22/12.57  tff(c_6, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_pre_topc(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 23.22/12.57  tff(c_113, plain, (![A_148, B_149]: (m1_subset_1(u1_waybel_0(A_148, B_149), k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_149), u1_struct_0(A_148)))) | ~l1_waybel_0(B_149, A_148) | ~l1_struct_0(A_148))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.22/12.57  tff(c_4, plain, (![A_4, B_5, C_6]: (k2_relset_1(A_4, B_5, C_6)=k2_relat_1(C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(k2_zfmisc_1(A_4, B_5))))), inference(cnfTransformation, [status(thm)], [f_33])).
% 23.22/12.57  tff(c_120, plain, (![B_149, A_148]: (k2_relset_1(u1_struct_0(B_149), u1_struct_0(A_148), u1_waybel_0(A_148, B_149))=k2_relat_1(u1_waybel_0(A_148, B_149)) | ~l1_waybel_0(B_149, A_148) | ~l1_struct_0(A_148))), inference(resolution, [status(thm)], [c_113, c_4])).
% 23.22/12.57  tff(c_86, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_84, plain, (v8_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_80, plain, (v4_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_78, plain, (v5_orders_2('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_74, plain, (v2_lattice3('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_72, plain, (v1_compts_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_46, plain, (![A_43, B_59, D_71]: (m1_subset_1('#skF_2'(A_43, B_59, D_71, D_71), u1_struct_0(A_43)) | r2_lattice3(A_43, k2_relset_1(u1_struct_0(B_59), u1_struct_0(A_43), u1_waybel_0(A_43, B_59)), D_71) | ~r3_waybel_9(A_43, B_59, D_71) | ~v10_waybel_0(B_59, A_43) | ~m1_subset_1(D_71, u1_struct_0(A_43)) | ~l1_waybel_0(B_59, A_43) | ~v7_waybel_0(B_59) | ~v4_orders_2(B_59) | v2_struct_0(B_59) | ~l1_waybel_9(A_43) | ~v1_compts_1(A_43) | ~v2_lattice3(A_43) | ~v1_lattice3(A_43) | ~v5_orders_2(A_43) | ~v4_orders_2(A_43) | ~v3_orders_2(A_43) | ~v8_pre_topc(A_43) | ~v2_pre_topc(A_43))), inference(cnfTransformation, [status(thm)], [f_176])).
% 23.22/12.57  tff(c_58, plain, (![D_130]: (v5_pre_topc(k4_waybel_1('#skF_4', D_130), '#skF_4', '#skF_4') | ~m1_subset_1(D_130, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_710, plain, (![A_331, B_332, D_333]: (~v5_pre_topc(k4_waybel_1(A_331, '#skF_2'(A_331, B_332, D_333, D_333)), A_331, A_331) | r2_lattice3(A_331, k2_relset_1(u1_struct_0(B_332), u1_struct_0(A_331), u1_waybel_0(A_331, B_332)), D_333) | ~r3_waybel_9(A_331, B_332, D_333) | ~v10_waybel_0(B_332, A_331) | ~m1_subset_1(D_333, u1_struct_0(A_331)) | ~l1_waybel_0(B_332, A_331) | ~v7_waybel_0(B_332) | ~v4_orders_2(B_332) | v2_struct_0(B_332) | ~l1_waybel_9(A_331) | ~v1_compts_1(A_331) | ~v2_lattice3(A_331) | ~v1_lattice3(A_331) | ~v5_orders_2(A_331) | ~v4_orders_2(A_331) | ~v3_orders_2(A_331) | ~v8_pre_topc(A_331) | ~v2_pre_topc(A_331))), inference(cnfTransformation, [status(thm)], [f_176])).
% 23.22/12.57  tff(c_713, plain, (![B_332, D_333]: (r2_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_332), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_332)), D_333) | ~r3_waybel_9('#skF_4', B_332, D_333) | ~v10_waybel_0(B_332, '#skF_4') | ~m1_subset_1(D_333, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_332, '#skF_4') | ~v7_waybel_0(B_332) | ~v4_orders_2(B_332) | v2_struct_0(B_332) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_subset_1('#skF_2'('#skF_4', B_332, D_333, D_333), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_58, c_710])).
% 23.22/12.57  tff(c_717, plain, (![B_334, D_335]: (r2_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_334), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_334)), D_335) | ~r3_waybel_9('#skF_4', B_334, D_335) | ~v10_waybel_0(B_334, '#skF_4') | ~m1_subset_1(D_335, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_334, '#skF_4') | ~v7_waybel_0(B_334) | ~v4_orders_2(B_334) | v2_struct_0(B_334) | ~m1_subset_1('#skF_2'('#skF_4', B_334, D_335, D_335), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_713])).
% 23.22/12.57  tff(c_720, plain, (![B_59, D_71]: (r2_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_59), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_59)), D_71) | ~r3_waybel_9('#skF_4', B_59, D_71) | ~v10_waybel_0(B_59, '#skF_4') | ~m1_subset_1(D_71, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_59, '#skF_4') | ~v7_waybel_0(B_59) | ~v4_orders_2(B_59) | v2_struct_0(B_59) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_46, c_717])).
% 23.22/12.57  tff(c_724, plain, (![B_336, D_337]: (r2_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_336), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_336)), D_337) | ~r3_waybel_9('#skF_4', B_336, D_337) | ~v10_waybel_0(B_336, '#skF_4') | ~m1_subset_1(D_337, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_336, '#skF_4') | ~v7_waybel_0(B_336) | ~v4_orders_2(B_336) | v2_struct_0(B_336))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_720])).
% 23.22/12.57  tff(c_728, plain, (![B_149, D_337]: (r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_149)), D_337) | ~r3_waybel_9('#skF_4', B_149, D_337) | ~v10_waybel_0(B_149, '#skF_4') | ~m1_subset_1(D_337, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_149, '#skF_4') | ~v7_waybel_0(B_149) | ~v4_orders_2(B_149) | v2_struct_0(B_149) | ~l1_waybel_0(B_149, '#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_724])).
% 23.22/12.57  tff(c_729, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_728])).
% 23.22/12.57  tff(c_732, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_6, c_729])).
% 23.22/12.57  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_732])).
% 23.22/12.57  tff(c_738, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_728])).
% 23.22/12.57  tff(c_2, plain, (![C_3, A_1, B_2]: (v1_relat_1(C_3) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(A_1, B_2))))), inference(cnfTransformation, [status(thm)], [f_29])).
% 23.22/12.57  tff(c_121, plain, (![A_148, B_149]: (v1_relat_1(u1_waybel_0(A_148, B_149)) | ~l1_waybel_0(B_149, A_148) | ~l1_struct_0(A_148))), inference(resolution, [status(thm)], [c_113, c_2])).
% 23.22/12.57  tff(c_66, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_64, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_62, plain, (v7_waybel_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_56, plain, (v10_waybel_0('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_54, plain, (r3_waybel_9('#skF_4', '#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_269])).
% 23.22/12.57  tff(c_737, plain, (![B_149, D_337]: (r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_149)), D_337) | ~r3_waybel_9('#skF_4', B_149, D_337) | ~v10_waybel_0(B_149, '#skF_4') | ~m1_subset_1(D_337, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_149, '#skF_4') | ~v7_waybel_0(B_149) | ~v4_orders_2(B_149) | v2_struct_0(B_149) | ~l1_waybel_0(B_149, '#skF_4'))), inference(splitRight, [status(thm)], [c_728])).
% 23.22/12.57  tff(c_22, plain, (![A_12, B_24, C_30]: (m1_subset_1('#skF_1'(A_12, B_24, C_30), u1_struct_0(A_12)) | r1_yellow_0(A_12, C_30) | ~r2_lattice3(A_12, C_30, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_12)) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.22/12.57  tff(c_20, plain, (![A_12, C_30, B_24]: (r2_lattice3(A_12, C_30, '#skF_1'(A_12, B_24, C_30)) | r1_yellow_0(A_12, C_30) | ~r2_lattice3(A_12, C_30, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_12)) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.22/12.57  tff(c_776, plain, (![A_346, B_347, D_348, E_349]: (m1_subset_1('#skF_3'(A_346, B_347, D_348, D_348), u1_struct_0(A_346)) | r3_orders_2(A_346, D_348, E_349) | ~r2_lattice3(A_346, k2_relset_1(u1_struct_0(B_347), u1_struct_0(A_346), u1_waybel_0(A_346, B_347)), E_349) | ~m1_subset_1(E_349, u1_struct_0(A_346)) | ~r3_waybel_9(A_346, B_347, D_348) | ~m1_subset_1(D_348, u1_struct_0(A_346)) | ~l1_waybel_0(B_347, A_346) | ~v7_waybel_0(B_347) | ~v4_orders_2(B_347) | v2_struct_0(B_347) | ~l1_waybel_9(A_346) | ~v1_compts_1(A_346) | ~v2_lattice3(A_346) | ~v1_lattice3(A_346) | ~v5_orders_2(A_346) | ~v4_orders_2(A_346) | ~v3_orders_2(A_346) | ~v8_pre_topc(A_346) | ~v2_pre_topc(A_346))), inference(cnfTransformation, [status(thm)], [f_226])).
% 23.22/12.57  tff(c_1288, plain, (![A_444, B_445, D_446, E_447]: (m1_subset_1('#skF_3'(A_444, B_445, D_446, D_446), u1_struct_0(A_444)) | r3_orders_2(A_444, D_446, E_447) | ~r2_lattice3(A_444, k2_relat_1(u1_waybel_0(A_444, B_445)), E_447) | ~m1_subset_1(E_447, u1_struct_0(A_444)) | ~r3_waybel_9(A_444, B_445, D_446) | ~m1_subset_1(D_446, u1_struct_0(A_444)) | ~l1_waybel_0(B_445, A_444) | ~v7_waybel_0(B_445) | ~v4_orders_2(B_445) | v2_struct_0(B_445) | ~l1_waybel_9(A_444) | ~v1_compts_1(A_444) | ~v2_lattice3(A_444) | ~v1_lattice3(A_444) | ~v5_orders_2(A_444) | ~v4_orders_2(A_444) | ~v3_orders_2(A_444) | ~v8_pre_topc(A_444) | ~v2_pre_topc(A_444) | ~l1_waybel_0(B_445, A_444) | ~l1_struct_0(A_444))), inference(superposition, [status(thm), theory('equality')], [c_120, c_776])).
% 23.22/12.57  tff(c_12631, plain, (![A_23257, B_23258, D_23259, B_23260]: (m1_subset_1('#skF_3'(A_23257, B_23258, D_23259, D_23259), u1_struct_0(A_23257)) | r3_orders_2(A_23257, D_23259, '#skF_1'(A_23257, B_23260, k2_relat_1(u1_waybel_0(A_23257, B_23258)))) | ~m1_subset_1('#skF_1'(A_23257, B_23260, k2_relat_1(u1_waybel_0(A_23257, B_23258))), u1_struct_0(A_23257)) | ~r3_waybel_9(A_23257, B_23258, D_23259) | ~m1_subset_1(D_23259, u1_struct_0(A_23257)) | ~v7_waybel_0(B_23258) | ~v4_orders_2(B_23258) | v2_struct_0(B_23258) | ~l1_waybel_9(A_23257) | ~v1_compts_1(A_23257) | ~v2_lattice3(A_23257) | ~v1_lattice3(A_23257) | ~v4_orders_2(A_23257) | ~v3_orders_2(A_23257) | ~v8_pre_topc(A_23257) | ~v2_pre_topc(A_23257) | ~l1_waybel_0(B_23258, A_23257) | ~l1_struct_0(A_23257) | r1_yellow_0(A_23257, k2_relat_1(u1_waybel_0(A_23257, B_23258))) | ~r2_lattice3(A_23257, k2_relat_1(u1_waybel_0(A_23257, B_23258)), B_23260) | ~m1_subset_1(B_23260, u1_struct_0(A_23257)) | ~l1_orders_2(A_23257) | ~v5_orders_2(A_23257))), inference(resolution, [status(thm)], [c_20, c_1288])).
% 23.22/12.57  tff(c_12668, plain, (![A_23348, B_23349, D_23350, B_23351]: (m1_subset_1('#skF_3'(A_23348, B_23349, D_23350, D_23350), u1_struct_0(A_23348)) | r3_orders_2(A_23348, D_23350, '#skF_1'(A_23348, B_23351, k2_relat_1(u1_waybel_0(A_23348, B_23349)))) | ~r3_waybel_9(A_23348, B_23349, D_23350) | ~m1_subset_1(D_23350, u1_struct_0(A_23348)) | ~v7_waybel_0(B_23349) | ~v4_orders_2(B_23349) | v2_struct_0(B_23349) | ~l1_waybel_9(A_23348) | ~v1_compts_1(A_23348) | ~v2_lattice3(A_23348) | ~v1_lattice3(A_23348) | ~v4_orders_2(A_23348) | ~v3_orders_2(A_23348) | ~v8_pre_topc(A_23348) | ~v2_pre_topc(A_23348) | ~l1_waybel_0(B_23349, A_23348) | ~l1_struct_0(A_23348) | r1_yellow_0(A_23348, k2_relat_1(u1_waybel_0(A_23348, B_23349))) | ~r2_lattice3(A_23348, k2_relat_1(u1_waybel_0(A_23348, B_23349)), B_23351) | ~m1_subset_1(B_23351, u1_struct_0(A_23348)) | ~l1_orders_2(A_23348) | ~v5_orders_2(A_23348))), inference(resolution, [status(thm)], [c_22, c_12631])).
% 23.22/12.57  tff(c_865, plain, (![A_366, B_367, D_368, E_369]: (~v5_pre_topc(k4_waybel_1(A_366, '#skF_3'(A_366, B_367, D_368, D_368)), A_366, A_366) | r3_orders_2(A_366, D_368, E_369) | ~r2_lattice3(A_366, k2_relset_1(u1_struct_0(B_367), u1_struct_0(A_366), u1_waybel_0(A_366, B_367)), E_369) | ~m1_subset_1(E_369, u1_struct_0(A_366)) | ~r3_waybel_9(A_366, B_367, D_368) | ~m1_subset_1(D_368, u1_struct_0(A_366)) | ~l1_waybel_0(B_367, A_366) | ~v7_waybel_0(B_367) | ~v4_orders_2(B_367) | v2_struct_0(B_367) | ~l1_waybel_9(A_366) | ~v1_compts_1(A_366) | ~v2_lattice3(A_366) | ~v1_lattice3(A_366) | ~v5_orders_2(A_366) | ~v4_orders_2(A_366) | ~v3_orders_2(A_366) | ~v8_pre_topc(A_366) | ~v2_pre_topc(A_366))), inference(cnfTransformation, [status(thm)], [f_226])).
% 23.22/12.57  tff(c_868, plain, (![D_368, E_369, B_367]: (r3_orders_2('#skF_4', D_368, E_369) | ~r2_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_367), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_367)), E_369) | ~m1_subset_1(E_369, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_367, D_368) | ~m1_subset_1(D_368, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_367, '#skF_4') | ~v7_waybel_0(B_367) | ~v4_orders_2(B_367) | v2_struct_0(B_367) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v5_orders_2('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_subset_1('#skF_3'('#skF_4', B_367, D_368, D_368), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_58, c_865])).
% 23.22/12.57  tff(c_872, plain, (![D_370, E_371, B_372]: (r3_orders_2('#skF_4', D_370, E_371) | ~r2_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_372), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_372)), E_371) | ~m1_subset_1(E_371, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_372, D_370) | ~m1_subset_1(D_370, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_372, '#skF_4') | ~v7_waybel_0(B_372) | ~v4_orders_2(B_372) | v2_struct_0(B_372) | ~m1_subset_1('#skF_3'('#skF_4', B_372, D_370, D_370), u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_868])).
% 23.22/12.57  tff(c_886, plain, (![D_370, E_371, B_149]: (r3_orders_2('#skF_4', D_370, E_371) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_149)), E_371) | ~m1_subset_1(E_371, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_149, D_370) | ~m1_subset_1(D_370, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_149, '#skF_4') | ~v7_waybel_0(B_149) | ~v4_orders_2(B_149) | v2_struct_0(B_149) | ~m1_subset_1('#skF_3'('#skF_4', B_149, D_370, D_370), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_149, '#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_872])).
% 23.22/12.57  tff(c_963, plain, (![D_383, E_384, B_385]: (r3_orders_2('#skF_4', D_383, E_384) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_385)), E_384) | ~m1_subset_1(E_384, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_385, D_383) | ~m1_subset_1(D_383, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_385) | ~v4_orders_2(B_385) | v2_struct_0(B_385) | ~m1_subset_1('#skF_3'('#skF_4', B_385, D_383, D_383), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_385, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_886])).
% 23.22/12.57  tff(c_982, plain, (![D_383, B_24, B_385]: (r3_orders_2('#skF_4', D_383, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_385)))) | ~m1_subset_1('#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_385))), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_385, D_383) | ~m1_subset_1(D_383, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_385) | ~v4_orders_2(B_385) | v2_struct_0(B_385) | ~m1_subset_1('#skF_3'('#skF_4', B_385, D_383, D_383), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_385, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_385))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_385)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_20, c_963])).
% 23.22/12.57  tff(c_1257, plain, (![D_434, B_435, B_436]: (r3_orders_2('#skF_4', D_434, '#skF_1'('#skF_4', B_435, k2_relat_1(u1_waybel_0('#skF_4', B_436)))) | ~m1_subset_1('#skF_1'('#skF_4', B_435, k2_relat_1(u1_waybel_0('#skF_4', B_436))), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_436, D_434) | ~m1_subset_1(D_434, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_436) | ~v4_orders_2(B_436) | v2_struct_0(B_436) | ~m1_subset_1('#skF_3'('#skF_4', B_436, D_434, D_434), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_436, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_436))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_436)), B_435) | ~m1_subset_1(B_435, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_982])).
% 23.22/12.57  tff(c_1263, plain, (![D_434, B_24, B_436]: (r3_orders_2('#skF_4', D_434, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_436)))) | ~r3_waybel_9('#skF_4', B_436, D_434) | ~m1_subset_1(D_434, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_436) | ~v4_orders_2(B_436) | v2_struct_0(B_436) | ~m1_subset_1('#skF_3'('#skF_4', B_436, D_434, D_434), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_436, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_436))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_436)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_1257])).
% 23.22/12.57  tff(c_1269, plain, (![D_434, B_24, B_436]: (r3_orders_2('#skF_4', D_434, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_436)))) | ~r3_waybel_9('#skF_4', B_436, D_434) | ~m1_subset_1(D_434, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_436) | ~v4_orders_2(B_436) | v2_struct_0(B_436) | ~m1_subset_1('#skF_3'('#skF_4', B_436, D_434, D_434), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_436, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_436))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_436)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_1263])).
% 23.22/12.57  tff(c_12683, plain, (![D_23350, B_24, B_23349, B_23351]: (r3_orders_2('#skF_4', D_23350, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_23349)))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23349)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')) | r3_orders_2('#skF_4', D_23350, '#skF_1'('#skF_4', B_23351, k2_relat_1(u1_waybel_0('#skF_4', B_23349)))) | ~r3_waybel_9('#skF_4', B_23349, D_23350) | ~m1_subset_1(D_23350, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_23349) | ~v4_orders_2(B_23349) | v2_struct_0(B_23349) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_waybel_0(B_23349, '#skF_4') | ~l1_struct_0('#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23349))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23349)), B_23351) | ~m1_subset_1(B_23351, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_12668, c_1269])).
% 23.22/12.57  tff(c_12757, plain, (![D_23350, B_24, B_23349, B_23351]: (r3_orders_2('#skF_4', D_23350, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_23349)))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23349)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')) | r3_orders_2('#skF_4', D_23350, '#skF_1'('#skF_4', B_23351, k2_relat_1(u1_waybel_0('#skF_4', B_23349)))) | ~r3_waybel_9('#skF_4', B_23349, D_23350) | ~m1_subset_1(D_23350, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_23349) | ~v4_orders_2(B_23349) | v2_struct_0(B_23349) | ~l1_waybel_0(B_23349, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23349))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23349)), B_23351) | ~m1_subset_1(B_23351, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_738, c_86, c_84, c_82, c_80, c_76, c_74, c_72, c_70, c_12683])).
% 23.22/12.57  tff(c_12971, plain, (![B_23803, D_23804, B_23805]: (~r3_waybel_9('#skF_4', B_23803, D_23804) | ~m1_subset_1(D_23804, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_23803) | ~v4_orders_2(B_23803) | v2_struct_0(B_23803) | ~l1_waybel_0(B_23803, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23803))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23803)), B_23805) | ~m1_subset_1(B_23805, u1_struct_0('#skF_4')) | r3_orders_2('#skF_4', D_23804, '#skF_1'('#skF_4', B_23805, k2_relat_1(u1_waybel_0('#skF_4', B_23803)))))), inference(factorization, [status(thm), theory('equality')], [c_12757])).
% 23.22/12.57  tff(c_10, plain, (![A_8, B_9, C_10]: (r1_orders_2(A_8, B_9, C_10) | ~r3_orders_2(A_8, B_9, C_10) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 23.22/12.57  tff(c_12973, plain, (![D_23804, B_23805, B_23803]: (r1_orders_2('#skF_4', D_23804, '#skF_1'('#skF_4', B_23805, k2_relat_1(u1_waybel_0('#skF_4', B_23803)))) | ~m1_subset_1('#skF_1'('#skF_4', B_23805, k2_relat_1(u1_waybel_0('#skF_4', B_23803))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_23803, D_23804) | ~m1_subset_1(D_23804, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_23803) | ~v4_orders_2(B_23803) | v2_struct_0(B_23803) | ~l1_waybel_0(B_23803, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23803))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23803)), B_23805) | ~m1_subset_1(B_23805, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_12971, c_10])).
% 23.22/12.57  tff(c_12997, plain, (![D_23804, B_23805, B_23803]: (r1_orders_2('#skF_4', D_23804, '#skF_1'('#skF_4', B_23805, k2_relat_1(u1_waybel_0('#skF_4', B_23803)))) | ~m1_subset_1('#skF_1'('#skF_4', B_23805, k2_relat_1(u1_waybel_0('#skF_4', B_23803))), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_23803, D_23804) | ~m1_subset_1(D_23804, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_23803) | ~v4_orders_2(B_23803) | v2_struct_0(B_23803) | ~l1_waybel_0(B_23803, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23803))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23803)), B_23805) | ~m1_subset_1(B_23805, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_92, c_12973])).
% 23.22/12.57  tff(c_12999, plain, (![D_23893, B_23894, B_23895]: (r1_orders_2('#skF_4', D_23893, '#skF_1'('#skF_4', B_23894, k2_relat_1(u1_waybel_0('#skF_4', B_23895)))) | ~m1_subset_1('#skF_1'('#skF_4', B_23894, k2_relat_1(u1_waybel_0('#skF_4', B_23895))), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_23895, D_23893) | ~m1_subset_1(D_23893, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_23895) | ~v4_orders_2(B_23895) | v2_struct_0(B_23895) | ~l1_waybel_0(B_23895, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23895))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23895)), B_23894) | ~m1_subset_1(B_23894, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_160, c_12997])).
% 23.22/12.57  tff(c_13026, plain, (![D_23893, B_24, B_23895]: (r1_orders_2('#skF_4', D_23893, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_23895)))) | ~r3_waybel_9('#skF_4', B_23895, D_23893) | ~m1_subset_1(D_23893, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_23895) | ~v4_orders_2(B_23895) | v2_struct_0(B_23895) | ~l1_waybel_0(B_23895, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23895))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23895)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_12999])).
% 23.22/12.57  tff(c_13033, plain, (![D_23983, B_23984, B_23985]: (r1_orders_2('#skF_4', D_23983, '#skF_1'('#skF_4', B_23984, k2_relat_1(u1_waybel_0('#skF_4', B_23985)))) | ~r3_waybel_9('#skF_4', B_23985, D_23983) | ~m1_subset_1(D_23983, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_23985) | ~v4_orders_2(B_23985) | v2_struct_0(B_23985) | ~l1_waybel_0(B_23985, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23985))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23985)), B_23984) | ~m1_subset_1(B_23984, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_13026])).
% 23.22/12.57  tff(c_18, plain, (![A_12, B_24, C_30]: (~r1_orders_2(A_12, B_24, '#skF_1'(A_12, B_24, C_30)) | r1_yellow_0(A_12, C_30) | ~r2_lattice3(A_12, C_30, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_12)) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.22/12.57  tff(c_13041, plain, (![B_23985, B_23984]: (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~r3_waybel_9('#skF_4', B_23985, B_23984) | ~v7_waybel_0(B_23985) | ~v4_orders_2(B_23985) | v2_struct_0(B_23985) | ~l1_waybel_0(B_23985, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23985))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_23985)), B_23984) | ~m1_subset_1(B_23984, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_13033, c_18])).
% 23.22/12.57  tff(c_13069, plain, (![B_24073, B_24074]: (~r3_waybel_9('#skF_4', B_24073, B_24074) | ~v7_waybel_0(B_24073) | ~v4_orders_2(B_24073) | v2_struct_0(B_24073) | ~l1_waybel_0(B_24073, '#skF_4') | r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_24073))) | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_24073)), B_24074) | ~m1_subset_1(B_24074, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_13041])).
% 23.22/12.57  tff(c_13169, plain, (![B_24162, D_24163]: (r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_24162))) | ~r3_waybel_9('#skF_4', B_24162, D_24163) | ~v10_waybel_0(B_24162, '#skF_4') | ~m1_subset_1(D_24163, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_24162) | ~v4_orders_2(B_24162) | v2_struct_0(B_24162) | ~l1_waybel_0(B_24162, '#skF_4'))), inference(resolution, [status(thm)], [c_737, c_13069])).
% 23.22/12.57  tff(c_13171, plain, (r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6'))) | ~v10_waybel_0('#skF_6', '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_13169])).
% 23.22/12.57  tff(c_13174, plain, (r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_62, c_68, c_56, c_13171])).
% 23.22/12.57  tff(c_13175, plain, (r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_66, c_13174])).
% 23.22/12.57  tff(c_36, plain, (![A_36, B_38]: (k4_yellow_2(A_36, u1_waybel_0(A_36, B_38))=k1_waybel_2(A_36, B_38) | ~l1_waybel_0(B_38, A_36) | ~l1_orders_2(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_113])).
% 23.22/12.57  tff(c_739, plain, (![B_338, D_339]: (r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_338)), D_339) | ~r3_waybel_9('#skF_4', B_338, D_339) | ~v10_waybel_0(B_338, '#skF_4') | ~m1_subset_1(D_339, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_338, '#skF_4') | ~v7_waybel_0(B_338) | ~v4_orders_2(B_338) | v2_struct_0(B_338) | ~l1_waybel_0(B_338, '#skF_4'))), inference(splitRight, [status(thm)], [c_728])).
% 23.22/12.57  tff(c_38, plain, (![A_39, B_41]: (k1_yellow_0(A_39, k2_relat_1(B_41))=k4_yellow_2(A_39, B_41) | ~v1_relat_1(B_41) | ~l1_orders_2(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_123])).
% 23.22/12.57  tff(c_612, plain, (![A_295, C_296, D_297]: (r1_orders_2(A_295, k1_yellow_0(A_295, C_296), D_297) | ~r2_lattice3(A_295, C_296, D_297) | ~m1_subset_1(D_297, u1_struct_0(A_295)) | ~r1_yellow_0(A_295, C_296) | ~m1_subset_1(k1_yellow_0(A_295, C_296), u1_struct_0(A_295)) | ~l1_orders_2(A_295) | ~v5_orders_2(A_295))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.22/12.57  tff(c_623, plain, (![A_302, B_303, D_304]: (r1_orders_2(A_302, k1_yellow_0(A_302, k2_relat_1(B_303)), D_304) | ~r2_lattice3(A_302, k2_relat_1(B_303), D_304) | ~m1_subset_1(D_304, u1_struct_0(A_302)) | ~r1_yellow_0(A_302, k2_relat_1(B_303)) | ~m1_subset_1(k4_yellow_2(A_302, B_303), u1_struct_0(A_302)) | ~l1_orders_2(A_302) | ~v5_orders_2(A_302) | ~v1_relat_1(B_303) | ~l1_orders_2(A_302) | v2_struct_0(A_302))), inference(superposition, [status(thm), theory('equality')], [c_38, c_612])).
% 23.22/12.57  tff(c_634, plain, (![A_39, B_41, D_304]: (r1_orders_2(A_39, k4_yellow_2(A_39, B_41), D_304) | ~r2_lattice3(A_39, k2_relat_1(B_41), D_304) | ~m1_subset_1(D_304, u1_struct_0(A_39)) | ~r1_yellow_0(A_39, k2_relat_1(B_41)) | ~m1_subset_1(k4_yellow_2(A_39, B_41), u1_struct_0(A_39)) | ~l1_orders_2(A_39) | ~v5_orders_2(A_39) | ~v1_relat_1(B_41) | ~l1_orders_2(A_39) | v2_struct_0(A_39) | ~v1_relat_1(B_41) | ~l1_orders_2(A_39) | v2_struct_0(A_39))), inference(superposition, [status(thm), theory('equality')], [c_38, c_623])).
% 23.22/12.57  tff(c_741, plain, (![B_338, D_339]: (r1_orders_2('#skF_4', k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', B_338)), D_339) | ~r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_338))) | ~m1_subset_1(k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', B_338)), u1_struct_0('#skF_4')) | ~v5_orders_2('#skF_4') | ~v1_relat_1(u1_waybel_0('#skF_4', B_338)) | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_338, D_339) | ~v10_waybel_0(B_338, '#skF_4') | ~m1_subset_1(D_339, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_338) | ~v4_orders_2(B_338) | v2_struct_0(B_338) | ~l1_waybel_0(B_338, '#skF_4'))), inference(resolution, [status(thm)], [c_739, c_634])).
% 23.22/12.57  tff(c_744, plain, (![B_338, D_339]: (r1_orders_2('#skF_4', k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', B_338)), D_339) | ~r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_338))) | ~m1_subset_1(k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', B_338)), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', B_338)) | v2_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_338, D_339) | ~v10_waybel_0(B_338, '#skF_4') | ~m1_subset_1(D_339, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_338) | ~v4_orders_2(B_338) | v2_struct_0(B_338) | ~l1_waybel_0(B_338, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_78, c_741])).
% 23.22/12.57  tff(c_746, plain, (![B_340, D_341]: (r1_orders_2('#skF_4', k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', B_340)), D_341) | ~r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_340))) | ~m1_subset_1(k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', B_340)), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', B_340)) | ~r3_waybel_9('#skF_4', B_340, D_341) | ~v10_waybel_0(B_340, '#skF_4') | ~m1_subset_1(D_341, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_340) | ~v4_orders_2(B_340) | v2_struct_0(B_340) | ~l1_waybel_0(B_340, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_160, c_744])).
% 23.22/12.57  tff(c_749, plain, (![B_38, D_341]: (r1_orders_2('#skF_4', k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', B_38)), D_341) | ~r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_38))) | ~m1_subset_1(k1_waybel_2('#skF_4', B_38), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', B_38)) | ~r3_waybel_9('#skF_4', B_38, D_341) | ~v10_waybel_0(B_38, '#skF_4') | ~m1_subset_1(D_341, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_38) | ~v4_orders_2(B_38) | v2_struct_0(B_38) | ~l1_waybel_0(B_38, '#skF_4') | ~l1_waybel_0(B_38, '#skF_4') | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_746])).
% 23.22/12.57  tff(c_751, plain, (![B_38, D_341]: (r1_orders_2('#skF_4', k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', B_38)), D_341) | ~r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_38))) | ~m1_subset_1(k1_waybel_2('#skF_4', B_38), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', B_38)) | ~r3_waybel_9('#skF_4', B_38, D_341) | ~v10_waybel_0(B_38, '#skF_4') | ~m1_subset_1(D_341, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_38) | ~v4_orders_2(B_38) | v2_struct_0(B_38) | ~l1_waybel_0(B_38, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_749])).
% 23.22/12.57  tff(c_753, plain, (![B_342, D_343]: (r1_orders_2('#skF_4', k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', B_342)), D_343) | ~r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_342))) | ~m1_subset_1(k1_waybel_2('#skF_4', B_342), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', B_342)) | ~r3_waybel_9('#skF_4', B_342, D_343) | ~v10_waybel_0(B_342, '#skF_4') | ~m1_subset_1(D_343, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_342) | ~v4_orders_2(B_342) | v2_struct_0(B_342) | ~l1_waybel_0(B_342, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_160, c_751])).
% 23.22/12.57  tff(c_765, plain, (![B_38, D_343]: (r1_orders_2('#skF_4', k1_waybel_2('#skF_4', B_38), D_343) | ~r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_38))) | ~m1_subset_1(k1_waybel_2('#skF_4', B_38), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', B_38)) | ~r3_waybel_9('#skF_4', B_38, D_343) | ~v10_waybel_0(B_38, '#skF_4') | ~m1_subset_1(D_343, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_38) | ~v4_orders_2(B_38) | v2_struct_0(B_38) | ~l1_waybel_0(B_38, '#skF_4') | ~l1_waybel_0(B_38, '#skF_4') | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_753])).
% 23.22/12.57  tff(c_773, plain, (![B_38, D_343]: (r1_orders_2('#skF_4', k1_waybel_2('#skF_4', B_38), D_343) | ~r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_38))) | ~m1_subset_1(k1_waybel_2('#skF_4', B_38), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', B_38)) | ~r3_waybel_9('#skF_4', B_38, D_343) | ~v10_waybel_0(B_38, '#skF_4') | ~m1_subset_1(D_343, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_38) | ~v4_orders_2(B_38) | v2_struct_0(B_38) | ~l1_waybel_0(B_38, '#skF_4') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_765])).
% 23.22/12.57  tff(c_774, plain, (![B_38, D_343]: (r1_orders_2('#skF_4', k1_waybel_2('#skF_4', B_38), D_343) | ~r1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_38))) | ~m1_subset_1(k1_waybel_2('#skF_4', B_38), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', B_38)) | ~r3_waybel_9('#skF_4', B_38, D_343) | ~v10_waybel_0(B_38, '#skF_4') | ~m1_subset_1(D_343, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_38) | ~v4_orders_2(B_38) | v2_struct_0(B_38) | ~l1_waybel_0(B_38, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_160, c_773])).
% 23.22/12.57  tff(c_13215, plain, (![D_343]: (r1_orders_2('#skF_4', k1_waybel_2('#skF_4', '#skF_6'), D_343) | ~m1_subset_1(k1_waybel_2('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6')) | ~r3_waybel_9('#skF_4', '#skF_6', D_343) | ~v10_waybel_0('#skF_6', '#skF_4') | ~m1_subset_1(D_343, u1_struct_0('#skF_4')) | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_6', '#skF_4'))), inference(resolution, [status(thm)], [c_13175, c_774])).
% 23.22/12.57  tff(c_13286, plain, (![D_343]: (r1_orders_2('#skF_4', k1_waybel_2('#skF_4', '#skF_6'), D_343) | ~m1_subset_1(k1_waybel_2('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6')) | ~r3_waybel_9('#skF_4', '#skF_6', D_343) | ~m1_subset_1(D_343, u1_struct_0('#skF_4')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_62, c_56, c_13215])).
% 23.22/12.57  tff(c_13287, plain, (![D_343]: (r1_orders_2('#skF_4', k1_waybel_2('#skF_4', '#skF_6'), D_343) | ~m1_subset_1(k1_waybel_2('#skF_4', '#skF_6'), u1_struct_0('#skF_4')) | ~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6')) | ~r3_waybel_9('#skF_4', '#skF_6', D_343) | ~m1_subset_1(D_343, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_66, c_13286])).
% 23.22/12.57  tff(c_13288, plain, (~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6'))), inference(splitLeft, [status(thm)], [c_13287])).
% 23.22/12.57  tff(c_13291, plain, (~l1_waybel_0('#skF_6', '#skF_4') | ~l1_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_121, c_13288])).
% 23.22/12.57  tff(c_13295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_738, c_60, c_13291])).
% 23.22/12.57  tff(c_13297, plain, (v1_relat_1(u1_waybel_0('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_13287])).
% 23.22/12.57  tff(c_28, plain, (![A_12, B_24, C_30]: (m1_subset_1('#skF_1'(A_12, B_24, C_30), u1_struct_0(A_12)) | k1_yellow_0(A_12, C_30)=B_24 | ~r2_lattice3(A_12, C_30, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_12)) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.22/12.57  tff(c_723, plain, (![B_59, D_71]: (r2_lattice3('#skF_4', k2_relset_1(u1_struct_0(B_59), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_59)), D_71) | ~r3_waybel_9('#skF_4', B_59, D_71) | ~v10_waybel_0(B_59, '#skF_4') | ~m1_subset_1(D_71, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_59, '#skF_4') | ~v7_waybel_0(B_59) | ~v4_orders_2(B_59) | v2_struct_0(B_59))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_720])).
% 23.22/12.57  tff(c_26, plain, (![A_12, C_30, B_24]: (r2_lattice3(A_12, C_30, '#skF_1'(A_12, B_24, C_30)) | k1_yellow_0(A_12, C_30)=B_24 | ~r2_lattice3(A_12, C_30, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_12)) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.22/12.57  tff(c_1380, plain, (![A_463, B_464, D_465, B_466]: (m1_subset_1('#skF_3'(A_463, B_464, D_465, D_465), u1_struct_0(A_463)) | r3_orders_2(A_463, D_465, '#skF_1'(A_463, B_466, k2_relset_1(u1_struct_0(B_464), u1_struct_0(A_463), u1_waybel_0(A_463, B_464)))) | ~m1_subset_1('#skF_1'(A_463, B_466, k2_relset_1(u1_struct_0(B_464), u1_struct_0(A_463), u1_waybel_0(A_463, B_464))), u1_struct_0(A_463)) | ~r3_waybel_9(A_463, B_464, D_465) | ~m1_subset_1(D_465, u1_struct_0(A_463)) | ~l1_waybel_0(B_464, A_463) | ~v7_waybel_0(B_464) | ~v4_orders_2(B_464) | v2_struct_0(B_464) | ~l1_waybel_9(A_463) | ~v1_compts_1(A_463) | ~v2_lattice3(A_463) | ~v1_lattice3(A_463) | ~v4_orders_2(A_463) | ~v3_orders_2(A_463) | ~v8_pre_topc(A_463) | ~v2_pre_topc(A_463) | k1_yellow_0(A_463, k2_relset_1(u1_struct_0(B_464), u1_struct_0(A_463), u1_waybel_0(A_463, B_464)))=B_466 | ~r2_lattice3(A_463, k2_relset_1(u1_struct_0(B_464), u1_struct_0(A_463), u1_waybel_0(A_463, B_464)), B_466) | ~m1_subset_1(B_466, u1_struct_0(A_463)) | ~l1_orders_2(A_463) | ~v5_orders_2(A_463))), inference(resolution, [status(thm)], [c_26, c_776])).
% 23.22/12.57  tff(c_2716, plain, (![A_718, B_719, D_720, B_721]: (m1_subset_1('#skF_3'(A_718, B_719, D_720, D_720), u1_struct_0(A_718)) | r3_orders_2(A_718, D_720, '#skF_1'(A_718, B_721, k2_relset_1(u1_struct_0(B_719), u1_struct_0(A_718), u1_waybel_0(A_718, B_719)))) | ~r3_waybel_9(A_718, B_719, D_720) | ~m1_subset_1(D_720, u1_struct_0(A_718)) | ~l1_waybel_0(B_719, A_718) | ~v7_waybel_0(B_719) | ~v4_orders_2(B_719) | v2_struct_0(B_719) | ~l1_waybel_9(A_718) | ~v1_compts_1(A_718) | ~v2_lattice3(A_718) | ~v1_lattice3(A_718) | ~v4_orders_2(A_718) | ~v3_orders_2(A_718) | ~v8_pre_topc(A_718) | ~v2_pre_topc(A_718) | k1_yellow_0(A_718, k2_relset_1(u1_struct_0(B_719), u1_struct_0(A_718), u1_waybel_0(A_718, B_719)))=B_721 | ~r2_lattice3(A_718, k2_relset_1(u1_struct_0(B_719), u1_struct_0(A_718), u1_waybel_0(A_718, B_719)), B_721) | ~m1_subset_1(B_721, u1_struct_0(A_718)) | ~l1_orders_2(A_718) | ~v5_orders_2(A_718))), inference(resolution, [status(thm)], [c_28, c_1380])).
% 23.22/12.57  tff(c_13717, plain, (![A_25406, B_25407, D_25408, B_25409]: (m1_subset_1('#skF_3'(A_25406, B_25407, D_25408, D_25408), u1_struct_0(A_25406)) | r3_orders_2(A_25406, D_25408, '#skF_1'(A_25406, B_25409, k2_relat_1(u1_waybel_0(A_25406, B_25407)))) | ~r3_waybel_9(A_25406, B_25407, D_25408) | ~m1_subset_1(D_25408, u1_struct_0(A_25406)) | ~l1_waybel_0(B_25407, A_25406) | ~v7_waybel_0(B_25407) | ~v4_orders_2(B_25407) | v2_struct_0(B_25407) | ~l1_waybel_9(A_25406) | ~v1_compts_1(A_25406) | ~v2_lattice3(A_25406) | ~v1_lattice3(A_25406) | ~v4_orders_2(A_25406) | ~v3_orders_2(A_25406) | ~v8_pre_topc(A_25406) | ~v2_pre_topc(A_25406) | k1_yellow_0(A_25406, k2_relset_1(u1_struct_0(B_25407), u1_struct_0(A_25406), u1_waybel_0(A_25406, B_25407)))=B_25409 | ~r2_lattice3(A_25406, k2_relset_1(u1_struct_0(B_25407), u1_struct_0(A_25406), u1_waybel_0(A_25406, B_25407)), B_25409) | ~m1_subset_1(B_25409, u1_struct_0(A_25406)) | ~l1_orders_2(A_25406) | ~v5_orders_2(A_25406) | ~l1_waybel_0(B_25407, A_25406) | ~l1_struct_0(A_25406))), inference(superposition, [status(thm), theory('equality')], [c_120, c_2716])).
% 23.22/12.57  tff(c_13797, plain, (![B_59, D_25408, D_71]: (m1_subset_1('#skF_3'('#skF_4', B_59, D_25408, D_25408), u1_struct_0('#skF_4')) | r3_orders_2('#skF_4', D_25408, '#skF_1'('#skF_4', D_71, k2_relat_1(u1_waybel_0('#skF_4', B_59)))) | ~r3_waybel_9('#skF_4', B_59, D_25408) | ~m1_subset_1(D_25408, u1_struct_0('#skF_4')) | ~l1_waybel_9('#skF_4') | ~v1_compts_1('#skF_4') | ~v2_lattice3('#skF_4') | ~v1_lattice3('#skF_4') | ~v4_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | k1_yellow_0('#skF_4', k2_relset_1(u1_struct_0(B_59), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_59)))=D_71 | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~l1_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_59, D_71) | ~v10_waybel_0(B_59, '#skF_4') | ~m1_subset_1(D_71, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_59, '#skF_4') | ~v7_waybel_0(B_59) | ~v4_orders_2(B_59) | v2_struct_0(B_59))), inference(resolution, [status(thm)], [c_723, c_13717])).
% 23.22/12.57  tff(c_13815, plain, (![B_25497, D_25498, D_25499]: (m1_subset_1('#skF_3'('#skF_4', B_25497, D_25498, D_25498), u1_struct_0('#skF_4')) | r3_orders_2('#skF_4', D_25498, '#skF_1'('#skF_4', D_25499, k2_relat_1(u1_waybel_0('#skF_4', B_25497)))) | ~r3_waybel_9('#skF_4', B_25497, D_25498) | ~m1_subset_1(D_25498, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relset_1(u1_struct_0(B_25497), u1_struct_0('#skF_4'), u1_waybel_0('#skF_4', B_25497)))=D_25499 | ~r3_waybel_9('#skF_4', B_25497, D_25499) | ~v10_waybel_0(B_25497, '#skF_4') | ~m1_subset_1(D_25499, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_25497, '#skF_4') | ~v7_waybel_0(B_25497) | ~v4_orders_2(B_25497) | v2_struct_0(B_25497))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_78, c_92, c_86, c_84, c_82, c_80, c_76, c_74, c_72, c_70, c_13797])).
% 23.22/12.57  tff(c_17323, plain, (![B_149, D_25498, D_25499]: (m1_subset_1('#skF_3'('#skF_4', B_149, D_25498, D_25498), u1_struct_0('#skF_4')) | r3_orders_2('#skF_4', D_25498, '#skF_1'('#skF_4', D_25499, k2_relat_1(u1_waybel_0('#skF_4', B_149)))) | ~r3_waybel_9('#skF_4', B_149, D_25498) | ~m1_subset_1(D_25498, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_149)))=D_25499 | ~r3_waybel_9('#skF_4', B_149, D_25499) | ~v10_waybel_0(B_149, '#skF_4') | ~m1_subset_1(D_25499, u1_struct_0('#skF_4')) | ~l1_waybel_0(B_149, '#skF_4') | ~v7_waybel_0(B_149) | ~v4_orders_2(B_149) | v2_struct_0(B_149) | ~l1_waybel_0(B_149, '#skF_4') | ~l1_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_13815])).
% 23.22/12.57  tff(c_17364, plain, (![B_33127, D_33128, D_33129]: (m1_subset_1('#skF_3'('#skF_4', B_33127, D_33128, D_33128), u1_struct_0('#skF_4')) | r3_orders_2('#skF_4', D_33128, '#skF_1'('#skF_4', D_33129, k2_relat_1(u1_waybel_0('#skF_4', B_33127)))) | ~r3_waybel_9('#skF_4', B_33127, D_33128) | ~m1_subset_1(D_33128, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33127)))=D_33129 | ~r3_waybel_9('#skF_4', B_33127, D_33129) | ~v10_waybel_0(B_33127, '#skF_4') | ~m1_subset_1(D_33129, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_33127) | ~v4_orders_2(B_33127) | v2_struct_0(B_33127) | ~l1_waybel_0(B_33127, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_738, c_17323])).
% 23.22/12.57  tff(c_17390, plain, (![D_33128, D_33129, B_33127]: (r1_orders_2('#skF_4', D_33128, '#skF_1'('#skF_4', D_33129, k2_relat_1(u1_waybel_0('#skF_4', B_33127)))) | ~m1_subset_1('#skF_1'('#skF_4', D_33129, k2_relat_1(u1_waybel_0('#skF_4', B_33127))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | m1_subset_1('#skF_3'('#skF_4', B_33127, D_33128, D_33128), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_33127, D_33128) | ~m1_subset_1(D_33128, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33127)))=D_33129 | ~r3_waybel_9('#skF_4', B_33127, D_33129) | ~v10_waybel_0(B_33127, '#skF_4') | ~m1_subset_1(D_33129, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_33127) | ~v4_orders_2(B_33127) | v2_struct_0(B_33127) | ~l1_waybel_0(B_33127, '#skF_4'))), inference(resolution, [status(thm)], [c_17364, c_10])).
% 23.22/12.57  tff(c_17511, plain, (![D_33128, D_33129, B_33127]: (r1_orders_2('#skF_4', D_33128, '#skF_1'('#skF_4', D_33129, k2_relat_1(u1_waybel_0('#skF_4', B_33127)))) | ~m1_subset_1('#skF_1'('#skF_4', D_33129, k2_relat_1(u1_waybel_0('#skF_4', B_33127))), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | m1_subset_1('#skF_3'('#skF_4', B_33127, D_33128, D_33128), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_33127, D_33128) | ~m1_subset_1(D_33128, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33127)))=D_33129 | ~r3_waybel_9('#skF_4', B_33127, D_33129) | ~v10_waybel_0(B_33127, '#skF_4') | ~m1_subset_1(D_33129, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_33127) | ~v4_orders_2(B_33127) | v2_struct_0(B_33127) | ~l1_waybel_0(B_33127, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_92, c_17390])).
% 23.22/12.57  tff(c_18133, plain, (![D_33724, D_33725, B_33726]: (r1_orders_2('#skF_4', D_33724, '#skF_1'('#skF_4', D_33725, k2_relat_1(u1_waybel_0('#skF_4', B_33726)))) | ~m1_subset_1('#skF_1'('#skF_4', D_33725, k2_relat_1(u1_waybel_0('#skF_4', B_33726))), u1_struct_0('#skF_4')) | m1_subset_1('#skF_3'('#skF_4', B_33726, D_33724, D_33724), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_33726, D_33724) | ~m1_subset_1(D_33724, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33726)))=D_33725 | ~r3_waybel_9('#skF_4', B_33726, D_33725) | ~v10_waybel_0(B_33726, '#skF_4') | ~m1_subset_1(D_33725, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_33726) | ~v4_orders_2(B_33726) | v2_struct_0(B_33726) | ~l1_waybel_0(B_33726, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_160, c_17511])).
% 23.22/12.57  tff(c_18230, plain, (![D_33724, B_24, B_33726]: (r1_orders_2('#skF_4', D_33724, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_33726)))) | m1_subset_1('#skF_3'('#skF_4', B_33726, D_33724, D_33724), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_33726, D_33724) | ~m1_subset_1(D_33724, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_33726, B_24) | ~v10_waybel_0(B_33726, '#skF_4') | ~v7_waybel_0(B_33726) | ~v4_orders_2(B_33726) | v2_struct_0(B_33726) | ~l1_waybel_0(B_33726, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33726)))=B_24 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33726)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_18133])).
% 23.22/12.57  tff(c_18240, plain, (![D_33843, B_33844, B_33845]: (r1_orders_2('#skF_4', D_33843, '#skF_1'('#skF_4', B_33844, k2_relat_1(u1_waybel_0('#skF_4', B_33845)))) | m1_subset_1('#skF_3'('#skF_4', B_33845, D_33843, D_33843), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_33845, D_33843) | ~m1_subset_1(D_33843, u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_33845, B_33844) | ~v10_waybel_0(B_33845, '#skF_4') | ~v7_waybel_0(B_33845) | ~v4_orders_2(B_33845) | v2_struct_0(B_33845) | ~l1_waybel_0(B_33845, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33845)))=B_33844 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33845)), B_33844) | ~m1_subset_1(B_33844, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_18230])).
% 23.22/12.57  tff(c_24, plain, (![A_12, B_24, C_30]: (~r1_orders_2(A_12, B_24, '#skF_1'(A_12, B_24, C_30)) | k1_yellow_0(A_12, C_30)=B_24 | ~r2_lattice3(A_12, C_30, B_24) | ~m1_subset_1(B_24, u1_struct_0(A_12)) | ~l1_orders_2(A_12) | ~v5_orders_2(A_12))), inference(cnfTransformation, [status(thm)], [f_93])).
% 23.22/12.57  tff(c_18244, plain, (![B_33845, B_33844]: (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | m1_subset_1('#skF_3'('#skF_4', B_33845, B_33844, B_33844), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_33845, B_33844) | ~v10_waybel_0(B_33845, '#skF_4') | ~v7_waybel_0(B_33845) | ~v4_orders_2(B_33845) | v2_struct_0(B_33845) | ~l1_waybel_0(B_33845, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33845)))=B_33844 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33845)), B_33844) | ~m1_subset_1(B_33844, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_18240, c_24])).
% 23.22/12.57  tff(c_18397, plain, (![B_33962, B_33963]: (m1_subset_1('#skF_3'('#skF_4', B_33962, B_33963, B_33963), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_33962, B_33963) | ~v10_waybel_0(B_33962, '#skF_4') | ~v7_waybel_0(B_33962) | ~v4_orders_2(B_33962) | v2_struct_0(B_33962) | ~l1_waybel_0(B_33962, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33962)))=B_33963 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_33962)), B_33963) | ~m1_subset_1(B_33963, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_18244])).
% 23.22/12.57  tff(c_18588, plain, (![B_34200, D_34201]: (m1_subset_1('#skF_3'('#skF_4', B_34200, D_34201, D_34201), u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_34200)))=D_34201 | ~r3_waybel_9('#skF_4', B_34200, D_34201) | ~v10_waybel_0(B_34200, '#skF_4') | ~m1_subset_1(D_34201, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_34200) | ~v4_orders_2(B_34200) | v2_struct_0(B_34200) | ~l1_waybel_0(B_34200, '#skF_4'))), inference(resolution, [status(thm)], [c_737, c_18397])).
% 23.22/12.57  tff(c_979, plain, (![D_383, B_24, B_385]: (r3_orders_2('#skF_4', D_383, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_385)))) | ~m1_subset_1('#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_385))), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_385, D_383) | ~m1_subset_1(D_383, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_385) | ~v4_orders_2(B_385) | v2_struct_0(B_385) | ~m1_subset_1('#skF_3'('#skF_4', B_385, D_383, D_383), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_385, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_385)))=B_24 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_385)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_963])).
% 23.22/12.57  tff(c_1322, plain, (![D_451, B_452, B_453]: (r3_orders_2('#skF_4', D_451, '#skF_1'('#skF_4', B_452, k2_relat_1(u1_waybel_0('#skF_4', B_453)))) | ~m1_subset_1('#skF_1'('#skF_4', B_452, k2_relat_1(u1_waybel_0('#skF_4', B_453))), u1_struct_0('#skF_4')) | ~r3_waybel_9('#skF_4', B_453, D_451) | ~m1_subset_1(D_451, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_453) | ~v4_orders_2(B_453) | v2_struct_0(B_453) | ~m1_subset_1('#skF_3'('#skF_4', B_453, D_451, D_451), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_453, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_453)))=B_452 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_453)), B_452) | ~m1_subset_1(B_452, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_979])).
% 23.22/12.57  tff(c_1325, plain, (![D_451, B_24, B_453]: (r3_orders_2('#skF_4', D_451, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_453)))) | ~r3_waybel_9('#skF_4', B_453, D_451) | ~m1_subset_1(D_451, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_453) | ~v4_orders_2(B_453) | v2_struct_0(B_453) | ~m1_subset_1('#skF_3'('#skF_4', B_453, D_451, D_451), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_453, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_453)))=B_24 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_453)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_1322])).
% 23.22/12.57  tff(c_1331, plain, (![D_451, B_24, B_453]: (r3_orders_2('#skF_4', D_451, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_453)))) | ~r3_waybel_9('#skF_4', B_453, D_451) | ~m1_subset_1(D_451, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_453) | ~v4_orders_2(B_453) | v2_struct_0(B_453) | ~m1_subset_1('#skF_3'('#skF_4', B_453, D_451, D_451), u1_struct_0('#skF_4')) | ~l1_waybel_0(B_453, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_453)))=B_24 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_453)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_1325])).
% 23.22/12.57  tff(c_22093, plain, (![D_43893, B_43894, B_43895]: (r3_orders_2('#skF_4', D_43893, '#skF_1'('#skF_4', B_43894, k2_relat_1(u1_waybel_0('#skF_4', B_43895)))) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_43895)))=B_43894 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_43895)), B_43894) | ~m1_subset_1(B_43894, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_43895)))=D_43893 | ~r3_waybel_9('#skF_4', B_43895, D_43893) | ~v10_waybel_0(B_43895, '#skF_4') | ~m1_subset_1(D_43893, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_43895) | ~v4_orders_2(B_43895) | v2_struct_0(B_43895) | ~l1_waybel_0(B_43895, '#skF_4'))), inference(resolution, [status(thm)], [c_18588, c_1331])).
% 23.22/12.57  tff(c_22095, plain, (![D_43893, B_43894, B_43895]: (r1_orders_2('#skF_4', D_43893, '#skF_1'('#skF_4', B_43894, k2_relat_1(u1_waybel_0('#skF_4', B_43895)))) | ~m1_subset_1('#skF_1'('#skF_4', B_43894, k2_relat_1(u1_waybel_0('#skF_4', B_43895))), u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v3_orders_2('#skF_4') | v2_struct_0('#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_43895)))=B_43894 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_43895)), B_43894) | ~m1_subset_1(B_43894, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_43895)))=D_43893 | ~r3_waybel_9('#skF_4', B_43895, D_43893) | ~v10_waybel_0(B_43895, '#skF_4') | ~m1_subset_1(D_43893, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_43895) | ~v4_orders_2(B_43895) | v2_struct_0(B_43895) | ~l1_waybel_0(B_43895, '#skF_4'))), inference(resolution, [status(thm)], [c_22093, c_10])).
% 23.22/12.57  tff(c_22291, plain, (![D_43893, B_43894, B_43895]: (r1_orders_2('#skF_4', D_43893, '#skF_1'('#skF_4', B_43894, k2_relat_1(u1_waybel_0('#skF_4', B_43895)))) | ~m1_subset_1('#skF_1'('#skF_4', B_43894, k2_relat_1(u1_waybel_0('#skF_4', B_43895))), u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_43895)))=B_43894 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_43895)), B_43894) | ~m1_subset_1(B_43894, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_43895)))=D_43893 | ~r3_waybel_9('#skF_4', B_43895, D_43893) | ~v10_waybel_0(B_43895, '#skF_4') | ~m1_subset_1(D_43893, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_43895) | ~v4_orders_2(B_43895) | v2_struct_0(B_43895) | ~l1_waybel_0(B_43895, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_92, c_22095])).
% 23.22/12.57  tff(c_25344, plain, (![D_47147, B_47148, B_47149]: (r1_orders_2('#skF_4', D_47147, '#skF_1'('#skF_4', B_47148, k2_relat_1(u1_waybel_0('#skF_4', B_47149)))) | ~m1_subset_1('#skF_1'('#skF_4', B_47148, k2_relat_1(u1_waybel_0('#skF_4', B_47149))), u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47149)))=B_47148 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47149)), B_47148) | ~m1_subset_1(B_47148, u1_struct_0('#skF_4')) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47149)))=D_47147 | ~r3_waybel_9('#skF_4', B_47149, D_47147) | ~v10_waybel_0(B_47149, '#skF_4') | ~m1_subset_1(D_47147, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_47149) | ~v4_orders_2(B_47149) | v2_struct_0(B_47149) | ~l1_waybel_0(B_47149, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_160, c_22291])).
% 23.22/12.57  tff(c_25540, plain, (![D_47147, B_24, B_47149]: (r1_orders_2('#skF_4', D_47147, '#skF_1'('#skF_4', B_24, k2_relat_1(u1_waybel_0('#skF_4', B_47149)))) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47149)))=D_47147 | ~r3_waybel_9('#skF_4', B_47149, D_47147) | ~v10_waybel_0(B_47149, '#skF_4') | ~m1_subset_1(D_47147, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_47149) | ~v4_orders_2(B_47149) | v2_struct_0(B_47149) | ~l1_waybel_0(B_47149, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47149)))=B_24 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47149)), B_24) | ~m1_subset_1(B_24, u1_struct_0('#skF_4')) | ~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_25344])).
% 23.22/12.57  tff(c_25550, plain, (![D_47295, B_47296, B_47297]: (r1_orders_2('#skF_4', D_47295, '#skF_1'('#skF_4', B_47296, k2_relat_1(u1_waybel_0('#skF_4', B_47297)))) | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47297)))=D_47295 | ~r3_waybel_9('#skF_4', B_47297, D_47295) | ~v10_waybel_0(B_47297, '#skF_4') | ~m1_subset_1(D_47295, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_47297) | ~v4_orders_2(B_47297) | v2_struct_0(B_47297) | ~l1_waybel_0(B_47297, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47297)))=B_47296 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47297)), B_47296) | ~m1_subset_1(B_47296, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_25540])).
% 23.22/12.57  tff(c_25554, plain, (![B_47297, B_47296]: (~l1_orders_2('#skF_4') | ~v5_orders_2('#skF_4') | ~r3_waybel_9('#skF_4', B_47297, B_47296) | ~v10_waybel_0(B_47297, '#skF_4') | ~v7_waybel_0(B_47297) | ~v4_orders_2(B_47297) | v2_struct_0(B_47297) | ~l1_waybel_0(B_47297, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47297)))=B_47296 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47297)), B_47296) | ~m1_subset_1(B_47296, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_25550, c_24])).
% 23.22/12.57  tff(c_26270, plain, (![B_47592, B_47593]: (~r3_waybel_9('#skF_4', B_47592, B_47593) | ~v10_waybel_0(B_47592, '#skF_4') | ~v7_waybel_0(B_47592) | ~v4_orders_2(B_47592) | v2_struct_0(B_47592) | ~l1_waybel_0(B_47592, '#skF_4') | k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47592)))=B_47593 | ~r2_lattice3('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47592)), B_47593) | ~m1_subset_1(B_47593, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_92, c_25554])).
% 23.22/12.57  tff(c_26479, plain, (![B_47739, D_47740]: (k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', B_47739)))=D_47740 | ~r3_waybel_9('#skF_4', B_47739, D_47740) | ~v10_waybel_0(B_47739, '#skF_4') | ~m1_subset_1(D_47740, u1_struct_0('#skF_4')) | ~v7_waybel_0(B_47739) | ~v4_orders_2(B_47739) | v2_struct_0(B_47739) | ~l1_waybel_0(B_47739, '#skF_4'))), inference(resolution, [status(thm)], [c_737, c_26270])).
% 23.22/12.57  tff(c_26529, plain, (k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))='#skF_5' | ~v10_waybel_0('#skF_6', '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_26479])).
% 23.22/12.57  tff(c_26532, plain, (k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))='#skF_5' | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_64, c_62, c_68, c_56, c_26529])).
% 23.22/12.57  tff(c_26533, plain, (k1_yellow_0('#skF_4', k2_relat_1(u1_waybel_0('#skF_4', '#skF_6')))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_26532])).
% 23.22/12.57  tff(c_26579, plain, (k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', '#skF_6'))='#skF_5' | ~v1_relat_1(u1_waybel_0('#skF_4', '#skF_6')) | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26533, c_38])).
% 23.22/12.57  tff(c_26677, plain, (k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', '#skF_6'))='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_13297, c_26579])).
% 23.22/12.57  tff(c_26678, plain, (k4_yellow_2('#skF_4', u1_waybel_0('#skF_4', '#skF_6'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_160, c_26677])).
% 23.22/12.57  tff(c_26806, plain, (k1_waybel_2('#skF_4', '#skF_6')='#skF_5' | ~l1_waybel_0('#skF_6', '#skF_4') | ~l1_orders_2('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26678, c_36])).
% 23.22/12.57  tff(c_26948, plain, (k1_waybel_2('#skF_4', '#skF_6')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_60, c_26806])).
% 23.22/12.57  tff(c_26950, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_52, c_26948])).
% 23.22/12.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.22/12.57  
% 23.22/12.57  Inference rules
% 23.22/12.57  ----------------------
% 23.22/12.57  #Ref     : 0
% 23.22/12.57  #Sup     : 4000
% 23.22/12.57  #Fact    : 32
% 23.22/12.57  #Define  : 0
% 23.22/12.57  #Split   : 10
% 23.22/12.57  #Chain   : 0
% 23.22/12.57  #Close   : 0
% 23.22/12.57  
% 23.22/12.57  Ordering : KBO
% 23.22/12.57  
% 23.22/12.57  Simplification rules
% 23.22/12.57  ----------------------
% 23.22/12.57  #Subsume      : 589
% 23.22/12.57  #Demod        : 3127
% 23.22/12.57  #Tautology    : 152
% 23.22/12.57  #SimpNegUnit  : 471
% 23.22/12.57  #BackRed      : 0
% 23.22/12.57  
% 23.22/12.57  #Partial instantiations: 25808
% 23.22/12.57  #Strategies tried      : 1
% 23.22/12.57  
% 23.22/12.57  Timing (in seconds)
% 23.22/12.57  ----------------------
% 23.22/12.57  Preprocessing        : 0.38
% 23.22/12.57  Parsing              : 0.20
% 23.22/12.57  CNF conversion       : 0.03
% 23.22/12.57  Main loop            : 11.40
% 23.22/12.57  Inferencing          : 2.27
% 23.22/12.57  Reduction            : 1.55
% 23.22/12.57  Demodulation         : 1.14
% 23.22/12.57  BG Simplification    : 0.16
% 23.22/12.57  Subsumption          : 7.18
% 23.22/12.57  Abstraction          : 0.22
% 23.22/12.57  MUC search           : 0.00
% 23.22/12.57  Cooper               : 0.00
% 23.22/12.57  Total                : 11.85
% 23.22/12.57  Index Insertion      : 0.00
% 23.22/12.57  Index Deletion       : 0.00
% 23.22/12.57  Index Matching       : 0.00
% 23.22/12.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
