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
% DateTime   : Thu Dec  3 10:31:21 EST 2020

% Result     : Theorem 6.07s
% Output     : CNFRefutation 6.34s
% Verified   : 
% Statistics : Number of formulae       :  225 (1824 expanded)
%              Number of leaves         :   54 ( 763 expanded)
%              Depth                    :   29
%              Number of atoms          : 1345 (15566 expanded)
%              Number of equality atoms :   56 ( 159 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > r3_waybel_9 > r3_orders_2 > r2_lattice3 > r1_orders_2 > v10_waybel_0 > r2_hidden > r1_yellow_0 > r1_waybel_9 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_compts_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_waybel_1 > k1_waybel_2 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_6 > #skF_1 > #skF_10 > #skF_9 > #skF_4 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_5

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v10_waybel_0,type,(
    v10_waybel_0: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(r1_waybel_9,type,(
    r1_waybel_9: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_waybel_2,type,(
    k1_waybel_2: ( $i * $i ) > $i )).

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_326,negated_conjecture,(
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
       => ( ! [B] :
              ( m1_subset_1(B,u1_struct_0(A))
             => v5_pre_topc(k4_waybel_1(A,B),A,A) )
         => ! [B] :
              ( ( ~ v2_struct_0(B)
                & v4_orders_2(B)
                & v7_waybel_0(B)
                & l1_waybel_0(B,A) )
             => ( v10_waybel_0(B,A)
               => ( r1_waybel_9(A,B)
                  & r2_hidden(k1_waybel_2(A,B),k10_yellow_6(A,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_waybel_9)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_204,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v8_pre_topc(A)
        & v1_compts_1(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r3_waybel_9(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_waybel_9)).

tff(f_286,axiom,(
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

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_244,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v8_pre_topc(A)
        & v1_compts_1(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ( ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( ( r3_waybel_9(A,B,C)
                        & r3_waybel_9(A,B,D) )
                     => C = D ) ) )
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(A))
               => ( r3_waybel_9(A,B,C)
                 => r2_hidden(C,k10_yellow_6(A,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_waybel_9)).

tff(f_128,axiom,(
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

tff(f_66,axiom,(
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

tff(f_178,axiom,(
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

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ( r1_waybel_9(A,B)
          <=> r1_yellow_0(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_waybel_9)).

tff(c_68,plain,(
    l1_waybel_9('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_85,plain,(
    ! [A_150] :
      ( l1_orders_2(A_150)
      | ~ l1_waybel_9(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_89,plain,(
    l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_85])).

tff(c_74,plain,(
    v1_lattice3('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_80,plain,(
    v3_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_84,plain,(
    v2_pre_topc('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_82,plain,(
    v8_pre_topc('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_70,plain,(
    v1_compts_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_90,plain,(
    ! [A_151] :
      ( l1_pre_topc(A_151)
      | ~ l1_waybel_9(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_94,plain,(
    l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_90])).

tff(c_36,plain,(
    ! [A_110,B_114] :
      ( r3_waybel_9(A_110,B_114,'#skF_5'(A_110,B_114))
      | ~ l1_waybel_0(B_114,A_110)
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc(A_110)
      | ~ v1_compts_1(A_110)
      | ~ v8_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_78,plain,(
    v4_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_76,plain,(
    v5_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_72,plain,(
    v2_lattice3('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_52,plain,(
    ! [A_133,B_141,C_145] :
      ( m1_subset_1('#skF_8'(A_133,B_141,C_145),u1_struct_0(A_133))
      | k1_waybel_2(A_133,C_145) = B_141
      | ~ r3_waybel_9(A_133,C_145,B_141)
      | ~ v10_waybel_0(C_145,A_133)
      | ~ l1_waybel_0(C_145,A_133)
      | ~ v7_waybel_0(C_145)
      | ~ v4_orders_2(C_145)
      | v2_struct_0(C_145)
      | ~ m1_subset_1(B_141,u1_struct_0(A_133))
      | ~ l1_waybel_9(A_133)
      | ~ v1_compts_1(A_133)
      | ~ v2_lattice3(A_133)
      | ~ v1_lattice3(A_133)
      | ~ v5_orders_2(A_133)
      | ~ v4_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | ~ v8_pre_topc(A_133)
      | ~ v2_pre_topc(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_66,plain,(
    ! [B_149] :
      ( v5_pre_topc(k4_waybel_1('#skF_9',B_149),'#skF_9','#skF_9')
      | ~ m1_subset_1(B_149,u1_struct_0('#skF_9')) ) ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_1577,plain,(
    ! [A_592,B_593,C_594] :
      ( ~ v5_pre_topc(k4_waybel_1(A_592,'#skF_8'(A_592,B_593,C_594)),A_592,A_592)
      | k1_waybel_2(A_592,C_594) = B_593
      | ~ r3_waybel_9(A_592,C_594,B_593)
      | ~ v10_waybel_0(C_594,A_592)
      | ~ l1_waybel_0(C_594,A_592)
      | ~ v7_waybel_0(C_594)
      | ~ v4_orders_2(C_594)
      | v2_struct_0(C_594)
      | ~ m1_subset_1(B_593,u1_struct_0(A_592))
      | ~ l1_waybel_9(A_592)
      | ~ v1_compts_1(A_592)
      | ~ v2_lattice3(A_592)
      | ~ v1_lattice3(A_592)
      | ~ v5_orders_2(A_592)
      | ~ v4_orders_2(A_592)
      | ~ v3_orders_2(A_592)
      | ~ v8_pre_topc(A_592)
      | ~ v2_pre_topc(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1581,plain,(
    ! [C_594,B_593] :
      ( k1_waybel_2('#skF_9',C_594) = B_593
      | ~ r3_waybel_9('#skF_9',C_594,B_593)
      | ~ v10_waybel_0(C_594,'#skF_9')
      | ~ l1_waybel_0(C_594,'#skF_9')
      | ~ v7_waybel_0(C_594)
      | ~ v4_orders_2(C_594)
      | v2_struct_0(C_594)
      | ~ m1_subset_1(B_593,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_8'('#skF_9',B_593,C_594),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_66,c_1577])).

tff(c_1585,plain,(
    ! [C_595,B_596] :
      ( k1_waybel_2('#skF_9',C_595) = B_596
      | ~ r3_waybel_9('#skF_9',C_595,B_596)
      | ~ v10_waybel_0(C_595,'#skF_9')
      | ~ l1_waybel_0(C_595,'#skF_9')
      | ~ v7_waybel_0(C_595)
      | ~ v4_orders_2(C_595)
      | v2_struct_0(C_595)
      | ~ m1_subset_1(B_596,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_8'('#skF_9',B_596,C_595),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1581])).

tff(c_1589,plain,(
    ! [C_145,B_141] :
      ( k1_waybel_2('#skF_9',C_145) = B_141
      | ~ r3_waybel_9('#skF_9',C_145,B_141)
      | ~ v10_waybel_0(C_145,'#skF_9')
      | ~ l1_waybel_0(C_145,'#skF_9')
      | ~ v7_waybel_0(C_145)
      | ~ v4_orders_2(C_145)
      | v2_struct_0(C_145)
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_1585])).

tff(c_1593,plain,(
    ! [C_597,B_598] :
      ( k1_waybel_2('#skF_9',C_597) = B_598
      | ~ r3_waybel_9('#skF_9',C_597,B_598)
      | ~ v10_waybel_0(C_597,'#skF_9')
      | ~ l1_waybel_0(C_597,'#skF_9')
      | ~ v7_waybel_0(C_597)
      | ~ v4_orders_2(C_597)
      | v2_struct_0(C_597)
      | ~ m1_subset_1(B_598,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1589])).

tff(c_1602,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_114),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_1593])).

tff(c_1611,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_114),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1602])).

tff(c_1612,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1611])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1615,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_1612,c_6])).

tff(c_1619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_74,c_1615])).

tff(c_1621,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1611])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_62,plain,(
    v4_orders_2('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_60,plain,(
    v7_waybel_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_58,plain,(
    l1_waybel_0('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_38,plain,(
    ! [A_110,B_114] :
      ( m1_subset_1('#skF_5'(A_110,B_114),u1_struct_0(A_110))
      | ~ l1_waybel_0(B_114,A_110)
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc(A_110)
      | ~ v1_compts_1(A_110)
      | ~ v8_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_56,plain,(
    v10_waybel_0('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_1622,plain,(
    ! [B_599] :
      ( k1_waybel_2('#skF_9',B_599) = '#skF_5'('#skF_9',B_599)
      | ~ v10_waybel_0(B_599,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_599),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_599,'#skF_9')
      | ~ v7_waybel_0(B_599)
      | ~ v4_orders_2(B_599)
      | v2_struct_0(B_599) ) ),
    inference(splitRight,[status(thm)],[c_1611])).

tff(c_1626,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_38,c_1622])).

tff(c_1629,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1626])).

tff(c_1631,plain,(
    ! [B_600] :
      ( k1_waybel_2('#skF_9',B_600) = '#skF_5'('#skF_9',B_600)
      | ~ v10_waybel_0(B_600,'#skF_9')
      | ~ l1_waybel_0(B_600,'#skF_9')
      | ~ v7_waybel_0(B_600)
      | ~ v4_orders_2(B_600)
      | v2_struct_0(B_600) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1621,c_1629])).

tff(c_1634,plain,
    ( k1_waybel_2('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_56,c_1631])).

tff(c_1637,plain,
    ( k1_waybel_2('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1634])).

tff(c_1638,plain,(
    k1_waybel_2('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1637])).

tff(c_1509,plain,(
    ! [A_561,B_562,C_563] :
      ( m1_subset_1('#skF_6'(A_561,B_562),u1_struct_0(A_561))
      | r2_hidden(C_563,k10_yellow_6(A_561,B_562))
      | ~ r3_waybel_9(A_561,B_562,C_563)
      | ~ m1_subset_1(C_563,u1_struct_0(A_561))
      | ~ l1_waybel_0(B_562,A_561)
      | ~ v7_waybel_0(B_562)
      | ~ v4_orders_2(B_562)
      | v2_struct_0(B_562)
      | ~ l1_pre_topc(A_561)
      | ~ v1_compts_1(A_561)
      | ~ v8_pre_topc(A_561)
      | ~ v2_pre_topc(A_561)
      | v2_struct_0(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_54,plain,
    ( ~ r2_hidden(k1_waybel_2('#skF_9','#skF_10'),k10_yellow_6('#skF_9','#skF_10'))
    | ~ r1_waybel_9('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_97,plain,(
    ~ r1_waybel_9('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_160,plain,(
    ! [A_215,B_216,C_217] :
      ( ~ v5_pre_topc(k4_waybel_1(A_215,'#skF_8'(A_215,B_216,C_217)),A_215,A_215)
      | k1_waybel_2(A_215,C_217) = B_216
      | ~ r3_waybel_9(A_215,C_217,B_216)
      | ~ v10_waybel_0(C_217,A_215)
      | ~ l1_waybel_0(C_217,A_215)
      | ~ v7_waybel_0(C_217)
      | ~ v4_orders_2(C_217)
      | v2_struct_0(C_217)
      | ~ m1_subset_1(B_216,u1_struct_0(A_215))
      | ~ l1_waybel_9(A_215)
      | ~ v1_compts_1(A_215)
      | ~ v2_lattice3(A_215)
      | ~ v1_lattice3(A_215)
      | ~ v5_orders_2(A_215)
      | ~ v4_orders_2(A_215)
      | ~ v3_orders_2(A_215)
      | ~ v8_pre_topc(A_215)
      | ~ v2_pre_topc(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_164,plain,(
    ! [C_217,B_216] :
      ( k1_waybel_2('#skF_9',C_217) = B_216
      | ~ r3_waybel_9('#skF_9',C_217,B_216)
      | ~ v10_waybel_0(C_217,'#skF_9')
      | ~ l1_waybel_0(C_217,'#skF_9')
      | ~ v7_waybel_0(C_217)
      | ~ v4_orders_2(C_217)
      | v2_struct_0(C_217)
      | ~ m1_subset_1(B_216,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_8'('#skF_9',B_216,C_217),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_66,c_160])).

tff(c_173,plain,(
    ! [C_221,B_222] :
      ( k1_waybel_2('#skF_9',C_221) = B_222
      | ~ r3_waybel_9('#skF_9',C_221,B_222)
      | ~ v10_waybel_0(C_221,'#skF_9')
      | ~ l1_waybel_0(C_221,'#skF_9')
      | ~ v7_waybel_0(C_221)
      | ~ v4_orders_2(C_221)
      | v2_struct_0(C_221)
      | ~ m1_subset_1(B_222,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_8'('#skF_9',B_222,C_221),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_164])).

tff(c_177,plain,(
    ! [C_145,B_141] :
      ( k1_waybel_2('#skF_9',C_145) = B_141
      | ~ r3_waybel_9('#skF_9',C_145,B_141)
      | ~ v10_waybel_0(C_145,'#skF_9')
      | ~ l1_waybel_0(C_145,'#skF_9')
      | ~ v7_waybel_0(C_145)
      | ~ v4_orders_2(C_145)
      | v2_struct_0(C_145)
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_173])).

tff(c_181,plain,(
    ! [C_223,B_224] :
      ( k1_waybel_2('#skF_9',C_223) = B_224
      | ~ r3_waybel_9('#skF_9',C_223,B_224)
      | ~ v10_waybel_0(C_223,'#skF_9')
      | ~ l1_waybel_0(C_223,'#skF_9')
      | ~ v7_waybel_0(C_223)
      | ~ v4_orders_2(C_223)
      | v2_struct_0(C_223)
      | ~ m1_subset_1(B_224,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_177])).

tff(c_190,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_114),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_181])).

tff(c_199,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_114),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_190])).

tff(c_200,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_204,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_200,c_6])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_74,c_204])).

tff(c_210,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_30,plain,(
    ! [A_34,B_50,D_62] :
      ( m1_subset_1('#skF_3'(A_34,B_50,D_62,D_62),u1_struct_0(A_34))
      | r2_lattice3(A_34,k2_relset_1(u1_struct_0(B_50),u1_struct_0(A_34),u1_waybel_0(A_34,B_50)),D_62)
      | ~ r3_waybel_9(A_34,B_50,D_62)
      | ~ v10_waybel_0(B_50,A_34)
      | ~ m1_subset_1(D_62,u1_struct_0(A_34))
      | ~ l1_waybel_0(B_50,A_34)
      | ~ v7_waybel_0(B_50)
      | ~ v4_orders_2(B_50)
      | v2_struct_0(B_50)
      | ~ l1_waybel_9(A_34)
      | ~ v1_compts_1(A_34)
      | ~ v2_lattice3(A_34)
      | ~ v1_lattice3(A_34)
      | ~ v5_orders_2(A_34)
      | ~ v4_orders_2(A_34)
      | ~ v3_orders_2(A_34)
      | ~ v8_pre_topc(A_34)
      | ~ v2_pre_topc(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_232,plain,(
    ! [A_227,B_228,D_229] :
      ( ~ v5_pre_topc(k4_waybel_1(A_227,'#skF_3'(A_227,B_228,D_229,D_229)),A_227,A_227)
      | r2_lattice3(A_227,k2_relset_1(u1_struct_0(B_228),u1_struct_0(A_227),u1_waybel_0(A_227,B_228)),D_229)
      | ~ r3_waybel_9(A_227,B_228,D_229)
      | ~ v10_waybel_0(B_228,A_227)
      | ~ m1_subset_1(D_229,u1_struct_0(A_227))
      | ~ l1_waybel_0(B_228,A_227)
      | ~ v7_waybel_0(B_228)
      | ~ v4_orders_2(B_228)
      | v2_struct_0(B_228)
      | ~ l1_waybel_9(A_227)
      | ~ v1_compts_1(A_227)
      | ~ v2_lattice3(A_227)
      | ~ v1_lattice3(A_227)
      | ~ v5_orders_2(A_227)
      | ~ v4_orders_2(A_227)
      | ~ v3_orders_2(A_227)
      | ~ v8_pre_topc(A_227)
      | ~ v2_pre_topc(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_235,plain,(
    ! [B_228,D_229] :
      ( r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_228),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_228)),D_229)
      | ~ r3_waybel_9('#skF_9',B_228,D_229)
      | ~ v10_waybel_0(B_228,'#skF_9')
      | ~ m1_subset_1(D_229,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_228,'#skF_9')
      | ~ v7_waybel_0(B_228)
      | ~ v4_orders_2(B_228)
      | v2_struct_0(B_228)
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_3'('#skF_9',B_228,D_229,D_229),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_66,c_232])).

tff(c_239,plain,(
    ! [B_230,D_231] :
      ( r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_230),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_230)),D_231)
      | ~ r3_waybel_9('#skF_9',B_230,D_231)
      | ~ v10_waybel_0(B_230,'#skF_9')
      | ~ m1_subset_1(D_231,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_230,'#skF_9')
      | ~ v7_waybel_0(B_230)
      | ~ v4_orders_2(B_230)
      | v2_struct_0(B_230)
      | ~ m1_subset_1('#skF_3'('#skF_9',B_230,D_231,D_231),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_235])).

tff(c_242,plain,(
    ! [B_50,D_62] :
      ( r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_50),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_50)),D_62)
      | ~ r3_waybel_9('#skF_9',B_50,D_62)
      | ~ v10_waybel_0(B_50,'#skF_9')
      | ~ m1_subset_1(D_62,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_50,'#skF_9')
      | ~ v7_waybel_0(B_50)
      | ~ v4_orders_2(B_50)
      | v2_struct_0(B_50)
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_30,c_239])).

tff(c_245,plain,(
    ! [B_50,D_62] :
      ( r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_50),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_50)),D_62)
      | ~ r3_waybel_9('#skF_9',B_50,D_62)
      | ~ v10_waybel_0(B_50,'#skF_9')
      | ~ m1_subset_1(D_62,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_50,'#skF_9')
      | ~ v7_waybel_0(B_50)
      | ~ v4_orders_2(B_50)
      | v2_struct_0(B_50) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_242])).

tff(c_18,plain,(
    ! [A_5,B_19,C_26] :
      ( m1_subset_1('#skF_1'(A_5,B_19,C_26),u1_struct_0(A_5))
      | r1_yellow_0(A_5,B_19)
      | ~ r2_lattice3(A_5,B_19,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_5,B_19,C_26] :
      ( r2_lattice3(A_5,B_19,'#skF_1'(A_5,B_19,C_26))
      | r1_yellow_0(A_5,B_19)
      | ~ r2_lattice3(A_5,B_19,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_303,plain,(
    ! [A_248,B_249,D_250,E_251] :
      ( m1_subset_1('#skF_4'(A_248,B_249,D_250,D_250),u1_struct_0(A_248))
      | r3_orders_2(A_248,D_250,E_251)
      | ~ r2_lattice3(A_248,k2_relset_1(u1_struct_0(B_249),u1_struct_0(A_248),u1_waybel_0(A_248,B_249)),E_251)
      | ~ m1_subset_1(E_251,u1_struct_0(A_248))
      | ~ r3_waybel_9(A_248,B_249,D_250)
      | ~ m1_subset_1(D_250,u1_struct_0(A_248))
      | ~ l1_waybel_0(B_249,A_248)
      | ~ v7_waybel_0(B_249)
      | ~ v4_orders_2(B_249)
      | v2_struct_0(B_249)
      | ~ l1_waybel_9(A_248)
      | ~ v1_compts_1(A_248)
      | ~ v2_lattice3(A_248)
      | ~ v1_lattice3(A_248)
      | ~ v5_orders_2(A_248)
      | ~ v4_orders_2(A_248)
      | ~ v3_orders_2(A_248)
      | ~ v8_pre_topc(A_248)
      | ~ v2_pre_topc(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_940,plain,(
    ! [A_412,B_413,D_414,C_415] :
      ( m1_subset_1('#skF_4'(A_412,B_413,D_414,D_414),u1_struct_0(A_412))
      | r3_orders_2(A_412,D_414,'#skF_1'(A_412,k2_relset_1(u1_struct_0(B_413),u1_struct_0(A_412),u1_waybel_0(A_412,B_413)),C_415))
      | ~ m1_subset_1('#skF_1'(A_412,k2_relset_1(u1_struct_0(B_413),u1_struct_0(A_412),u1_waybel_0(A_412,B_413)),C_415),u1_struct_0(A_412))
      | ~ r3_waybel_9(A_412,B_413,D_414)
      | ~ m1_subset_1(D_414,u1_struct_0(A_412))
      | ~ l1_waybel_0(B_413,A_412)
      | ~ v7_waybel_0(B_413)
      | ~ v4_orders_2(B_413)
      | v2_struct_0(B_413)
      | ~ l1_waybel_9(A_412)
      | ~ v1_compts_1(A_412)
      | ~ v2_lattice3(A_412)
      | ~ v1_lattice3(A_412)
      | ~ v4_orders_2(A_412)
      | ~ v3_orders_2(A_412)
      | ~ v8_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | r1_yellow_0(A_412,k2_relset_1(u1_struct_0(B_413),u1_struct_0(A_412),u1_waybel_0(A_412,B_413)))
      | ~ r2_lattice3(A_412,k2_relset_1(u1_struct_0(B_413),u1_struct_0(A_412),u1_waybel_0(A_412,B_413)),C_415)
      | ~ m1_subset_1(C_415,u1_struct_0(A_412))
      | ~ l1_orders_2(A_412)
      | ~ v5_orders_2(A_412) ) ),
    inference(resolution,[status(thm)],[c_16,c_303])).

tff(c_1261,plain,(
    ! [A_489,B_490,D_491,C_492] :
      ( m1_subset_1('#skF_4'(A_489,B_490,D_491,D_491),u1_struct_0(A_489))
      | r3_orders_2(A_489,D_491,'#skF_1'(A_489,k2_relset_1(u1_struct_0(B_490),u1_struct_0(A_489),u1_waybel_0(A_489,B_490)),C_492))
      | ~ r3_waybel_9(A_489,B_490,D_491)
      | ~ m1_subset_1(D_491,u1_struct_0(A_489))
      | ~ l1_waybel_0(B_490,A_489)
      | ~ v7_waybel_0(B_490)
      | ~ v4_orders_2(B_490)
      | v2_struct_0(B_490)
      | ~ l1_waybel_9(A_489)
      | ~ v1_compts_1(A_489)
      | ~ v2_lattice3(A_489)
      | ~ v1_lattice3(A_489)
      | ~ v4_orders_2(A_489)
      | ~ v3_orders_2(A_489)
      | ~ v8_pre_topc(A_489)
      | ~ v2_pre_topc(A_489)
      | r1_yellow_0(A_489,k2_relset_1(u1_struct_0(B_490),u1_struct_0(A_489),u1_waybel_0(A_489,B_490)))
      | ~ r2_lattice3(A_489,k2_relset_1(u1_struct_0(B_490),u1_struct_0(A_489),u1_waybel_0(A_489,B_490)),C_492)
      | ~ m1_subset_1(C_492,u1_struct_0(A_489))
      | ~ l1_orders_2(A_489)
      | ~ v5_orders_2(A_489) ) ),
    inference(resolution,[status(thm)],[c_18,c_940])).

tff(c_387,plain,(
    ! [A_276,B_277,D_278,E_279] :
      ( ~ v5_pre_topc(k4_waybel_1(A_276,'#skF_4'(A_276,B_277,D_278,D_278)),A_276,A_276)
      | r3_orders_2(A_276,D_278,E_279)
      | ~ r2_lattice3(A_276,k2_relset_1(u1_struct_0(B_277),u1_struct_0(A_276),u1_waybel_0(A_276,B_277)),E_279)
      | ~ m1_subset_1(E_279,u1_struct_0(A_276))
      | ~ r3_waybel_9(A_276,B_277,D_278)
      | ~ m1_subset_1(D_278,u1_struct_0(A_276))
      | ~ l1_waybel_0(B_277,A_276)
      | ~ v7_waybel_0(B_277)
      | ~ v4_orders_2(B_277)
      | v2_struct_0(B_277)
      | ~ l1_waybel_9(A_276)
      | ~ v1_compts_1(A_276)
      | ~ v2_lattice3(A_276)
      | ~ v1_lattice3(A_276)
      | ~ v5_orders_2(A_276)
      | ~ v4_orders_2(A_276)
      | ~ v3_orders_2(A_276)
      | ~ v8_pre_topc(A_276)
      | ~ v2_pre_topc(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_390,plain,(
    ! [D_278,E_279,B_277] :
      ( r3_orders_2('#skF_9',D_278,E_279)
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_277),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_277)),E_279)
      | ~ m1_subset_1(E_279,u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9',B_277,D_278)
      | ~ m1_subset_1(D_278,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_277,'#skF_9')
      | ~ v7_waybel_0(B_277)
      | ~ v4_orders_2(B_277)
      | v2_struct_0(B_277)
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_277,D_278,D_278),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_66,c_387])).

tff(c_394,plain,(
    ! [D_280,E_281,B_282] :
      ( r3_orders_2('#skF_9',D_280,E_281)
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_282)),E_281)
      | ~ m1_subset_1(E_281,u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9',B_282,D_280)
      | ~ m1_subset_1(D_280,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_282,'#skF_9')
      | ~ v7_waybel_0(B_282)
      | ~ v4_orders_2(B_282)
      | v2_struct_0(B_282)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_282,D_280,D_280),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_390])).

tff(c_402,plain,(
    ! [D_280,B_282,C_26] :
      ( r3_orders_2('#skF_9',D_280,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_282)),C_26))
      | ~ m1_subset_1('#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_282)),C_26),u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9',B_282,D_280)
      | ~ m1_subset_1(D_280,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_282,'#skF_9')
      | ~ v7_waybel_0(B_282)
      | ~ v4_orders_2(B_282)
      | v2_struct_0(B_282)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_282,D_280,D_280),u1_struct_0('#skF_9'))
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_282)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_282)),C_26)
      | ~ m1_subset_1(C_26,u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_16,c_394])).

tff(c_742,plain,(
    ! [D_367,B_368,C_369] :
      ( r3_orders_2('#skF_9',D_367,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)),C_369))
      | ~ m1_subset_1('#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)),C_369),u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9',B_368,D_367)
      | ~ m1_subset_1(D_367,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_368,'#skF_9')
      | ~ v7_waybel_0(B_368)
      | ~ v4_orders_2(B_368)
      | v2_struct_0(B_368)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_368,D_367,D_367),u1_struct_0('#skF_9'))
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)),C_369)
      | ~ m1_subset_1(C_369,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89,c_402])).

tff(c_745,plain,(
    ! [D_367,B_368,C_26] :
      ( r3_orders_2('#skF_9',D_367,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)),C_26))
      | ~ r3_waybel_9('#skF_9',B_368,D_367)
      | ~ m1_subset_1(D_367,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_368,'#skF_9')
      | ~ v7_waybel_0(B_368)
      | ~ v4_orders_2(B_368)
      | v2_struct_0(B_368)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_368,D_367,D_367),u1_struct_0('#skF_9'))
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)),C_26)
      | ~ m1_subset_1(C_26,u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_742])).

tff(c_748,plain,(
    ! [D_367,B_368,C_26] :
      ( r3_orders_2('#skF_9',D_367,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)),C_26))
      | ~ r3_waybel_9('#skF_9',B_368,D_367)
      | ~ m1_subset_1(D_367,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_368,'#skF_9')
      | ~ v7_waybel_0(B_368)
      | ~ v4_orders_2(B_368)
      | v2_struct_0(B_368)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_368,D_367,D_367),u1_struct_0('#skF_9'))
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)),C_26)
      | ~ m1_subset_1(C_26,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89,c_745])).

tff(c_1264,plain,(
    ! [D_491,B_490,C_26,C_492] :
      ( r3_orders_2('#skF_9',D_491,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)),C_26))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)),C_26)
      | ~ m1_subset_1(C_26,u1_struct_0('#skF_9'))
      | r3_orders_2('#skF_9',D_491,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)),C_492))
      | ~ r3_waybel_9('#skF_9',B_490,D_491)
      | ~ m1_subset_1(D_491,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_490,'#skF_9')
      | ~ v7_waybel_0(B_490)
      | ~ v4_orders_2(B_490)
      | v2_struct_0(B_490)
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)),C_492)
      | ~ m1_subset_1(C_492,u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1261,c_748])).

tff(c_1274,plain,(
    ! [D_491,B_490,C_26,C_492] :
      ( r3_orders_2('#skF_9',D_491,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)),C_26))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)),C_26)
      | ~ m1_subset_1(C_26,u1_struct_0('#skF_9'))
      | r3_orders_2('#skF_9',D_491,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)),C_492))
      | ~ r3_waybel_9('#skF_9',B_490,D_491)
      | ~ m1_subset_1(D_491,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_490,'#skF_9')
      | ~ v7_waybel_0(B_490)
      | ~ v4_orders_2(B_490)
      | v2_struct_0(B_490)
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_490),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_490)),C_492)
      | ~ m1_subset_1(C_492,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89,c_84,c_82,c_80,c_78,c_74,c_72,c_70,c_68,c_1264])).

tff(c_1336,plain,(
    ! [B_505,D_506,C_507] :
      ( ~ r3_waybel_9('#skF_9',B_505,D_506)
      | ~ m1_subset_1(D_506,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_505,'#skF_9')
      | ~ v7_waybel_0(B_505)
      | ~ v4_orders_2(B_505)
      | v2_struct_0(B_505)
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)),C_507)
      | ~ m1_subset_1(C_507,u1_struct_0('#skF_9'))
      | r3_orders_2('#skF_9',D_506,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)),C_507)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1274])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_orders_2(A_1,B_2,C_3)
      | ~ r3_orders_2(A_1,B_2,C_3)
      | ~ m1_subset_1(C_3,u1_struct_0(A_1))
      | ~ m1_subset_1(B_2,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1338,plain,(
    ! [D_506,B_505,C_507] :
      ( r1_orders_2('#skF_9',D_506,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)),C_507))
      | ~ m1_subset_1('#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)),C_507),u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9',B_505,D_506)
      | ~ m1_subset_1(D_506,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_505,'#skF_9')
      | ~ v7_waybel_0(B_505)
      | ~ v4_orders_2(B_505)
      | v2_struct_0(B_505)
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)),C_507)
      | ~ m1_subset_1(C_507,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1336,c_4])).

tff(c_1341,plain,(
    ! [D_506,B_505,C_507] :
      ( r1_orders_2('#skF_9',D_506,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)),C_507))
      | ~ m1_subset_1('#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)),C_507),u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9',B_505,D_506)
      | ~ m1_subset_1(D_506,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_505,'#skF_9')
      | ~ v7_waybel_0(B_505)
      | ~ v4_orders_2(B_505)
      | v2_struct_0(B_505)
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_505),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_505)),C_507)
      | ~ m1_subset_1(C_507,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_89,c_1338])).

tff(c_1343,plain,(
    ! [D_508,B_509,C_510] :
      ( r1_orders_2('#skF_9',D_508,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_509),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_509)),C_510))
      | ~ m1_subset_1('#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_509),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_509)),C_510),u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9',B_509,D_508)
      | ~ m1_subset_1(D_508,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_509,'#skF_9')
      | ~ v7_waybel_0(B_509)
      | ~ v4_orders_2(B_509)
      | v2_struct_0(B_509)
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_509),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_509)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_509),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_509)),C_510)
      | ~ m1_subset_1(C_510,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_1341])).

tff(c_1346,plain,(
    ! [D_508,B_509,C_26] :
      ( r1_orders_2('#skF_9',D_508,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_509),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_509)),C_26))
      | ~ r3_waybel_9('#skF_9',B_509,D_508)
      | ~ m1_subset_1(D_508,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_509,'#skF_9')
      | ~ v7_waybel_0(B_509)
      | ~ v4_orders_2(B_509)
      | v2_struct_0(B_509)
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_509),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_509)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_509),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_509)),C_26)
      | ~ m1_subset_1(C_26,u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_1343])).

tff(c_1350,plain,(
    ! [D_511,B_512,C_513] :
      ( r1_orders_2('#skF_9',D_511,'#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_512),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_512)),C_513))
      | ~ r3_waybel_9('#skF_9',B_512,D_511)
      | ~ m1_subset_1(D_511,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_512,'#skF_9')
      | ~ v7_waybel_0(B_512)
      | ~ v4_orders_2(B_512)
      | v2_struct_0(B_512)
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_512),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_512)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_512),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_512)),C_513)
      | ~ m1_subset_1(C_513,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89,c_1346])).

tff(c_14,plain,(
    ! [A_5,C_26,B_19] :
      ( ~ r1_orders_2(A_5,C_26,'#skF_1'(A_5,B_19,C_26))
      | r1_yellow_0(A_5,B_19)
      | ~ r2_lattice3(A_5,B_19,C_26)
      | ~ m1_subset_1(C_26,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1354,plain,(
    ! [B_512,C_513] :
      ( ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ r3_waybel_9('#skF_9',B_512,C_513)
      | ~ l1_waybel_0(B_512,'#skF_9')
      | ~ v7_waybel_0(B_512)
      | ~ v4_orders_2(B_512)
      | v2_struct_0(B_512)
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_512),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_512)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_512),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_512)),C_513)
      | ~ m1_subset_1(C_513,u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_1350,c_14])).

tff(c_1358,plain,(
    ! [B_514,C_515] :
      ( ~ r3_waybel_9('#skF_9',B_514,C_515)
      | ~ l1_waybel_0(B_514,'#skF_9')
      | ~ v7_waybel_0(B_514)
      | ~ v4_orders_2(B_514)
      | v2_struct_0(B_514)
      | r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_514),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_514)))
      | ~ r2_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_514),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_514)),C_515)
      | ~ m1_subset_1(C_515,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89,c_1354])).

tff(c_1408,plain,(
    ! [B_521,D_522] :
      ( r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_521),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_521)))
      | ~ r3_waybel_9('#skF_9',B_521,D_522)
      | ~ v10_waybel_0(B_521,'#skF_9')
      | ~ m1_subset_1(D_522,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_521,'#skF_9')
      | ~ v7_waybel_0(B_521)
      | ~ v4_orders_2(B_521)
      | v2_struct_0(B_521) ) ),
    inference(resolution,[status(thm)],[c_245,c_1358])).

tff(c_1417,plain,(
    ! [B_114] :
      ( r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_114),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_114)))
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_114),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_1408])).

tff(c_1428,plain,(
    ! [B_114] :
      ( r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_114),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_114)))
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_114),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1417])).

tff(c_1430,plain,(
    ! [B_523] :
      ( r1_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_523),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_523)))
      | ~ v10_waybel_0(B_523,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_523),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_523,'#skF_9')
      | ~ v7_waybel_0(B_523)
      | ~ v4_orders_2(B_523)
      | v2_struct_0(B_523) ) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_1428])).

tff(c_20,plain,(
    ! [A_30,B_32] :
      ( r1_waybel_9(A_30,B_32)
      | ~ r1_yellow_0(A_30,k2_relset_1(u1_struct_0(B_32),u1_struct_0(A_30),u1_waybel_0(A_30,B_32)))
      | ~ l1_waybel_0(B_32,A_30)
      | ~ l1_orders_2(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1433,plain,(
    ! [B_523] :
      ( r1_waybel_9('#skF_9',B_523)
      | ~ l1_orders_2('#skF_9')
      | ~ v10_waybel_0(B_523,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_523),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_523,'#skF_9')
      | ~ v7_waybel_0(B_523)
      | ~ v4_orders_2(B_523)
      | v2_struct_0(B_523) ) ),
    inference(resolution,[status(thm)],[c_1430,c_20])).

tff(c_1437,plain,(
    ! [B_524] :
      ( r1_waybel_9('#skF_9',B_524)
      | ~ v10_waybel_0(B_524,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_524),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_524,'#skF_9')
      | ~ v7_waybel_0(B_524)
      | ~ v4_orders_2(B_524)
      | v2_struct_0(B_524) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1433])).

tff(c_1441,plain,(
    ! [B_114] :
      ( r1_waybel_9('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_38,c_1437])).

tff(c_1444,plain,(
    ! [B_114] :
      ( r1_waybel_9('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1441])).

tff(c_1468,plain,(
    ! [B_530] :
      ( r1_waybel_9('#skF_9',B_530)
      | ~ v10_waybel_0(B_530,'#skF_9')
      | ~ l1_waybel_0(B_530,'#skF_9')
      | ~ v7_waybel_0(B_530)
      | ~ v4_orders_2(B_530)
      | v2_struct_0(B_530) ) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_1444])).

tff(c_1471,plain,
    ( r1_waybel_9('#skF_9','#skF_10')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_56,c_1468])).

tff(c_1474,plain,
    ( r1_waybel_9('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1471])).

tff(c_1476,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_97,c_1474])).

tff(c_1477,plain,(
    ~ r2_hidden(k1_waybel_2('#skF_9','#skF_10'),k10_yellow_6('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1514,plain,
    ( m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_2('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1509,c_1477])).

tff(c_1518,plain,
    ( m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_2('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1514])).

tff(c_1519,plain,
    ( m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_2('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1518])).

tff(c_1520,plain,(
    ~ m1_subset_1(k1_waybel_2('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1519])).

tff(c_1644,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1638,c_1520])).

tff(c_1652,plain,
    ( ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_1644])).

tff(c_1655,plain,
    ( v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1652])).

tff(c_1657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1621,c_64,c_1655])).

tff(c_1659,plain,(
    m1_subset_1(k1_waybel_2('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1519])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r3_orders_2(A_1,B_2,C_3)
      | ~ r1_orders_2(A_1,B_2,C_3)
      | ~ m1_subset_1(C_3,u1_struct_0(A_1))
      | ~ m1_subset_1(B_2,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1661,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_9',B_2,k1_waybel_2('#skF_9','#skF_10'))
      | ~ r1_orders_2('#skF_9',B_2,k1_waybel_2('#skF_9','#skF_10'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1659,c_2])).

tff(c_1664,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_9',B_2,k1_waybel_2('#skF_9','#skF_10'))
      | ~ r1_orders_2('#skF_9',B_2,k1_waybel_2('#skF_9','#skF_10'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_89,c_1661])).

tff(c_1666,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1664])).

tff(c_1669,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_1666,c_6])).

tff(c_1673,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_74,c_1669])).

tff(c_1675,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1664])).

tff(c_1739,plain,(
    ! [A_633,B_634,C_635] :
      ( ~ v5_pre_topc(k4_waybel_1(A_633,'#skF_8'(A_633,B_634,C_635)),A_633,A_633)
      | k1_waybel_2(A_633,C_635) = B_634
      | ~ r3_waybel_9(A_633,C_635,B_634)
      | ~ v10_waybel_0(C_635,A_633)
      | ~ l1_waybel_0(C_635,A_633)
      | ~ v7_waybel_0(C_635)
      | ~ v4_orders_2(C_635)
      | v2_struct_0(C_635)
      | ~ m1_subset_1(B_634,u1_struct_0(A_633))
      | ~ l1_waybel_9(A_633)
      | ~ v1_compts_1(A_633)
      | ~ v2_lattice3(A_633)
      | ~ v1_lattice3(A_633)
      | ~ v5_orders_2(A_633)
      | ~ v4_orders_2(A_633)
      | ~ v3_orders_2(A_633)
      | ~ v8_pre_topc(A_633)
      | ~ v2_pre_topc(A_633) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1743,plain,(
    ! [C_635,B_634] :
      ( k1_waybel_2('#skF_9',C_635) = B_634
      | ~ r3_waybel_9('#skF_9',C_635,B_634)
      | ~ v10_waybel_0(C_635,'#skF_9')
      | ~ l1_waybel_0(C_635,'#skF_9')
      | ~ v7_waybel_0(C_635)
      | ~ v4_orders_2(C_635)
      | v2_struct_0(C_635)
      | ~ m1_subset_1(B_634,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_8'('#skF_9',B_634,C_635),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_66,c_1739])).

tff(c_1752,plain,(
    ! [C_639,B_640] :
      ( k1_waybel_2('#skF_9',C_639) = B_640
      | ~ r3_waybel_9('#skF_9',C_639,B_640)
      | ~ v10_waybel_0(C_639,'#skF_9')
      | ~ l1_waybel_0(C_639,'#skF_9')
      | ~ v7_waybel_0(C_639)
      | ~ v4_orders_2(C_639)
      | v2_struct_0(C_639)
      | ~ m1_subset_1(B_640,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_8'('#skF_9',B_640,C_639),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1743])).

tff(c_1756,plain,(
    ! [C_145,B_141] :
      ( k1_waybel_2('#skF_9',C_145) = B_141
      | ~ r3_waybel_9('#skF_9',C_145,B_141)
      | ~ v10_waybel_0(C_145,'#skF_9')
      | ~ l1_waybel_0(C_145,'#skF_9')
      | ~ v7_waybel_0(C_145)
      | ~ v4_orders_2(C_145)
      | v2_struct_0(C_145)
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_1752])).

tff(c_1760,plain,(
    ! [C_641,B_642] :
      ( k1_waybel_2('#skF_9',C_641) = B_642
      | ~ r3_waybel_9('#skF_9',C_641,B_642)
      | ~ v10_waybel_0(C_641,'#skF_9')
      | ~ l1_waybel_0(C_641,'#skF_9')
      | ~ v7_waybel_0(C_641)
      | ~ v4_orders_2(C_641)
      | v2_struct_0(C_641)
      | ~ m1_subset_1(B_642,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1756])).

tff(c_1769,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_114),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_36,c_1760])).

tff(c_1780,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_114),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1769])).

tff(c_1782,plain,(
    ! [B_643] :
      ( k1_waybel_2('#skF_9',B_643) = '#skF_5'('#skF_9',B_643)
      | ~ v10_waybel_0(B_643,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_643),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_643,'#skF_9')
      | ~ v7_waybel_0(B_643)
      | ~ v4_orders_2(B_643)
      | v2_struct_0(B_643) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1675,c_1780])).

tff(c_1786,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_38,c_1782])).

tff(c_1789,plain,(
    ! [B_114] :
      ( k1_waybel_2('#skF_9',B_114) = '#skF_5'('#skF_9',B_114)
      | ~ v10_waybel_0(B_114,'#skF_9')
      | ~ l1_waybel_0(B_114,'#skF_9')
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1786])).

tff(c_1791,plain,(
    ! [B_644] :
      ( k1_waybel_2('#skF_9',B_644) = '#skF_5'('#skF_9',B_644)
      | ~ v10_waybel_0(B_644,'#skF_9')
      | ~ l1_waybel_0(B_644,'#skF_9')
      | ~ v7_waybel_0(B_644)
      | ~ v4_orders_2(B_644)
      | v2_struct_0(B_644) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1675,c_1789])).

tff(c_1794,plain,
    ( k1_waybel_2('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_56,c_1791])).

tff(c_1797,plain,
    ( k1_waybel_2('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1794])).

tff(c_1798,plain,(
    k1_waybel_2('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1797])).

tff(c_1658,plain,
    ( ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10'))
    | v2_struct_0('#skF_9')
    | m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1519])).

tff(c_1665,plain,(
    ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1658])).

tff(c_1800,plain,(
    ~ r3_waybel_9('#skF_9','#skF_10','#skF_5'('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1798,c_1665])).

tff(c_1815,plain,
    ( ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_1800])).

tff(c_1818,plain,
    ( v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1815])).

tff(c_1820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1675,c_64,c_1818])).

tff(c_1821,plain,
    ( m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1658])).

tff(c_1823,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1821])).

tff(c_1834,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_1823,c_6])).

tff(c_1838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_74,c_1834])).

tff(c_1840,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1821])).

tff(c_1822,plain,(
    r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1658])).

tff(c_1886,plain,(
    ! [A_663,B_664,C_665] :
      ( '#skF_6'(A_663,B_664) != '#skF_7'(A_663,B_664)
      | r2_hidden(C_665,k10_yellow_6(A_663,B_664))
      | ~ r3_waybel_9(A_663,B_664,C_665)
      | ~ m1_subset_1(C_665,u1_struct_0(A_663))
      | ~ l1_waybel_0(B_664,A_663)
      | ~ v7_waybel_0(B_664)
      | ~ v4_orders_2(B_664)
      | v2_struct_0(B_664)
      | ~ l1_pre_topc(A_663)
      | ~ v1_compts_1(A_663)
      | ~ v8_pre_topc(A_663)
      | ~ v2_pre_topc(A_663)
      | v2_struct_0(A_663) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1889,plain,
    ( '#skF_6'('#skF_9','#skF_10') != '#skF_7'('#skF_9','#skF_10')
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_2('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1886,c_1477])).

tff(c_1892,plain,
    ( '#skF_6'('#skF_9','#skF_10') != '#skF_7'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1659,c_1822,c_1889])).

tff(c_1893,plain,(
    '#skF_6'('#skF_9','#skF_10') != '#skF_7'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_1840,c_64,c_1892])).

tff(c_1894,plain,(
    ! [A_666,B_667,C_668] :
      ( m1_subset_1('#skF_7'(A_666,B_667),u1_struct_0(A_666))
      | r2_hidden(C_668,k10_yellow_6(A_666,B_667))
      | ~ r3_waybel_9(A_666,B_667,C_668)
      | ~ m1_subset_1(C_668,u1_struct_0(A_666))
      | ~ l1_waybel_0(B_667,A_666)
      | ~ v7_waybel_0(B_667)
      | ~ v4_orders_2(B_667)
      | v2_struct_0(B_667)
      | ~ l1_pre_topc(A_666)
      | ~ v1_compts_1(A_666)
      | ~ v8_pre_topc(A_666)
      | ~ v2_pre_topc(A_666)
      | v2_struct_0(A_666) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1899,plain,
    ( m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_2('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1894,c_1477])).

tff(c_1903,plain,
    ( m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1659,c_1822,c_1899])).

tff(c_1904,plain,(
    m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_1840,c_64,c_1903])).

tff(c_1870,plain,(
    ! [A_657,B_658,C_659] :
      ( r3_waybel_9(A_657,B_658,'#skF_7'(A_657,B_658))
      | r2_hidden(C_659,k10_yellow_6(A_657,B_658))
      | ~ r3_waybel_9(A_657,B_658,C_659)
      | ~ m1_subset_1(C_659,u1_struct_0(A_657))
      | ~ l1_waybel_0(B_658,A_657)
      | ~ v7_waybel_0(B_658)
      | ~ v4_orders_2(B_658)
      | v2_struct_0(B_658)
      | ~ l1_pre_topc(A_657)
      | ~ v1_compts_1(A_657)
      | ~ v8_pre_topc(A_657)
      | ~ v2_pre_topc(A_657)
      | v2_struct_0(A_657) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1873,plain,
    ( r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9','#skF_10'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_2('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1870,c_1477])).

tff(c_1876,plain,
    ( r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9','#skF_10'))
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1659,c_1822,c_1873])).

tff(c_1877,plain,(
    r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_1840,c_64,c_1876])).

tff(c_1931,plain,(
    ! [A_679,B_680,C_681] :
      ( ~ v5_pre_topc(k4_waybel_1(A_679,'#skF_8'(A_679,B_680,C_681)),A_679,A_679)
      | k1_waybel_2(A_679,C_681) = B_680
      | ~ r3_waybel_9(A_679,C_681,B_680)
      | ~ v10_waybel_0(C_681,A_679)
      | ~ l1_waybel_0(C_681,A_679)
      | ~ v7_waybel_0(C_681)
      | ~ v4_orders_2(C_681)
      | v2_struct_0(C_681)
      | ~ m1_subset_1(B_680,u1_struct_0(A_679))
      | ~ l1_waybel_9(A_679)
      | ~ v1_compts_1(A_679)
      | ~ v2_lattice3(A_679)
      | ~ v1_lattice3(A_679)
      | ~ v5_orders_2(A_679)
      | ~ v4_orders_2(A_679)
      | ~ v3_orders_2(A_679)
      | ~ v8_pre_topc(A_679)
      | ~ v2_pre_topc(A_679) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1935,plain,(
    ! [C_681,B_680] :
      ( k1_waybel_2('#skF_9',C_681) = B_680
      | ~ r3_waybel_9('#skF_9',C_681,B_680)
      | ~ v10_waybel_0(C_681,'#skF_9')
      | ~ l1_waybel_0(C_681,'#skF_9')
      | ~ v7_waybel_0(C_681)
      | ~ v4_orders_2(C_681)
      | v2_struct_0(C_681)
      | ~ m1_subset_1(B_680,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_8'('#skF_9',B_680,C_681),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_66,c_1931])).

tff(c_1939,plain,(
    ! [C_682,B_683] :
      ( k1_waybel_2('#skF_9',C_682) = B_683
      | ~ r3_waybel_9('#skF_9',C_682,B_683)
      | ~ v10_waybel_0(C_682,'#skF_9')
      | ~ l1_waybel_0(C_682,'#skF_9')
      | ~ v7_waybel_0(C_682)
      | ~ v4_orders_2(C_682)
      | v2_struct_0(C_682)
      | ~ m1_subset_1(B_683,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_8'('#skF_9',B_683,C_682),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1935])).

tff(c_1943,plain,(
    ! [C_145,B_141] :
      ( k1_waybel_2('#skF_9',C_145) = B_141
      | ~ r3_waybel_9('#skF_9',C_145,B_141)
      | ~ v10_waybel_0(C_145,'#skF_9')
      | ~ l1_waybel_0(C_145,'#skF_9')
      | ~ v7_waybel_0(C_145)
      | ~ v4_orders_2(C_145)
      | v2_struct_0(C_145)
      | ~ m1_subset_1(B_141,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_52,c_1939])).

tff(c_1947,plain,(
    ! [C_684,B_685] :
      ( k1_waybel_2('#skF_9',C_684) = B_685
      | ~ r3_waybel_9('#skF_9',C_684,B_685)
      | ~ v10_waybel_0(C_684,'#skF_9')
      | ~ l1_waybel_0(C_684,'#skF_9')
      | ~ v7_waybel_0(C_684)
      | ~ v4_orders_2(C_684)
      | v2_struct_0(C_684)
      | ~ m1_subset_1(B_685,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1943])).

tff(c_1954,plain,
    ( k1_waybel_2('#skF_9','#skF_10') = '#skF_7'('#skF_9','#skF_10')
    | ~ v10_waybel_0('#skF_10','#skF_9')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_1877,c_1947])).

tff(c_1973,plain,
    ( k1_waybel_2('#skF_9','#skF_10') = '#skF_7'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1904,c_62,c_60,c_58,c_56,c_1954])).

tff(c_1974,plain,(
    k1_waybel_2('#skF_9','#skF_10') = '#skF_7'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1973])).

tff(c_1839,plain,(
    m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1821])).

tff(c_1878,plain,(
    ! [A_660,B_661,C_662] :
      ( r3_waybel_9(A_660,B_661,'#skF_6'(A_660,B_661))
      | r2_hidden(C_662,k10_yellow_6(A_660,B_661))
      | ~ r3_waybel_9(A_660,B_661,C_662)
      | ~ m1_subset_1(C_662,u1_struct_0(A_660))
      | ~ l1_waybel_0(B_661,A_660)
      | ~ v7_waybel_0(B_661)
      | ~ v4_orders_2(B_661)
      | v2_struct_0(B_661)
      | ~ l1_pre_topc(A_660)
      | ~ v1_compts_1(A_660)
      | ~ v8_pre_topc(A_660)
      | ~ v2_pre_topc(A_660)
      | v2_struct_0(A_660) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1881,plain,
    ( r3_waybel_9('#skF_9','#skF_10','#skF_6'('#skF_9','#skF_10'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_2('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_2('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1878,c_1477])).

tff(c_1884,plain,
    ( r3_waybel_9('#skF_9','#skF_10','#skF_6'('#skF_9','#skF_10'))
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1659,c_1822,c_1881])).

tff(c_1885,plain,(
    r3_waybel_9('#skF_9','#skF_10','#skF_6'('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_1840,c_64,c_1884])).

tff(c_1949,plain,
    ( k1_waybel_2('#skF_9','#skF_10') = '#skF_6'('#skF_9','#skF_10')
    | ~ v10_waybel_0('#skF_10','#skF_9')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_1885,c_1947])).

tff(c_1965,plain,
    ( k1_waybel_2('#skF_9','#skF_10') = '#skF_6'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1839,c_62,c_60,c_58,c_56,c_1949])).

tff(c_1966,plain,(
    k1_waybel_2('#skF_9','#skF_10') = '#skF_6'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1965])).

tff(c_1998,plain,(
    '#skF_6'('#skF_9','#skF_10') = '#skF_7'('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1974,c_1966])).

tff(c_2000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1893,c_1998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.07/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.26/2.14  
% 6.26/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.14  %$ v5_pre_topc > r3_waybel_9 > r3_orders_2 > r2_lattice3 > r1_orders_2 > v10_waybel_0 > r2_hidden > r1_yellow_0 > r1_waybel_9 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_compts_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_waybel_1 > k1_waybel_2 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_6 > #skF_1 > #skF_10 > #skF_9 > #skF_4 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 6.34/2.14  
% 6.34/2.14  %Foreground sorts:
% 6.34/2.14  
% 6.34/2.14  
% 6.34/2.14  %Background operators:
% 6.34/2.14  
% 6.34/2.14  
% 6.34/2.14  %Foreground operators:
% 6.34/2.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.34/2.14  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.34/2.14  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 6.34/2.14  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 6.34/2.14  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.34/2.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.34/2.14  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.34/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.34/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.34/2.14  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.34/2.14  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 6.34/2.14  tff(v10_waybel_0, type, v10_waybel_0: ($i * $i) > $o).
% 6.34/2.14  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.34/2.14  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 6.34/2.14  tff('#skF_10', type, '#skF_10': $i).
% 6.34/2.14  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 6.34/2.14  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 6.34/2.14  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 6.34/2.14  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.34/2.14  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 6.34/2.14  tff('#skF_9', type, '#skF_9': $i).
% 6.34/2.14  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.34/2.14  tff(r1_waybel_9, type, r1_waybel_9: ($i * $i) > $o).
% 6.34/2.14  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 6.34/2.14  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.34/2.14  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 6.34/2.14  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 6.34/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.34/2.14  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 6.34/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.34/2.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.34/2.14  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 6.34/2.14  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.34/2.14  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 6.34/2.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.34/2.14  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 6.34/2.14  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.34/2.14  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.34/2.14  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 6.34/2.14  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.34/2.14  tff(k1_waybel_2, type, k1_waybel_2: ($i * $i) > $i).
% 6.34/2.14  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 6.34/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.34/2.14  
% 6.34/2.19  tff(f_326, negated_conjecture, ~(![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => ((![B]: (m1_subset_1(B, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, B), A, A))) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v10_waybel_0(B, A) => (r1_waybel_9(A, B) & r2_hidden(k1_waybel_2(A, B), k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_waybel_9)).
% 6.34/2.19  tff(f_81, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 6.34/2.19  tff(f_204, axiom, (![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_waybel_9)).
% 6.34/2.19  tff(f_286, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => ((((![D]: (m1_subset_1(D, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, D), A, A))) & v10_waybel_0(C, A)) & r3_waybel_9(A, C, B)) => (B = k1_waybel_2(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_waybel_9)).
% 6.34/2.19  tff(f_47, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 6.34/2.19  tff(f_244, axiom, (![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r3_waybel_9(A, B, C) & r3_waybel_9(A, B, D)) => (C = D)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) => r2_hidden(C, k10_yellow_6(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_waybel_9)).
% 6.34/2.19  tff(f_128, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & v10_waybel_0(B, A)) & r3_waybel_9(A, B, C)) => r2_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l48_waybel_9)).
% 6.34/2.19  tff(f_66, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (r1_yellow_0(A, B) <=> (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r2_lattice3(A, B, C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, B, D) => r1_orders_2(A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_yellow_0)).
% 6.34/2.19  tff(f_178, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & r3_waybel_9(A, B, C)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r2_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), E) => r3_orders_2(A, D, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_waybel_9)).
% 6.34/2.19  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 6.34/2.19  tff(f_75, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_waybel_0(B, A) => (r1_waybel_9(A, B) <=> r1_yellow_0(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_waybel_9)).
% 6.34/2.19  tff(c_68, plain, (l1_waybel_9('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_85, plain, (![A_150]: (l1_orders_2(A_150) | ~l1_waybel_9(A_150))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.34/2.19  tff(c_89, plain, (l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_68, c_85])).
% 6.34/2.19  tff(c_74, plain, (v1_lattice3('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_80, plain, (v3_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_84, plain, (v2_pre_topc('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_82, plain, (v8_pre_topc('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_70, plain, (v1_compts_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_90, plain, (![A_151]: (l1_pre_topc(A_151) | ~l1_waybel_9(A_151))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.34/2.19  tff(c_94, plain, (l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_68, c_90])).
% 6.34/2.19  tff(c_36, plain, (![A_110, B_114]: (r3_waybel_9(A_110, B_114, '#skF_5'(A_110, B_114)) | ~l1_waybel_0(B_114, A_110) | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | ~l1_pre_topc(A_110) | ~v1_compts_1(A_110) | ~v8_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.34/2.19  tff(c_78, plain, (v4_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_76, plain, (v5_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_72, plain, (v2_lattice3('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_52, plain, (![A_133, B_141, C_145]: (m1_subset_1('#skF_8'(A_133, B_141, C_145), u1_struct_0(A_133)) | k1_waybel_2(A_133, C_145)=B_141 | ~r3_waybel_9(A_133, C_145, B_141) | ~v10_waybel_0(C_145, A_133) | ~l1_waybel_0(C_145, A_133) | ~v7_waybel_0(C_145) | ~v4_orders_2(C_145) | v2_struct_0(C_145) | ~m1_subset_1(B_141, u1_struct_0(A_133)) | ~l1_waybel_9(A_133) | ~v1_compts_1(A_133) | ~v2_lattice3(A_133) | ~v1_lattice3(A_133) | ~v5_orders_2(A_133) | ~v4_orders_2(A_133) | ~v3_orders_2(A_133) | ~v8_pre_topc(A_133) | ~v2_pre_topc(A_133))), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.34/2.19  tff(c_66, plain, (![B_149]: (v5_pre_topc(k4_waybel_1('#skF_9', B_149), '#skF_9', '#skF_9') | ~m1_subset_1(B_149, u1_struct_0('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_1577, plain, (![A_592, B_593, C_594]: (~v5_pre_topc(k4_waybel_1(A_592, '#skF_8'(A_592, B_593, C_594)), A_592, A_592) | k1_waybel_2(A_592, C_594)=B_593 | ~r3_waybel_9(A_592, C_594, B_593) | ~v10_waybel_0(C_594, A_592) | ~l1_waybel_0(C_594, A_592) | ~v7_waybel_0(C_594) | ~v4_orders_2(C_594) | v2_struct_0(C_594) | ~m1_subset_1(B_593, u1_struct_0(A_592)) | ~l1_waybel_9(A_592) | ~v1_compts_1(A_592) | ~v2_lattice3(A_592) | ~v1_lattice3(A_592) | ~v5_orders_2(A_592) | ~v4_orders_2(A_592) | ~v3_orders_2(A_592) | ~v8_pre_topc(A_592) | ~v2_pre_topc(A_592))), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.34/2.19  tff(c_1581, plain, (![C_594, B_593]: (k1_waybel_2('#skF_9', C_594)=B_593 | ~r3_waybel_9('#skF_9', C_594, B_593) | ~v10_waybel_0(C_594, '#skF_9') | ~l1_waybel_0(C_594, '#skF_9') | ~v7_waybel_0(C_594) | ~v4_orders_2(C_594) | v2_struct_0(C_594) | ~m1_subset_1(B_593, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_8'('#skF_9', B_593, C_594), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_66, c_1577])).
% 6.34/2.19  tff(c_1585, plain, (![C_595, B_596]: (k1_waybel_2('#skF_9', C_595)=B_596 | ~r3_waybel_9('#skF_9', C_595, B_596) | ~v10_waybel_0(C_595, '#skF_9') | ~l1_waybel_0(C_595, '#skF_9') | ~v7_waybel_0(C_595) | ~v4_orders_2(C_595) | v2_struct_0(C_595) | ~m1_subset_1(B_596, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_8'('#skF_9', B_596, C_595), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1581])).
% 6.34/2.19  tff(c_1589, plain, (![C_145, B_141]: (k1_waybel_2('#skF_9', C_145)=B_141 | ~r3_waybel_9('#skF_9', C_145, B_141) | ~v10_waybel_0(C_145, '#skF_9') | ~l1_waybel_0(C_145, '#skF_9') | ~v7_waybel_0(C_145) | ~v4_orders_2(C_145) | v2_struct_0(C_145) | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_1585])).
% 6.34/2.19  tff(c_1593, plain, (![C_597, B_598]: (k1_waybel_2('#skF_9', C_597)=B_598 | ~r3_waybel_9('#skF_9', C_597, B_598) | ~v10_waybel_0(C_597, '#skF_9') | ~l1_waybel_0(C_597, '#skF_9') | ~v7_waybel_0(C_597) | ~v4_orders_2(C_597) | v2_struct_0(C_597) | ~m1_subset_1(B_598, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1589])).
% 6.34/2.19  tff(c_1602, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_114), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_1593])).
% 6.34/2.19  tff(c_1611, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_114), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1602])).
% 6.34/2.19  tff(c_1612, plain, (v2_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1611])).
% 6.34/2.19  tff(c_6, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.34/2.19  tff(c_1615, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_1612, c_6])).
% 6.34/2.19  tff(c_1619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_74, c_1615])).
% 6.34/2.19  tff(c_1621, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1611])).
% 6.34/2.19  tff(c_64, plain, (~v2_struct_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_62, plain, (v4_orders_2('#skF_10')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_60, plain, (v7_waybel_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_58, plain, (l1_waybel_0('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_38, plain, (![A_110, B_114]: (m1_subset_1('#skF_5'(A_110, B_114), u1_struct_0(A_110)) | ~l1_waybel_0(B_114, A_110) | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | ~l1_pre_topc(A_110) | ~v1_compts_1(A_110) | ~v8_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_204])).
% 6.34/2.19  tff(c_56, plain, (v10_waybel_0('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_1622, plain, (![B_599]: (k1_waybel_2('#skF_9', B_599)='#skF_5'('#skF_9', B_599) | ~v10_waybel_0(B_599, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_599), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_599, '#skF_9') | ~v7_waybel_0(B_599) | ~v4_orders_2(B_599) | v2_struct_0(B_599))), inference(splitRight, [status(thm)], [c_1611])).
% 6.34/2.19  tff(c_1626, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_38, c_1622])).
% 6.34/2.19  tff(c_1629, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1626])).
% 6.34/2.19  tff(c_1631, plain, (![B_600]: (k1_waybel_2('#skF_9', B_600)='#skF_5'('#skF_9', B_600) | ~v10_waybel_0(B_600, '#skF_9') | ~l1_waybel_0(B_600, '#skF_9') | ~v7_waybel_0(B_600) | ~v4_orders_2(B_600) | v2_struct_0(B_600))), inference(negUnitSimplification, [status(thm)], [c_1621, c_1629])).
% 6.34/2.19  tff(c_1634, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_56, c_1631])).
% 6.34/2.19  tff(c_1637, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1634])).
% 6.34/2.19  tff(c_1638, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_64, c_1637])).
% 6.34/2.19  tff(c_1509, plain, (![A_561, B_562, C_563]: (m1_subset_1('#skF_6'(A_561, B_562), u1_struct_0(A_561)) | r2_hidden(C_563, k10_yellow_6(A_561, B_562)) | ~r3_waybel_9(A_561, B_562, C_563) | ~m1_subset_1(C_563, u1_struct_0(A_561)) | ~l1_waybel_0(B_562, A_561) | ~v7_waybel_0(B_562) | ~v4_orders_2(B_562) | v2_struct_0(B_562) | ~l1_pre_topc(A_561) | ~v1_compts_1(A_561) | ~v8_pre_topc(A_561) | ~v2_pre_topc(A_561) | v2_struct_0(A_561))), inference(cnfTransformation, [status(thm)], [f_244])).
% 6.34/2.19  tff(c_54, plain, (~r2_hidden(k1_waybel_2('#skF_9', '#skF_10'), k10_yellow_6('#skF_9', '#skF_10')) | ~r1_waybel_9('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_326])).
% 6.34/2.19  tff(c_97, plain, (~r1_waybel_9('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_54])).
% 6.34/2.19  tff(c_160, plain, (![A_215, B_216, C_217]: (~v5_pre_topc(k4_waybel_1(A_215, '#skF_8'(A_215, B_216, C_217)), A_215, A_215) | k1_waybel_2(A_215, C_217)=B_216 | ~r3_waybel_9(A_215, C_217, B_216) | ~v10_waybel_0(C_217, A_215) | ~l1_waybel_0(C_217, A_215) | ~v7_waybel_0(C_217) | ~v4_orders_2(C_217) | v2_struct_0(C_217) | ~m1_subset_1(B_216, u1_struct_0(A_215)) | ~l1_waybel_9(A_215) | ~v1_compts_1(A_215) | ~v2_lattice3(A_215) | ~v1_lattice3(A_215) | ~v5_orders_2(A_215) | ~v4_orders_2(A_215) | ~v3_orders_2(A_215) | ~v8_pre_topc(A_215) | ~v2_pre_topc(A_215))), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.34/2.19  tff(c_164, plain, (![C_217, B_216]: (k1_waybel_2('#skF_9', C_217)=B_216 | ~r3_waybel_9('#skF_9', C_217, B_216) | ~v10_waybel_0(C_217, '#skF_9') | ~l1_waybel_0(C_217, '#skF_9') | ~v7_waybel_0(C_217) | ~v4_orders_2(C_217) | v2_struct_0(C_217) | ~m1_subset_1(B_216, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_8'('#skF_9', B_216, C_217), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_66, c_160])).
% 6.34/2.19  tff(c_173, plain, (![C_221, B_222]: (k1_waybel_2('#skF_9', C_221)=B_222 | ~r3_waybel_9('#skF_9', C_221, B_222) | ~v10_waybel_0(C_221, '#skF_9') | ~l1_waybel_0(C_221, '#skF_9') | ~v7_waybel_0(C_221) | ~v4_orders_2(C_221) | v2_struct_0(C_221) | ~m1_subset_1(B_222, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_8'('#skF_9', B_222, C_221), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_164])).
% 6.34/2.19  tff(c_177, plain, (![C_145, B_141]: (k1_waybel_2('#skF_9', C_145)=B_141 | ~r3_waybel_9('#skF_9', C_145, B_141) | ~v10_waybel_0(C_145, '#skF_9') | ~l1_waybel_0(C_145, '#skF_9') | ~v7_waybel_0(C_145) | ~v4_orders_2(C_145) | v2_struct_0(C_145) | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_173])).
% 6.34/2.19  tff(c_181, plain, (![C_223, B_224]: (k1_waybel_2('#skF_9', C_223)=B_224 | ~r3_waybel_9('#skF_9', C_223, B_224) | ~v10_waybel_0(C_223, '#skF_9') | ~l1_waybel_0(C_223, '#skF_9') | ~v7_waybel_0(C_223) | ~v4_orders_2(C_223) | v2_struct_0(C_223) | ~m1_subset_1(B_224, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_177])).
% 6.34/2.19  tff(c_190, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_114), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_181])).
% 6.34/2.19  tff(c_199, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_114), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_190])).
% 6.34/2.19  tff(c_200, plain, (v2_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_199])).
% 6.34/2.19  tff(c_204, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_200, c_6])).
% 6.34/2.19  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_74, c_204])).
% 6.34/2.19  tff(c_210, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_199])).
% 6.34/2.19  tff(c_30, plain, (![A_34, B_50, D_62]: (m1_subset_1('#skF_3'(A_34, B_50, D_62, D_62), u1_struct_0(A_34)) | r2_lattice3(A_34, k2_relset_1(u1_struct_0(B_50), u1_struct_0(A_34), u1_waybel_0(A_34, B_50)), D_62) | ~r3_waybel_9(A_34, B_50, D_62) | ~v10_waybel_0(B_50, A_34) | ~m1_subset_1(D_62, u1_struct_0(A_34)) | ~l1_waybel_0(B_50, A_34) | ~v7_waybel_0(B_50) | ~v4_orders_2(B_50) | v2_struct_0(B_50) | ~l1_waybel_9(A_34) | ~v1_compts_1(A_34) | ~v2_lattice3(A_34) | ~v1_lattice3(A_34) | ~v5_orders_2(A_34) | ~v4_orders_2(A_34) | ~v3_orders_2(A_34) | ~v8_pre_topc(A_34) | ~v2_pre_topc(A_34))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.34/2.19  tff(c_232, plain, (![A_227, B_228, D_229]: (~v5_pre_topc(k4_waybel_1(A_227, '#skF_3'(A_227, B_228, D_229, D_229)), A_227, A_227) | r2_lattice3(A_227, k2_relset_1(u1_struct_0(B_228), u1_struct_0(A_227), u1_waybel_0(A_227, B_228)), D_229) | ~r3_waybel_9(A_227, B_228, D_229) | ~v10_waybel_0(B_228, A_227) | ~m1_subset_1(D_229, u1_struct_0(A_227)) | ~l1_waybel_0(B_228, A_227) | ~v7_waybel_0(B_228) | ~v4_orders_2(B_228) | v2_struct_0(B_228) | ~l1_waybel_9(A_227) | ~v1_compts_1(A_227) | ~v2_lattice3(A_227) | ~v1_lattice3(A_227) | ~v5_orders_2(A_227) | ~v4_orders_2(A_227) | ~v3_orders_2(A_227) | ~v8_pre_topc(A_227) | ~v2_pre_topc(A_227))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.34/2.19  tff(c_235, plain, (![B_228, D_229]: (r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_228), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_228)), D_229) | ~r3_waybel_9('#skF_9', B_228, D_229) | ~v10_waybel_0(B_228, '#skF_9') | ~m1_subset_1(D_229, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_228, '#skF_9') | ~v7_waybel_0(B_228) | ~v4_orders_2(B_228) | v2_struct_0(B_228) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_3'('#skF_9', B_228, D_229, D_229), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_66, c_232])).
% 6.34/2.19  tff(c_239, plain, (![B_230, D_231]: (r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_230), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_230)), D_231) | ~r3_waybel_9('#skF_9', B_230, D_231) | ~v10_waybel_0(B_230, '#skF_9') | ~m1_subset_1(D_231, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_230, '#skF_9') | ~v7_waybel_0(B_230) | ~v4_orders_2(B_230) | v2_struct_0(B_230) | ~m1_subset_1('#skF_3'('#skF_9', B_230, D_231, D_231), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_235])).
% 6.34/2.19  tff(c_242, plain, (![B_50, D_62]: (r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_50), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_50)), D_62) | ~r3_waybel_9('#skF_9', B_50, D_62) | ~v10_waybel_0(B_50, '#skF_9') | ~m1_subset_1(D_62, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_50, '#skF_9') | ~v7_waybel_0(B_50) | ~v4_orders_2(B_50) | v2_struct_0(B_50) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_30, c_239])).
% 6.34/2.19  tff(c_245, plain, (![B_50, D_62]: (r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_50), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_50)), D_62) | ~r3_waybel_9('#skF_9', B_50, D_62) | ~v10_waybel_0(B_50, '#skF_9') | ~m1_subset_1(D_62, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_50, '#skF_9') | ~v7_waybel_0(B_50) | ~v4_orders_2(B_50) | v2_struct_0(B_50))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_242])).
% 6.34/2.19  tff(c_18, plain, (![A_5, B_19, C_26]: (m1_subset_1('#skF_1'(A_5, B_19, C_26), u1_struct_0(A_5)) | r1_yellow_0(A_5, B_19) | ~r2_lattice3(A_5, B_19, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.34/2.19  tff(c_16, plain, (![A_5, B_19, C_26]: (r2_lattice3(A_5, B_19, '#skF_1'(A_5, B_19, C_26)) | r1_yellow_0(A_5, B_19) | ~r2_lattice3(A_5, B_19, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.34/2.19  tff(c_303, plain, (![A_248, B_249, D_250, E_251]: (m1_subset_1('#skF_4'(A_248, B_249, D_250, D_250), u1_struct_0(A_248)) | r3_orders_2(A_248, D_250, E_251) | ~r2_lattice3(A_248, k2_relset_1(u1_struct_0(B_249), u1_struct_0(A_248), u1_waybel_0(A_248, B_249)), E_251) | ~m1_subset_1(E_251, u1_struct_0(A_248)) | ~r3_waybel_9(A_248, B_249, D_250) | ~m1_subset_1(D_250, u1_struct_0(A_248)) | ~l1_waybel_0(B_249, A_248) | ~v7_waybel_0(B_249) | ~v4_orders_2(B_249) | v2_struct_0(B_249) | ~l1_waybel_9(A_248) | ~v1_compts_1(A_248) | ~v2_lattice3(A_248) | ~v1_lattice3(A_248) | ~v5_orders_2(A_248) | ~v4_orders_2(A_248) | ~v3_orders_2(A_248) | ~v8_pre_topc(A_248) | ~v2_pre_topc(A_248))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.34/2.19  tff(c_940, plain, (![A_412, B_413, D_414, C_415]: (m1_subset_1('#skF_4'(A_412, B_413, D_414, D_414), u1_struct_0(A_412)) | r3_orders_2(A_412, D_414, '#skF_1'(A_412, k2_relset_1(u1_struct_0(B_413), u1_struct_0(A_412), u1_waybel_0(A_412, B_413)), C_415)) | ~m1_subset_1('#skF_1'(A_412, k2_relset_1(u1_struct_0(B_413), u1_struct_0(A_412), u1_waybel_0(A_412, B_413)), C_415), u1_struct_0(A_412)) | ~r3_waybel_9(A_412, B_413, D_414) | ~m1_subset_1(D_414, u1_struct_0(A_412)) | ~l1_waybel_0(B_413, A_412) | ~v7_waybel_0(B_413) | ~v4_orders_2(B_413) | v2_struct_0(B_413) | ~l1_waybel_9(A_412) | ~v1_compts_1(A_412) | ~v2_lattice3(A_412) | ~v1_lattice3(A_412) | ~v4_orders_2(A_412) | ~v3_orders_2(A_412) | ~v8_pre_topc(A_412) | ~v2_pre_topc(A_412) | r1_yellow_0(A_412, k2_relset_1(u1_struct_0(B_413), u1_struct_0(A_412), u1_waybel_0(A_412, B_413))) | ~r2_lattice3(A_412, k2_relset_1(u1_struct_0(B_413), u1_struct_0(A_412), u1_waybel_0(A_412, B_413)), C_415) | ~m1_subset_1(C_415, u1_struct_0(A_412)) | ~l1_orders_2(A_412) | ~v5_orders_2(A_412))), inference(resolution, [status(thm)], [c_16, c_303])).
% 6.34/2.19  tff(c_1261, plain, (![A_489, B_490, D_491, C_492]: (m1_subset_1('#skF_4'(A_489, B_490, D_491, D_491), u1_struct_0(A_489)) | r3_orders_2(A_489, D_491, '#skF_1'(A_489, k2_relset_1(u1_struct_0(B_490), u1_struct_0(A_489), u1_waybel_0(A_489, B_490)), C_492)) | ~r3_waybel_9(A_489, B_490, D_491) | ~m1_subset_1(D_491, u1_struct_0(A_489)) | ~l1_waybel_0(B_490, A_489) | ~v7_waybel_0(B_490) | ~v4_orders_2(B_490) | v2_struct_0(B_490) | ~l1_waybel_9(A_489) | ~v1_compts_1(A_489) | ~v2_lattice3(A_489) | ~v1_lattice3(A_489) | ~v4_orders_2(A_489) | ~v3_orders_2(A_489) | ~v8_pre_topc(A_489) | ~v2_pre_topc(A_489) | r1_yellow_0(A_489, k2_relset_1(u1_struct_0(B_490), u1_struct_0(A_489), u1_waybel_0(A_489, B_490))) | ~r2_lattice3(A_489, k2_relset_1(u1_struct_0(B_490), u1_struct_0(A_489), u1_waybel_0(A_489, B_490)), C_492) | ~m1_subset_1(C_492, u1_struct_0(A_489)) | ~l1_orders_2(A_489) | ~v5_orders_2(A_489))), inference(resolution, [status(thm)], [c_18, c_940])).
% 6.34/2.19  tff(c_387, plain, (![A_276, B_277, D_278, E_279]: (~v5_pre_topc(k4_waybel_1(A_276, '#skF_4'(A_276, B_277, D_278, D_278)), A_276, A_276) | r3_orders_2(A_276, D_278, E_279) | ~r2_lattice3(A_276, k2_relset_1(u1_struct_0(B_277), u1_struct_0(A_276), u1_waybel_0(A_276, B_277)), E_279) | ~m1_subset_1(E_279, u1_struct_0(A_276)) | ~r3_waybel_9(A_276, B_277, D_278) | ~m1_subset_1(D_278, u1_struct_0(A_276)) | ~l1_waybel_0(B_277, A_276) | ~v7_waybel_0(B_277) | ~v4_orders_2(B_277) | v2_struct_0(B_277) | ~l1_waybel_9(A_276) | ~v1_compts_1(A_276) | ~v2_lattice3(A_276) | ~v1_lattice3(A_276) | ~v5_orders_2(A_276) | ~v4_orders_2(A_276) | ~v3_orders_2(A_276) | ~v8_pre_topc(A_276) | ~v2_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_178])).
% 6.34/2.19  tff(c_390, plain, (![D_278, E_279, B_277]: (r3_orders_2('#skF_9', D_278, E_279) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_277), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_277)), E_279) | ~m1_subset_1(E_279, u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', B_277, D_278) | ~m1_subset_1(D_278, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_277, '#skF_9') | ~v7_waybel_0(B_277) | ~v4_orders_2(B_277) | v2_struct_0(B_277) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_4'('#skF_9', B_277, D_278, D_278), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_66, c_387])).
% 6.34/2.19  tff(c_394, plain, (![D_280, E_281, B_282]: (r3_orders_2('#skF_9', D_280, E_281) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_282)), E_281) | ~m1_subset_1(E_281, u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', B_282, D_280) | ~m1_subset_1(D_280, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_282, '#skF_9') | ~v7_waybel_0(B_282) | ~v4_orders_2(B_282) | v2_struct_0(B_282) | ~m1_subset_1('#skF_4'('#skF_9', B_282, D_280, D_280), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_390])).
% 6.34/2.19  tff(c_402, plain, (![D_280, B_282, C_26]: (r3_orders_2('#skF_9', D_280, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_282)), C_26)) | ~m1_subset_1('#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_282)), C_26), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', B_282, D_280) | ~m1_subset_1(D_280, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_282, '#skF_9') | ~v7_waybel_0(B_282) | ~v4_orders_2(B_282) | v2_struct_0(B_282) | ~m1_subset_1('#skF_4'('#skF_9', B_282, D_280, D_280), u1_struct_0('#skF_9')) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_282))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_282)), C_26) | ~m1_subset_1(C_26, u1_struct_0('#skF_9')) | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9'))), inference(resolution, [status(thm)], [c_16, c_394])).
% 6.34/2.19  tff(c_742, plain, (![D_367, B_368, C_369]: (r3_orders_2('#skF_9', D_367, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368)), C_369)) | ~m1_subset_1('#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368)), C_369), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', B_368, D_367) | ~m1_subset_1(D_367, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_368, '#skF_9') | ~v7_waybel_0(B_368) | ~v4_orders_2(B_368) | v2_struct_0(B_368) | ~m1_subset_1('#skF_4'('#skF_9', B_368, D_367, D_367), u1_struct_0('#skF_9')) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368)), C_369) | ~m1_subset_1(C_369, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89, c_402])).
% 6.34/2.19  tff(c_745, plain, (![D_367, B_368, C_26]: (r3_orders_2('#skF_9', D_367, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368)), C_26)) | ~r3_waybel_9('#skF_9', B_368, D_367) | ~m1_subset_1(D_367, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_368, '#skF_9') | ~v7_waybel_0(B_368) | ~v4_orders_2(B_368) | v2_struct_0(B_368) | ~m1_subset_1('#skF_4'('#skF_9', B_368, D_367, D_367), u1_struct_0('#skF_9')) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368)), C_26) | ~m1_subset_1(C_26, u1_struct_0('#skF_9')) | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9'))), inference(resolution, [status(thm)], [c_18, c_742])).
% 6.34/2.19  tff(c_748, plain, (![D_367, B_368, C_26]: (r3_orders_2('#skF_9', D_367, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368)), C_26)) | ~r3_waybel_9('#skF_9', B_368, D_367) | ~m1_subset_1(D_367, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_368, '#skF_9') | ~v7_waybel_0(B_368) | ~v4_orders_2(B_368) | v2_struct_0(B_368) | ~m1_subset_1('#skF_4'('#skF_9', B_368, D_367, D_367), u1_struct_0('#skF_9')) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368)), C_26) | ~m1_subset_1(C_26, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89, c_745])).
% 6.34/2.19  tff(c_1264, plain, (![D_491, B_490, C_26, C_492]: (r3_orders_2('#skF_9', D_491, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490)), C_26)) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490)), C_26) | ~m1_subset_1(C_26, u1_struct_0('#skF_9')) | r3_orders_2('#skF_9', D_491, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490)), C_492)) | ~r3_waybel_9('#skF_9', B_490, D_491) | ~m1_subset_1(D_491, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_490, '#skF_9') | ~v7_waybel_0(B_490) | ~v4_orders_2(B_490) | v2_struct_0(B_490) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490)), C_492) | ~m1_subset_1(C_492, u1_struct_0('#skF_9')) | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9'))), inference(resolution, [status(thm)], [c_1261, c_748])).
% 6.34/2.19  tff(c_1274, plain, (![D_491, B_490, C_26, C_492]: (r3_orders_2('#skF_9', D_491, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490)), C_26)) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490)), C_26) | ~m1_subset_1(C_26, u1_struct_0('#skF_9')) | r3_orders_2('#skF_9', D_491, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490)), C_492)) | ~r3_waybel_9('#skF_9', B_490, D_491) | ~m1_subset_1(D_491, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_490, '#skF_9') | ~v7_waybel_0(B_490) | ~v4_orders_2(B_490) | v2_struct_0(B_490) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_490), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_490)), C_492) | ~m1_subset_1(C_492, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89, c_84, c_82, c_80, c_78, c_74, c_72, c_70, c_68, c_1264])).
% 6.34/2.19  tff(c_1336, plain, (![B_505, D_506, C_507]: (~r3_waybel_9('#skF_9', B_505, D_506) | ~m1_subset_1(D_506, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_505, '#skF_9') | ~v7_waybel_0(B_505) | ~v4_orders_2(B_505) | v2_struct_0(B_505) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505)), C_507) | ~m1_subset_1(C_507, u1_struct_0('#skF_9')) | r3_orders_2('#skF_9', D_506, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505)), C_507)))), inference(factorization, [status(thm), theory('equality')], [c_1274])).
% 6.34/2.19  tff(c_4, plain, (![A_1, B_2, C_3]: (r1_orders_2(A_1, B_2, C_3) | ~r3_orders_2(A_1, B_2, C_3) | ~m1_subset_1(C_3, u1_struct_0(A_1)) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.34/2.19  tff(c_1338, plain, (![D_506, B_505, C_507]: (r1_orders_2('#skF_9', D_506, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505)), C_507)) | ~m1_subset_1('#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505)), C_507), u1_struct_0('#skF_9')) | ~l1_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', B_505, D_506) | ~m1_subset_1(D_506, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_505, '#skF_9') | ~v7_waybel_0(B_505) | ~v4_orders_2(B_505) | v2_struct_0(B_505) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505)), C_507) | ~m1_subset_1(C_507, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_1336, c_4])).
% 6.34/2.19  tff(c_1341, plain, (![D_506, B_505, C_507]: (r1_orders_2('#skF_9', D_506, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505)), C_507)) | ~m1_subset_1('#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505)), C_507), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', B_505, D_506) | ~m1_subset_1(D_506, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_505, '#skF_9') | ~v7_waybel_0(B_505) | ~v4_orders_2(B_505) | v2_struct_0(B_505) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_505), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_505)), C_507) | ~m1_subset_1(C_507, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_89, c_1338])).
% 6.34/2.19  tff(c_1343, plain, (![D_508, B_509, C_510]: (r1_orders_2('#skF_9', D_508, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_509), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_509)), C_510)) | ~m1_subset_1('#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_509), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_509)), C_510), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', B_509, D_508) | ~m1_subset_1(D_508, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_509, '#skF_9') | ~v7_waybel_0(B_509) | ~v4_orders_2(B_509) | v2_struct_0(B_509) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_509), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_509))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_509), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_509)), C_510) | ~m1_subset_1(C_510, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_210, c_1341])).
% 6.34/2.19  tff(c_1346, plain, (![D_508, B_509, C_26]: (r1_orders_2('#skF_9', D_508, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_509), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_509)), C_26)) | ~r3_waybel_9('#skF_9', B_509, D_508) | ~m1_subset_1(D_508, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_509, '#skF_9') | ~v7_waybel_0(B_509) | ~v4_orders_2(B_509) | v2_struct_0(B_509) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_509), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_509))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_509), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_509)), C_26) | ~m1_subset_1(C_26, u1_struct_0('#skF_9')) | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9'))), inference(resolution, [status(thm)], [c_18, c_1343])).
% 6.34/2.19  tff(c_1350, plain, (![D_511, B_512, C_513]: (r1_orders_2('#skF_9', D_511, '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_512), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_512)), C_513)) | ~r3_waybel_9('#skF_9', B_512, D_511) | ~m1_subset_1(D_511, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_512, '#skF_9') | ~v7_waybel_0(B_512) | ~v4_orders_2(B_512) | v2_struct_0(B_512) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_512), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_512))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_512), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_512)), C_513) | ~m1_subset_1(C_513, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89, c_1346])).
% 6.34/2.19  tff(c_14, plain, (![A_5, C_26, B_19]: (~r1_orders_2(A_5, C_26, '#skF_1'(A_5, B_19, C_26)) | r1_yellow_0(A_5, B_19) | ~r2_lattice3(A_5, B_19, C_26) | ~m1_subset_1(C_26, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.34/2.19  tff(c_1354, plain, (![B_512, C_513]: (~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9') | ~r3_waybel_9('#skF_9', B_512, C_513) | ~l1_waybel_0(B_512, '#skF_9') | ~v7_waybel_0(B_512) | ~v4_orders_2(B_512) | v2_struct_0(B_512) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_512), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_512))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_512), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_512)), C_513) | ~m1_subset_1(C_513, u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_1350, c_14])).
% 6.34/2.19  tff(c_1358, plain, (![B_514, C_515]: (~r3_waybel_9('#skF_9', B_514, C_515) | ~l1_waybel_0(B_514, '#skF_9') | ~v7_waybel_0(B_514) | ~v4_orders_2(B_514) | v2_struct_0(B_514) | r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_514), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_514))) | ~r2_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_514), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_514)), C_515) | ~m1_subset_1(C_515, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89, c_1354])).
% 6.34/2.19  tff(c_1408, plain, (![B_521, D_522]: (r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_521), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_521))) | ~r3_waybel_9('#skF_9', B_521, D_522) | ~v10_waybel_0(B_521, '#skF_9') | ~m1_subset_1(D_522, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_521, '#skF_9') | ~v7_waybel_0(B_521) | ~v4_orders_2(B_521) | v2_struct_0(B_521))), inference(resolution, [status(thm)], [c_245, c_1358])).
% 6.34/2.19  tff(c_1417, plain, (![B_114]: (r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_114), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_114))) | ~v10_waybel_0(B_114, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_114), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_1408])).
% 6.34/2.19  tff(c_1428, plain, (![B_114]: (r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_114), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_114))) | ~v10_waybel_0(B_114, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_114), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1417])).
% 6.34/2.19  tff(c_1430, plain, (![B_523]: (r1_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_523), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_523))) | ~v10_waybel_0(B_523, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_523), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_523, '#skF_9') | ~v7_waybel_0(B_523) | ~v4_orders_2(B_523) | v2_struct_0(B_523))), inference(negUnitSimplification, [status(thm)], [c_210, c_1428])).
% 6.34/2.19  tff(c_20, plain, (![A_30, B_32]: (r1_waybel_9(A_30, B_32) | ~r1_yellow_0(A_30, k2_relset_1(u1_struct_0(B_32), u1_struct_0(A_30), u1_waybel_0(A_30, B_32))) | ~l1_waybel_0(B_32, A_30) | ~l1_orders_2(A_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.34/2.19  tff(c_1433, plain, (![B_523]: (r1_waybel_9('#skF_9', B_523) | ~l1_orders_2('#skF_9') | ~v10_waybel_0(B_523, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_523), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_523, '#skF_9') | ~v7_waybel_0(B_523) | ~v4_orders_2(B_523) | v2_struct_0(B_523))), inference(resolution, [status(thm)], [c_1430, c_20])).
% 6.34/2.19  tff(c_1437, plain, (![B_524]: (r1_waybel_9('#skF_9', B_524) | ~v10_waybel_0(B_524, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_524), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_524, '#skF_9') | ~v7_waybel_0(B_524) | ~v4_orders_2(B_524) | v2_struct_0(B_524))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1433])).
% 6.34/2.19  tff(c_1441, plain, (![B_114]: (r1_waybel_9('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_38, c_1437])).
% 6.34/2.19  tff(c_1444, plain, (![B_114]: (r1_waybel_9('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1441])).
% 6.34/2.19  tff(c_1468, plain, (![B_530]: (r1_waybel_9('#skF_9', B_530) | ~v10_waybel_0(B_530, '#skF_9') | ~l1_waybel_0(B_530, '#skF_9') | ~v7_waybel_0(B_530) | ~v4_orders_2(B_530) | v2_struct_0(B_530))), inference(negUnitSimplification, [status(thm)], [c_210, c_1444])).
% 6.34/2.19  tff(c_1471, plain, (r1_waybel_9('#skF_9', '#skF_10') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_56, c_1468])).
% 6.34/2.19  tff(c_1474, plain, (r1_waybel_9('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1471])).
% 6.34/2.19  tff(c_1476, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_97, c_1474])).
% 6.34/2.19  tff(c_1477, plain, (~r2_hidden(k1_waybel_2('#skF_9', '#skF_10'), k10_yellow_6('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_54])).
% 6.34/2.19  tff(c_1514, plain, (m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_2('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1509, c_1477])).
% 6.34/2.19  tff(c_1518, plain, (m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_2('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1514])).
% 6.34/2.19  tff(c_1519, plain, (m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_2('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_64, c_1518])).
% 6.34/2.19  tff(c_1520, plain, (~m1_subset_1(k1_waybel_2('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_1519])).
% 6.34/2.19  tff(c_1644, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1638, c_1520])).
% 6.34/2.19  tff(c_1652, plain, (~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_38, c_1644])).
% 6.34/2.19  tff(c_1655, plain, (v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1652])).
% 6.34/2.19  tff(c_1657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1621, c_64, c_1655])).
% 6.34/2.19  tff(c_1659, plain, (m1_subset_1(k1_waybel_2('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_1519])).
% 6.34/2.19  tff(c_2, plain, (![A_1, B_2, C_3]: (r3_orders_2(A_1, B_2, C_3) | ~r1_orders_2(A_1, B_2, C_3) | ~m1_subset_1(C_3, u1_struct_0(A_1)) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.34/2.19  tff(c_1661, plain, (![B_2]: (r3_orders_2('#skF_9', B_2, k1_waybel_2('#skF_9', '#skF_10')) | ~r1_orders_2('#skF_9', B_2, k1_waybel_2('#skF_9', '#skF_10')) | ~m1_subset_1(B_2, u1_struct_0('#skF_9')) | ~l1_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_1659, c_2])).
% 6.34/2.19  tff(c_1664, plain, (![B_2]: (r3_orders_2('#skF_9', B_2, k1_waybel_2('#skF_9', '#skF_10')) | ~r1_orders_2('#skF_9', B_2, k1_waybel_2('#skF_9', '#skF_10')) | ~m1_subset_1(B_2, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_89, c_1661])).
% 6.34/2.19  tff(c_1666, plain, (v2_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1664])).
% 6.34/2.19  tff(c_1669, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_1666, c_6])).
% 6.34/2.19  tff(c_1673, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_74, c_1669])).
% 6.34/2.19  tff(c_1675, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1664])).
% 6.34/2.19  tff(c_1739, plain, (![A_633, B_634, C_635]: (~v5_pre_topc(k4_waybel_1(A_633, '#skF_8'(A_633, B_634, C_635)), A_633, A_633) | k1_waybel_2(A_633, C_635)=B_634 | ~r3_waybel_9(A_633, C_635, B_634) | ~v10_waybel_0(C_635, A_633) | ~l1_waybel_0(C_635, A_633) | ~v7_waybel_0(C_635) | ~v4_orders_2(C_635) | v2_struct_0(C_635) | ~m1_subset_1(B_634, u1_struct_0(A_633)) | ~l1_waybel_9(A_633) | ~v1_compts_1(A_633) | ~v2_lattice3(A_633) | ~v1_lattice3(A_633) | ~v5_orders_2(A_633) | ~v4_orders_2(A_633) | ~v3_orders_2(A_633) | ~v8_pre_topc(A_633) | ~v2_pre_topc(A_633))), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.34/2.19  tff(c_1743, plain, (![C_635, B_634]: (k1_waybel_2('#skF_9', C_635)=B_634 | ~r3_waybel_9('#skF_9', C_635, B_634) | ~v10_waybel_0(C_635, '#skF_9') | ~l1_waybel_0(C_635, '#skF_9') | ~v7_waybel_0(C_635) | ~v4_orders_2(C_635) | v2_struct_0(C_635) | ~m1_subset_1(B_634, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_8'('#skF_9', B_634, C_635), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_66, c_1739])).
% 6.34/2.19  tff(c_1752, plain, (![C_639, B_640]: (k1_waybel_2('#skF_9', C_639)=B_640 | ~r3_waybel_9('#skF_9', C_639, B_640) | ~v10_waybel_0(C_639, '#skF_9') | ~l1_waybel_0(C_639, '#skF_9') | ~v7_waybel_0(C_639) | ~v4_orders_2(C_639) | v2_struct_0(C_639) | ~m1_subset_1(B_640, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_8'('#skF_9', B_640, C_639), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1743])).
% 6.34/2.19  tff(c_1756, plain, (![C_145, B_141]: (k1_waybel_2('#skF_9', C_145)=B_141 | ~r3_waybel_9('#skF_9', C_145, B_141) | ~v10_waybel_0(C_145, '#skF_9') | ~l1_waybel_0(C_145, '#skF_9') | ~v7_waybel_0(C_145) | ~v4_orders_2(C_145) | v2_struct_0(C_145) | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_1752])).
% 6.34/2.19  tff(c_1760, plain, (![C_641, B_642]: (k1_waybel_2('#skF_9', C_641)=B_642 | ~r3_waybel_9('#skF_9', C_641, B_642) | ~v10_waybel_0(C_641, '#skF_9') | ~l1_waybel_0(C_641, '#skF_9') | ~v7_waybel_0(C_641) | ~v4_orders_2(C_641) | v2_struct_0(C_641) | ~m1_subset_1(B_642, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1756])).
% 6.34/2.19  tff(c_1769, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_114), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_36, c_1760])).
% 6.34/2.19  tff(c_1780, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_114), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1769])).
% 6.34/2.19  tff(c_1782, plain, (![B_643]: (k1_waybel_2('#skF_9', B_643)='#skF_5'('#skF_9', B_643) | ~v10_waybel_0(B_643, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_643), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_643, '#skF_9') | ~v7_waybel_0(B_643) | ~v4_orders_2(B_643) | v2_struct_0(B_643))), inference(negUnitSimplification, [status(thm)], [c_1675, c_1780])).
% 6.34/2.19  tff(c_1786, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_38, c_1782])).
% 6.34/2.19  tff(c_1789, plain, (![B_114]: (k1_waybel_2('#skF_9', B_114)='#skF_5'('#skF_9', B_114) | ~v10_waybel_0(B_114, '#skF_9') | ~l1_waybel_0(B_114, '#skF_9') | ~v7_waybel_0(B_114) | ~v4_orders_2(B_114) | v2_struct_0(B_114) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1786])).
% 6.34/2.19  tff(c_1791, plain, (![B_644]: (k1_waybel_2('#skF_9', B_644)='#skF_5'('#skF_9', B_644) | ~v10_waybel_0(B_644, '#skF_9') | ~l1_waybel_0(B_644, '#skF_9') | ~v7_waybel_0(B_644) | ~v4_orders_2(B_644) | v2_struct_0(B_644))), inference(negUnitSimplification, [status(thm)], [c_1675, c_1789])).
% 6.34/2.19  tff(c_1794, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_56, c_1791])).
% 6.34/2.19  tff(c_1797, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1794])).
% 6.34/2.19  tff(c_1798, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_64, c_1797])).
% 6.34/2.19  tff(c_1658, plain, (~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10')) | v2_struct_0('#skF_9') | m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_1519])).
% 6.34/2.19  tff(c_1665, plain, (~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_1658])).
% 6.34/2.19  tff(c_1800, plain, (~r3_waybel_9('#skF_9', '#skF_10', '#skF_5'('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1798, c_1665])).
% 6.34/2.19  tff(c_1815, plain, (~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_36, c_1800])).
% 6.34/2.19  tff(c_1818, plain, (v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1815])).
% 6.34/2.19  tff(c_1820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1675, c_64, c_1818])).
% 6.34/2.19  tff(c_1821, plain, (m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1658])).
% 6.34/2.19  tff(c_1823, plain, (v2_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1821])).
% 6.34/2.19  tff(c_1834, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_1823, c_6])).
% 6.34/2.19  tff(c_1838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_74, c_1834])).
% 6.34/2.19  tff(c_1840, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1821])).
% 6.34/2.19  tff(c_1822, plain, (r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_1658])).
% 6.34/2.19  tff(c_1886, plain, (![A_663, B_664, C_665]: ('#skF_6'(A_663, B_664)!='#skF_7'(A_663, B_664) | r2_hidden(C_665, k10_yellow_6(A_663, B_664)) | ~r3_waybel_9(A_663, B_664, C_665) | ~m1_subset_1(C_665, u1_struct_0(A_663)) | ~l1_waybel_0(B_664, A_663) | ~v7_waybel_0(B_664) | ~v4_orders_2(B_664) | v2_struct_0(B_664) | ~l1_pre_topc(A_663) | ~v1_compts_1(A_663) | ~v8_pre_topc(A_663) | ~v2_pre_topc(A_663) | v2_struct_0(A_663))), inference(cnfTransformation, [status(thm)], [f_244])).
% 6.34/2.19  tff(c_1889, plain, ('#skF_6'('#skF_9', '#skF_10')!='#skF_7'('#skF_9', '#skF_10') | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_2('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1886, c_1477])).
% 6.34/2.19  tff(c_1892, plain, ('#skF_6'('#skF_9', '#skF_10')!='#skF_7'('#skF_9', '#skF_10') | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1659, c_1822, c_1889])).
% 6.34/2.19  tff(c_1893, plain, ('#skF_6'('#skF_9', '#skF_10')!='#skF_7'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_1840, c_64, c_1892])).
% 6.34/2.19  tff(c_1894, plain, (![A_666, B_667, C_668]: (m1_subset_1('#skF_7'(A_666, B_667), u1_struct_0(A_666)) | r2_hidden(C_668, k10_yellow_6(A_666, B_667)) | ~r3_waybel_9(A_666, B_667, C_668) | ~m1_subset_1(C_668, u1_struct_0(A_666)) | ~l1_waybel_0(B_667, A_666) | ~v7_waybel_0(B_667) | ~v4_orders_2(B_667) | v2_struct_0(B_667) | ~l1_pre_topc(A_666) | ~v1_compts_1(A_666) | ~v8_pre_topc(A_666) | ~v2_pre_topc(A_666) | v2_struct_0(A_666))), inference(cnfTransformation, [status(thm)], [f_244])).
% 6.34/2.19  tff(c_1899, plain, (m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_2('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1894, c_1477])).
% 6.34/2.19  tff(c_1903, plain, (m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1659, c_1822, c_1899])).
% 6.34/2.19  tff(c_1904, plain, (m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1840, c_64, c_1903])).
% 6.34/2.19  tff(c_1870, plain, (![A_657, B_658, C_659]: (r3_waybel_9(A_657, B_658, '#skF_7'(A_657, B_658)) | r2_hidden(C_659, k10_yellow_6(A_657, B_658)) | ~r3_waybel_9(A_657, B_658, C_659) | ~m1_subset_1(C_659, u1_struct_0(A_657)) | ~l1_waybel_0(B_658, A_657) | ~v7_waybel_0(B_658) | ~v4_orders_2(B_658) | v2_struct_0(B_658) | ~l1_pre_topc(A_657) | ~v1_compts_1(A_657) | ~v8_pre_topc(A_657) | ~v2_pre_topc(A_657) | v2_struct_0(A_657))), inference(cnfTransformation, [status(thm)], [f_244])).
% 6.34/2.19  tff(c_1873, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', '#skF_10')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_2('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1870, c_1477])).
% 6.34/2.19  tff(c_1876, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', '#skF_10')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1659, c_1822, c_1873])).
% 6.34/2.19  tff(c_1877, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_1840, c_64, c_1876])).
% 6.34/2.19  tff(c_1931, plain, (![A_679, B_680, C_681]: (~v5_pre_topc(k4_waybel_1(A_679, '#skF_8'(A_679, B_680, C_681)), A_679, A_679) | k1_waybel_2(A_679, C_681)=B_680 | ~r3_waybel_9(A_679, C_681, B_680) | ~v10_waybel_0(C_681, A_679) | ~l1_waybel_0(C_681, A_679) | ~v7_waybel_0(C_681) | ~v4_orders_2(C_681) | v2_struct_0(C_681) | ~m1_subset_1(B_680, u1_struct_0(A_679)) | ~l1_waybel_9(A_679) | ~v1_compts_1(A_679) | ~v2_lattice3(A_679) | ~v1_lattice3(A_679) | ~v5_orders_2(A_679) | ~v4_orders_2(A_679) | ~v3_orders_2(A_679) | ~v8_pre_topc(A_679) | ~v2_pre_topc(A_679))), inference(cnfTransformation, [status(thm)], [f_286])).
% 6.34/2.19  tff(c_1935, plain, (![C_681, B_680]: (k1_waybel_2('#skF_9', C_681)=B_680 | ~r3_waybel_9('#skF_9', C_681, B_680) | ~v10_waybel_0(C_681, '#skF_9') | ~l1_waybel_0(C_681, '#skF_9') | ~v7_waybel_0(C_681) | ~v4_orders_2(C_681) | v2_struct_0(C_681) | ~m1_subset_1(B_680, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_8'('#skF_9', B_680, C_681), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_66, c_1931])).
% 6.34/2.19  tff(c_1939, plain, (![C_682, B_683]: (k1_waybel_2('#skF_9', C_682)=B_683 | ~r3_waybel_9('#skF_9', C_682, B_683) | ~v10_waybel_0(C_682, '#skF_9') | ~l1_waybel_0(C_682, '#skF_9') | ~v7_waybel_0(C_682) | ~v4_orders_2(C_682) | v2_struct_0(C_682) | ~m1_subset_1(B_683, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_8'('#skF_9', B_683, C_682), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1935])).
% 6.34/2.19  tff(c_1943, plain, (![C_145, B_141]: (k1_waybel_2('#skF_9', C_145)=B_141 | ~r3_waybel_9('#skF_9', C_145, B_141) | ~v10_waybel_0(C_145, '#skF_9') | ~l1_waybel_0(C_145, '#skF_9') | ~v7_waybel_0(C_145) | ~v4_orders_2(C_145) | v2_struct_0(C_145) | ~m1_subset_1(B_141, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_52, c_1939])).
% 6.34/2.19  tff(c_1947, plain, (![C_684, B_685]: (k1_waybel_2('#skF_9', C_684)=B_685 | ~r3_waybel_9('#skF_9', C_684, B_685) | ~v10_waybel_0(C_684, '#skF_9') | ~l1_waybel_0(C_684, '#skF_9') | ~v7_waybel_0(C_684) | ~v4_orders_2(C_684) | v2_struct_0(C_684) | ~m1_subset_1(B_685, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1943])).
% 6.34/2.19  tff(c_1954, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_7'('#skF_9', '#skF_10') | ~v10_waybel_0('#skF_10', '#skF_9') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_1877, c_1947])).
% 6.34/2.19  tff(c_1973, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_7'('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1904, c_62, c_60, c_58, c_56, c_1954])).
% 6.34/2.19  tff(c_1974, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_7'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_64, c_1973])).
% 6.34/2.19  tff(c_1839, plain, (m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_1821])).
% 6.34/2.19  tff(c_1878, plain, (![A_660, B_661, C_662]: (r3_waybel_9(A_660, B_661, '#skF_6'(A_660, B_661)) | r2_hidden(C_662, k10_yellow_6(A_660, B_661)) | ~r3_waybel_9(A_660, B_661, C_662) | ~m1_subset_1(C_662, u1_struct_0(A_660)) | ~l1_waybel_0(B_661, A_660) | ~v7_waybel_0(B_661) | ~v4_orders_2(B_661) | v2_struct_0(B_661) | ~l1_pre_topc(A_660) | ~v1_compts_1(A_660) | ~v8_pre_topc(A_660) | ~v2_pre_topc(A_660) | v2_struct_0(A_660))), inference(cnfTransformation, [status(thm)], [f_244])).
% 6.34/2.19  tff(c_1881, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_6'('#skF_9', '#skF_10')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_2('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_2('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1878, c_1477])).
% 6.34/2.19  tff(c_1884, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_6'('#skF_9', '#skF_10')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1659, c_1822, c_1881])).
% 6.34/2.19  tff(c_1885, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_6'('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_1840, c_64, c_1884])).
% 6.34/2.19  tff(c_1949, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_6'('#skF_9', '#skF_10') | ~v10_waybel_0('#skF_10', '#skF_9') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_1885, c_1947])).
% 6.34/2.19  tff(c_1965, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_6'('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1839, c_62, c_60, c_58, c_56, c_1949])).
% 6.34/2.19  tff(c_1966, plain, (k1_waybel_2('#skF_9', '#skF_10')='#skF_6'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_64, c_1965])).
% 6.34/2.19  tff(c_1998, plain, ('#skF_6'('#skF_9', '#skF_10')='#skF_7'('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1974, c_1966])).
% 6.34/2.19  tff(c_2000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1893, c_1998])).
% 6.34/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.34/2.19  
% 6.34/2.19  Inference rules
% 6.34/2.19  ----------------------
% 6.34/2.19  #Ref     : 0
% 6.34/2.19  #Sup     : 265
% 6.34/2.19  #Fact    : 34
% 6.34/2.19  #Define  : 0
% 6.34/2.19  #Split   : 8
% 6.34/2.19  #Chain   : 0
% 6.34/2.19  #Close   : 0
% 6.34/2.19  
% 6.34/2.19  Ordering : KBO
% 6.34/2.19  
% 6.34/2.19  Simplification rules
% 6.34/2.19  ----------------------
% 6.34/2.19  #Subsume      : 141
% 6.34/2.19  #Demod        : 812
% 6.34/2.19  #Tautology    : 45
% 6.34/2.19  #SimpNegUnit  : 136
% 6.34/2.19  #BackRed      : 11
% 6.34/2.19  
% 6.34/2.19  #Partial instantiations: 0
% 6.34/2.19  #Strategies tried      : 1
% 6.34/2.19  
% 6.34/2.19  Timing (in seconds)
% 6.34/2.19  ----------------------
% 6.34/2.19  Preprocessing        : 0.41
% 6.34/2.19  Parsing              : 0.21
% 6.34/2.19  CNF conversion       : 0.04
% 6.34/2.19  Main loop            : 0.97
% 6.34/2.19  Inferencing          : 0.43
% 6.34/2.19  Reduction            : 0.26
% 6.34/2.19  Demodulation         : 0.18
% 6.34/2.19  BG Simplification    : 0.04
% 6.34/2.19  Subsumption          : 0.19
% 6.34/2.19  Abstraction          : 0.04
% 6.34/2.19  MUC search           : 0.00
% 6.34/2.19  Cooper               : 0.00
% 6.34/2.19  Total                : 1.45
% 6.34/2.19  Index Insertion      : 0.00
% 6.34/2.19  Index Deletion       : 0.00
% 6.34/2.19  Index Matching       : 0.00
% 6.34/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
