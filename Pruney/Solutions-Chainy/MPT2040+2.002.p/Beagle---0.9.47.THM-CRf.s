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
% DateTime   : Thu Dec  3 10:31:22 EST 2020

% Result     : Theorem 5.07s
% Output     : CNFRefutation 5.07s
% Verified   : 
% Statistics : Number of formulae       :  217 (1815 expanded)
%              Number of leaves         :   52 ( 770 expanded)
%              Depth                    :   22
%              Number of atoms          : 1282 (15983 expanded)
%              Number of equality atoms :   58 ( 189 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > r3_waybel_9 > r1_orders_2 > r1_lattice3 > v11_waybel_0 > r2_yellow_0 > r2_waybel_9 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_compts_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_waybel_1 > k2_yellow_0 > k1_waybel_9 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

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

tff(r2_waybel_9,type,(
    r2_waybel_9: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(v11_waybel_0,type,(
    v11_waybel_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff(k1_waybel_9,type,(
    k1_waybel_9: ( $i * $i ) > $i )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

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
             => ( v11_waybel_0(B,A)
               => ( r2_waybel_9(A,B)
                  & r2_hidden(k1_waybel_9(A,B),k10_yellow_6(A,B)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_waybel_9)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_waybel_9)).

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
                  & v11_waybel_0(C,A)
                  & r3_waybel_9(A,C,B) )
               => B = k1_waybel_9(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_9)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_9)).

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
                      & v11_waybel_0(B,A)
                      & r3_waybel_9(A,B,C) )
                   => r1_lattice3(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B)),D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_waybel_9)).

tff(f_66,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

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
                       => ( r1_lattice3(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B)),E)
                         => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l52_waybel_9)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ( r2_waybel_9(A,B)
          <=> r2_yellow_0(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_waybel_9)).

tff(c_68,plain,(
    l1_waybel_9('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_85,plain,(
    ! [A_144] :
      ( l1_orders_2(A_144)
      | ~ l1_waybel_9(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_89,plain,(
    l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_85])).

tff(c_74,plain,(
    v1_lattice3('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_84,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_82,plain,(
    v8_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_70,plain,(
    v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_90,plain,(
    ! [A_145] :
      ( l1_pre_topc(A_145)
      | ~ l1_waybel_9(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_94,plain,(
    l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_90])).

tff(c_36,plain,(
    ! [A_104,B_108] :
      ( r3_waybel_9(A_104,B_108,'#skF_4'(A_104,B_108))
      | ~ l1_waybel_0(B_108,A_104)
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc(A_104)
      | ~ v1_compts_1(A_104)
      | ~ v8_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_80,plain,(
    v3_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_78,plain,(
    v4_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_76,plain,(
    v5_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_72,plain,(
    v2_lattice3('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_52,plain,(
    ! [A_127,B_135,C_139] :
      ( m1_subset_1('#skF_7'(A_127,B_135,C_139),u1_struct_0(A_127))
      | k1_waybel_9(A_127,C_139) = B_135
      | ~ r3_waybel_9(A_127,C_139,B_135)
      | ~ v11_waybel_0(C_139,A_127)
      | ~ l1_waybel_0(C_139,A_127)
      | ~ v7_waybel_0(C_139)
      | ~ v4_orders_2(C_139)
      | v2_struct_0(C_139)
      | ~ m1_subset_1(B_135,u1_struct_0(A_127))
      | ~ l1_waybel_9(A_127)
      | ~ v1_compts_1(A_127)
      | ~ v2_lattice3(A_127)
      | ~ v1_lattice3(A_127)
      | ~ v5_orders_2(A_127)
      | ~ v4_orders_2(A_127)
      | ~ v3_orders_2(A_127)
      | ~ v8_pre_topc(A_127)
      | ~ v2_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_66,plain,(
    ! [B_143] :
      ( v5_pre_topc(k4_waybel_1('#skF_8',B_143),'#skF_8','#skF_8')
      | ~ m1_subset_1(B_143,u1_struct_0('#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_1136,plain,(
    ! [A_461,B_462,C_463] :
      ( ~ v5_pre_topc(k4_waybel_1(A_461,'#skF_7'(A_461,B_462,C_463)),A_461,A_461)
      | k1_waybel_9(A_461,C_463) = B_462
      | ~ r3_waybel_9(A_461,C_463,B_462)
      | ~ v11_waybel_0(C_463,A_461)
      | ~ l1_waybel_0(C_463,A_461)
      | ~ v7_waybel_0(C_463)
      | ~ v4_orders_2(C_463)
      | v2_struct_0(C_463)
      | ~ m1_subset_1(B_462,u1_struct_0(A_461))
      | ~ l1_waybel_9(A_461)
      | ~ v1_compts_1(A_461)
      | ~ v2_lattice3(A_461)
      | ~ v1_lattice3(A_461)
      | ~ v5_orders_2(A_461)
      | ~ v4_orders_2(A_461)
      | ~ v3_orders_2(A_461)
      | ~ v8_pre_topc(A_461)
      | ~ v2_pre_topc(A_461) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1140,plain,(
    ! [C_463,B_462] :
      ( k1_waybel_9('#skF_8',C_463) = B_462
      | ~ r3_waybel_9('#skF_8',C_463,B_462)
      | ~ v11_waybel_0(C_463,'#skF_8')
      | ~ l1_waybel_0(C_463,'#skF_8')
      | ~ v7_waybel_0(C_463)
      | ~ v4_orders_2(C_463)
      | v2_struct_0(C_463)
      | ~ m1_subset_1(B_462,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_7'('#skF_8',B_462,C_463),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_66,c_1136])).

tff(c_1144,plain,(
    ! [C_464,B_465] :
      ( k1_waybel_9('#skF_8',C_464) = B_465
      | ~ r3_waybel_9('#skF_8',C_464,B_465)
      | ~ v11_waybel_0(C_464,'#skF_8')
      | ~ l1_waybel_0(C_464,'#skF_8')
      | ~ v7_waybel_0(C_464)
      | ~ v4_orders_2(C_464)
      | v2_struct_0(C_464)
      | ~ m1_subset_1(B_465,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_7'('#skF_8',B_465,C_464),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1140])).

tff(c_1148,plain,(
    ! [C_139,B_135] :
      ( k1_waybel_9('#skF_8',C_139) = B_135
      | ~ r3_waybel_9('#skF_8',C_139,B_135)
      | ~ v11_waybel_0(C_139,'#skF_8')
      | ~ l1_waybel_0(C_139,'#skF_8')
      | ~ v7_waybel_0(C_139)
      | ~ v4_orders_2(C_139)
      | v2_struct_0(C_139)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_1144])).

tff(c_1153,plain,(
    ! [C_469,B_470] :
      ( k1_waybel_9('#skF_8',C_469) = B_470
      | ~ r3_waybel_9('#skF_8',C_469,B_470)
      | ~ v11_waybel_0(C_469,'#skF_8')
      | ~ l1_waybel_0(C_469,'#skF_8')
      | ~ v7_waybel_0(C_469)
      | ~ v4_orders_2(C_469)
      | v2_struct_0(C_469)
      | ~ m1_subset_1(B_470,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1148])).

tff(c_1162,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_108),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_1153])).

tff(c_1171,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_108),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1162])).

tff(c_1172,plain,(
    v2_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1171])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1175,plain,
    ( ~ v1_lattice3('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_1172,c_2])).

tff(c_1179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_74,c_1175])).

tff(c_1181,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1171])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_62,plain,(
    v4_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_60,plain,(
    v7_waybel_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_58,plain,(
    l1_waybel_0('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_56,plain,(
    v11_waybel_0('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_38,plain,(
    ! [A_104,B_108] :
      ( m1_subset_1('#skF_4'(A_104,B_108),u1_struct_0(A_104))
      | ~ l1_waybel_0(B_108,A_104)
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc(A_104)
      | ~ v1_compts_1(A_104)
      | ~ v8_pre_topc(A_104)
      | ~ v2_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_1186,plain,(
    ! [B_471] :
      ( k1_waybel_9('#skF_8',B_471) = '#skF_4'('#skF_8',B_471)
      | ~ v11_waybel_0(B_471,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_471),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_471,'#skF_8')
      | ~ v7_waybel_0(B_471)
      | ~ v4_orders_2(B_471)
      | v2_struct_0(B_471) ) ),
    inference(splitRight,[status(thm)],[c_1171])).

tff(c_1190,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_1186])).

tff(c_1193,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1190])).

tff(c_1202,plain,(
    ! [B_475] :
      ( k1_waybel_9('#skF_8',B_475) = '#skF_4'('#skF_8',B_475)
      | ~ v11_waybel_0(B_475,'#skF_8')
      | ~ l1_waybel_0(B_475,'#skF_8')
      | ~ v7_waybel_0(B_475)
      | ~ v4_orders_2(B_475)
      | v2_struct_0(B_475) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1181,c_1193])).

tff(c_1205,plain,
    ( k1_waybel_9('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_1202])).

tff(c_1208,plain,
    ( k1_waybel_9('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1205])).

tff(c_1209,plain,(
    k1_waybel_9('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1208])).

tff(c_1014,plain,(
    ! [A_432,B_433,C_434] :
      ( ~ v5_pre_topc(k4_waybel_1(A_432,'#skF_7'(A_432,B_433,C_434)),A_432,A_432)
      | k1_waybel_9(A_432,C_434) = B_433
      | ~ r3_waybel_9(A_432,C_434,B_433)
      | ~ v11_waybel_0(C_434,A_432)
      | ~ l1_waybel_0(C_434,A_432)
      | ~ v7_waybel_0(C_434)
      | ~ v4_orders_2(C_434)
      | v2_struct_0(C_434)
      | ~ m1_subset_1(B_433,u1_struct_0(A_432))
      | ~ l1_waybel_9(A_432)
      | ~ v1_compts_1(A_432)
      | ~ v2_lattice3(A_432)
      | ~ v1_lattice3(A_432)
      | ~ v5_orders_2(A_432)
      | ~ v4_orders_2(A_432)
      | ~ v3_orders_2(A_432)
      | ~ v8_pre_topc(A_432)
      | ~ v2_pre_topc(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1018,plain,(
    ! [C_434,B_433] :
      ( k1_waybel_9('#skF_8',C_434) = B_433
      | ~ r3_waybel_9('#skF_8',C_434,B_433)
      | ~ v11_waybel_0(C_434,'#skF_8')
      | ~ l1_waybel_0(C_434,'#skF_8')
      | ~ v7_waybel_0(C_434)
      | ~ v4_orders_2(C_434)
      | v2_struct_0(C_434)
      | ~ m1_subset_1(B_433,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_7'('#skF_8',B_433,C_434),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_66,c_1014])).

tff(c_1022,plain,(
    ! [C_435,B_436] :
      ( k1_waybel_9('#skF_8',C_435) = B_436
      | ~ r3_waybel_9('#skF_8',C_435,B_436)
      | ~ v11_waybel_0(C_435,'#skF_8')
      | ~ l1_waybel_0(C_435,'#skF_8')
      | ~ v7_waybel_0(C_435)
      | ~ v4_orders_2(C_435)
      | v2_struct_0(C_435)
      | ~ m1_subset_1(B_436,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_7'('#skF_8',B_436,C_435),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1018])).

tff(c_1026,plain,(
    ! [C_139,B_135] :
      ( k1_waybel_9('#skF_8',C_139) = B_135
      | ~ r3_waybel_9('#skF_8',C_139,B_135)
      | ~ v11_waybel_0(C_139,'#skF_8')
      | ~ l1_waybel_0(C_139,'#skF_8')
      | ~ v7_waybel_0(C_139)
      | ~ v4_orders_2(C_139)
      | v2_struct_0(C_139)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_1022])).

tff(c_1030,plain,(
    ! [C_437,B_438] :
      ( k1_waybel_9('#skF_8',C_437) = B_438
      | ~ r3_waybel_9('#skF_8',C_437,B_438)
      | ~ v11_waybel_0(C_437,'#skF_8')
      | ~ l1_waybel_0(C_437,'#skF_8')
      | ~ v7_waybel_0(C_437)
      | ~ v4_orders_2(C_437)
      | v2_struct_0(C_437)
      | ~ m1_subset_1(B_438,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1026])).

tff(c_1039,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_108),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_1030])).

tff(c_1048,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_108),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1039])).

tff(c_1050,plain,(
    v2_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1048])).

tff(c_1053,plain,
    ( ~ v1_lattice3('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_1050,c_2])).

tff(c_1057,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_74,c_1053])).

tff(c_1059,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1048])).

tff(c_1069,plain,(
    ! [B_444] :
      ( k1_waybel_9('#skF_8',B_444) = '#skF_4'('#skF_8',B_444)
      | ~ v11_waybel_0(B_444,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_444),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_444,'#skF_8')
      | ~ v7_waybel_0(B_444)
      | ~ v4_orders_2(B_444)
      | v2_struct_0(B_444) ) ),
    inference(splitRight,[status(thm)],[c_1048])).

tff(c_1073,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_1069])).

tff(c_1076,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_1073])).

tff(c_1078,plain,(
    ! [B_445] :
      ( k1_waybel_9('#skF_8',B_445) = '#skF_4'('#skF_8',B_445)
      | ~ v11_waybel_0(B_445,'#skF_8')
      | ~ l1_waybel_0(B_445,'#skF_8')
      | ~ v7_waybel_0(B_445)
      | ~ v4_orders_2(B_445)
      | v2_struct_0(B_445) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1059,c_1076])).

tff(c_1081,plain,
    ( k1_waybel_9('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_1078])).

tff(c_1084,plain,
    ( k1_waybel_9('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_1081])).

tff(c_1085,plain,(
    k1_waybel_9('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1084])).

tff(c_972,plain,(
    ! [A_414,B_415,C_416] :
      ( m1_subset_1('#skF_5'(A_414,B_415),u1_struct_0(A_414))
      | r2_hidden(C_416,k10_yellow_6(A_414,B_415))
      | ~ r3_waybel_9(A_414,B_415,C_416)
      | ~ m1_subset_1(C_416,u1_struct_0(A_414))
      | ~ l1_waybel_0(B_415,A_414)
      | ~ v7_waybel_0(B_415)
      | ~ v4_orders_2(B_415)
      | v2_struct_0(B_415)
      | ~ l1_pre_topc(A_414)
      | ~ v1_compts_1(A_414)
      | ~ v8_pre_topc(A_414)
      | ~ v2_pre_topc(A_414)
      | v2_struct_0(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_54,plain,
    ( ~ r2_hidden(k1_waybel_9('#skF_8','#skF_9'),k10_yellow_6('#skF_8','#skF_9'))
    | ~ r2_waybel_9('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_326])).

tff(c_97,plain,(
    ~ r2_waybel_9('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_120,plain,(
    ! [A_197,B_198,C_199] :
      ( ~ v5_pre_topc(k4_waybel_1(A_197,'#skF_7'(A_197,B_198,C_199)),A_197,A_197)
      | k1_waybel_9(A_197,C_199) = B_198
      | ~ r3_waybel_9(A_197,C_199,B_198)
      | ~ v11_waybel_0(C_199,A_197)
      | ~ l1_waybel_0(C_199,A_197)
      | ~ v7_waybel_0(C_199)
      | ~ v4_orders_2(C_199)
      | v2_struct_0(C_199)
      | ~ m1_subset_1(B_198,u1_struct_0(A_197))
      | ~ l1_waybel_9(A_197)
      | ~ v1_compts_1(A_197)
      | ~ v2_lattice3(A_197)
      | ~ v1_lattice3(A_197)
      | ~ v5_orders_2(A_197)
      | ~ v4_orders_2(A_197)
      | ~ v3_orders_2(A_197)
      | ~ v8_pre_topc(A_197)
      | ~ v2_pre_topc(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_124,plain,(
    ! [C_199,B_198] :
      ( k1_waybel_9('#skF_8',C_199) = B_198
      | ~ r3_waybel_9('#skF_8',C_199,B_198)
      | ~ v11_waybel_0(C_199,'#skF_8')
      | ~ l1_waybel_0(C_199,'#skF_8')
      | ~ v7_waybel_0(C_199)
      | ~ v4_orders_2(C_199)
      | v2_struct_0(C_199)
      | ~ m1_subset_1(B_198,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_7'('#skF_8',B_198,C_199),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_66,c_120])).

tff(c_128,plain,(
    ! [C_200,B_201] :
      ( k1_waybel_9('#skF_8',C_200) = B_201
      | ~ r3_waybel_9('#skF_8',C_200,B_201)
      | ~ v11_waybel_0(C_200,'#skF_8')
      | ~ l1_waybel_0(C_200,'#skF_8')
      | ~ v7_waybel_0(C_200)
      | ~ v4_orders_2(C_200)
      | v2_struct_0(C_200)
      | ~ m1_subset_1(B_201,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_7'('#skF_8',B_201,C_200),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_124])).

tff(c_132,plain,(
    ! [C_139,B_135] :
      ( k1_waybel_9('#skF_8',C_139) = B_135
      | ~ r3_waybel_9('#skF_8',C_139,B_135)
      | ~ v11_waybel_0(C_139,'#skF_8')
      | ~ l1_waybel_0(C_139,'#skF_8')
      | ~ v7_waybel_0(C_139)
      | ~ v4_orders_2(C_139)
      | v2_struct_0(C_139)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_128])).

tff(c_136,plain,(
    ! [C_202,B_203] :
      ( k1_waybel_9('#skF_8',C_202) = B_203
      | ~ r3_waybel_9('#skF_8',C_202,B_203)
      | ~ v11_waybel_0(C_202,'#skF_8')
      | ~ l1_waybel_0(C_202,'#skF_8')
      | ~ v7_waybel_0(C_202)
      | ~ v4_orders_2(C_202)
      | v2_struct_0(C_202)
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_132])).

tff(c_145,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_108),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_136])).

tff(c_154,plain,(
    ! [B_108] :
      ( k1_waybel_9('#skF_8',B_108) = '#skF_4'('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_108),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_145])).

tff(c_155,plain,(
    v2_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_158,plain,
    ( ~ v1_lattice3('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_74,c_158])).

tff(c_164,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_30,plain,(
    ! [A_28,B_44,D_56] :
      ( m1_subset_1('#skF_2'(A_28,B_44,D_56,D_56),u1_struct_0(A_28))
      | r1_lattice3(A_28,k2_relset_1(u1_struct_0(B_44),u1_struct_0(A_28),u1_waybel_0(A_28,B_44)),D_56)
      | ~ r3_waybel_9(A_28,B_44,D_56)
      | ~ v11_waybel_0(B_44,A_28)
      | ~ m1_subset_1(D_56,u1_struct_0(A_28))
      | ~ l1_waybel_0(B_44,A_28)
      | ~ v7_waybel_0(B_44)
      | ~ v4_orders_2(B_44)
      | v2_struct_0(B_44)
      | ~ l1_waybel_9(A_28)
      | ~ v1_compts_1(A_28)
      | ~ v2_lattice3(A_28)
      | ~ v1_lattice3(A_28)
      | ~ v5_orders_2(A_28)
      | ~ v4_orders_2(A_28)
      | ~ v3_orders_2(A_28)
      | ~ v8_pre_topc(A_28)
      | ~ v2_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_221,plain,(
    ! [A_218,B_219,D_220] :
      ( ~ v5_pre_topc(k4_waybel_1(A_218,'#skF_2'(A_218,B_219,D_220,D_220)),A_218,A_218)
      | r1_lattice3(A_218,k2_relset_1(u1_struct_0(B_219),u1_struct_0(A_218),u1_waybel_0(A_218,B_219)),D_220)
      | ~ r3_waybel_9(A_218,B_219,D_220)
      | ~ v11_waybel_0(B_219,A_218)
      | ~ m1_subset_1(D_220,u1_struct_0(A_218))
      | ~ l1_waybel_0(B_219,A_218)
      | ~ v7_waybel_0(B_219)
      | ~ v4_orders_2(B_219)
      | v2_struct_0(B_219)
      | ~ l1_waybel_9(A_218)
      | ~ v1_compts_1(A_218)
      | ~ v2_lattice3(A_218)
      | ~ v1_lattice3(A_218)
      | ~ v5_orders_2(A_218)
      | ~ v4_orders_2(A_218)
      | ~ v3_orders_2(A_218)
      | ~ v8_pre_topc(A_218)
      | ~ v2_pre_topc(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_224,plain,(
    ! [B_219,D_220] :
      ( r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_219),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_219)),D_220)
      | ~ r3_waybel_9('#skF_8',B_219,D_220)
      | ~ v11_waybel_0(B_219,'#skF_8')
      | ~ m1_subset_1(D_220,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_219,'#skF_8')
      | ~ v7_waybel_0(B_219)
      | ~ v4_orders_2(B_219)
      | v2_struct_0(B_219)
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_2'('#skF_8',B_219,D_220,D_220),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_66,c_221])).

tff(c_228,plain,(
    ! [B_221,D_222] :
      ( r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_221),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_221)),D_222)
      | ~ r3_waybel_9('#skF_8',B_221,D_222)
      | ~ v11_waybel_0(B_221,'#skF_8')
      | ~ m1_subset_1(D_222,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_221,'#skF_8')
      | ~ v7_waybel_0(B_221)
      | ~ v4_orders_2(B_221)
      | v2_struct_0(B_221)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_221,D_222,D_222),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_224])).

tff(c_231,plain,(
    ! [B_44,D_56] :
      ( r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_44),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_44)),D_56)
      | ~ r3_waybel_9('#skF_8',B_44,D_56)
      | ~ v11_waybel_0(B_44,'#skF_8')
      | ~ m1_subset_1(D_56,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_44,'#skF_8')
      | ~ v7_waybel_0(B_44)
      | ~ v4_orders_2(B_44)
      | v2_struct_0(B_44)
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_30,c_228])).

tff(c_234,plain,(
    ! [B_44,D_56] :
      ( r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_44),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_44)),D_56)
      | ~ r3_waybel_9('#skF_8',B_44,D_56)
      | ~ v11_waybel_0(B_44,'#skF_8')
      | ~ m1_subset_1(D_56,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_44,'#skF_8')
      | ~ v7_waybel_0(B_44)
      | ~ v4_orders_2(B_44)
      | v2_struct_0(B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_231])).

tff(c_12,plain,(
    ! [A_2,B_14,C_20] :
      ( m1_subset_1('#skF_1'(A_2,B_14,C_20),u1_struct_0(A_2))
      | r2_yellow_0(A_2,C_20)
      | ~ r1_lattice3(A_2,C_20,B_14)
      | ~ m1_subset_1(B_14,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v5_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_2,C_20,B_14] :
      ( r1_lattice3(A_2,C_20,'#skF_1'(A_2,B_14,C_20))
      | r2_yellow_0(A_2,C_20)
      | ~ r1_lattice3(A_2,C_20,B_14)
      | ~ m1_subset_1(B_14,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v5_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_252,plain,(
    ! [A_230,B_231,D_232,E_233] :
      ( m1_subset_1('#skF_3'(A_230,B_231,D_232,D_232),u1_struct_0(A_230))
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
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_496,plain,(
    ! [A_296,B_297,D_298,B_299] :
      ( m1_subset_1('#skF_3'(A_296,B_297,D_298,D_298),u1_struct_0(A_296))
      | r1_orders_2(A_296,'#skF_1'(A_296,B_299,k2_relset_1(u1_struct_0(B_297),u1_struct_0(A_296),u1_waybel_0(A_296,B_297))),D_298)
      | ~ m1_subset_1('#skF_1'(A_296,B_299,k2_relset_1(u1_struct_0(B_297),u1_struct_0(A_296),u1_waybel_0(A_296,B_297))),u1_struct_0(A_296))
      | ~ r3_waybel_9(A_296,B_297,D_298)
      | ~ m1_subset_1(D_298,u1_struct_0(A_296))
      | ~ l1_waybel_0(B_297,A_296)
      | ~ v7_waybel_0(B_297)
      | ~ v4_orders_2(B_297)
      | v2_struct_0(B_297)
      | ~ l1_waybel_9(A_296)
      | ~ v1_compts_1(A_296)
      | ~ v2_lattice3(A_296)
      | ~ v1_lattice3(A_296)
      | ~ v4_orders_2(A_296)
      | ~ v3_orders_2(A_296)
      | ~ v8_pre_topc(A_296)
      | ~ v2_pre_topc(A_296)
      | r2_yellow_0(A_296,k2_relset_1(u1_struct_0(B_297),u1_struct_0(A_296),u1_waybel_0(A_296,B_297)))
      | ~ r1_lattice3(A_296,k2_relset_1(u1_struct_0(B_297),u1_struct_0(A_296),u1_waybel_0(A_296,B_297)),B_299)
      | ~ m1_subset_1(B_299,u1_struct_0(A_296))
      | ~ l1_orders_2(A_296)
      | ~ v5_orders_2(A_296) ) ),
    inference(resolution,[status(thm)],[c_10,c_252])).

tff(c_640,plain,(
    ! [A_336,B_337,D_338,B_339] :
      ( m1_subset_1('#skF_3'(A_336,B_337,D_338,D_338),u1_struct_0(A_336))
      | r1_orders_2(A_336,'#skF_1'(A_336,B_339,k2_relset_1(u1_struct_0(B_337),u1_struct_0(A_336),u1_waybel_0(A_336,B_337))),D_338)
      | ~ r3_waybel_9(A_336,B_337,D_338)
      | ~ m1_subset_1(D_338,u1_struct_0(A_336))
      | ~ l1_waybel_0(B_337,A_336)
      | ~ v7_waybel_0(B_337)
      | ~ v4_orders_2(B_337)
      | v2_struct_0(B_337)
      | ~ l1_waybel_9(A_336)
      | ~ v1_compts_1(A_336)
      | ~ v2_lattice3(A_336)
      | ~ v1_lattice3(A_336)
      | ~ v4_orders_2(A_336)
      | ~ v3_orders_2(A_336)
      | ~ v8_pre_topc(A_336)
      | ~ v2_pre_topc(A_336)
      | r2_yellow_0(A_336,k2_relset_1(u1_struct_0(B_337),u1_struct_0(A_336),u1_waybel_0(A_336,B_337)))
      | ~ r1_lattice3(A_336,k2_relset_1(u1_struct_0(B_337),u1_struct_0(A_336),u1_waybel_0(A_336,B_337)),B_339)
      | ~ m1_subset_1(B_339,u1_struct_0(A_336))
      | ~ l1_orders_2(A_336)
      | ~ v5_orders_2(A_336) ) ),
    inference(resolution,[status(thm)],[c_12,c_496])).

tff(c_8,plain,(
    ! [A_2,B_14,C_20] :
      ( ~ r1_orders_2(A_2,'#skF_1'(A_2,B_14,C_20),B_14)
      | r2_yellow_0(A_2,C_20)
      | ~ r1_lattice3(A_2,C_20,B_14)
      | ~ m1_subset_1(B_14,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v5_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_779,plain,(
    ! [A_360,B_361,D_362] :
      ( m1_subset_1('#skF_3'(A_360,B_361,D_362,D_362),u1_struct_0(A_360))
      | ~ r3_waybel_9(A_360,B_361,D_362)
      | ~ l1_waybel_0(B_361,A_360)
      | ~ v7_waybel_0(B_361)
      | ~ v4_orders_2(B_361)
      | v2_struct_0(B_361)
      | ~ l1_waybel_9(A_360)
      | ~ v1_compts_1(A_360)
      | ~ v2_lattice3(A_360)
      | ~ v1_lattice3(A_360)
      | ~ v4_orders_2(A_360)
      | ~ v3_orders_2(A_360)
      | ~ v8_pre_topc(A_360)
      | ~ v2_pre_topc(A_360)
      | r2_yellow_0(A_360,k2_relset_1(u1_struct_0(B_361),u1_struct_0(A_360),u1_waybel_0(A_360,B_361)))
      | ~ r1_lattice3(A_360,k2_relset_1(u1_struct_0(B_361),u1_struct_0(A_360),u1_waybel_0(A_360,B_361)),D_362)
      | ~ m1_subset_1(D_362,u1_struct_0(A_360))
      | ~ l1_orders_2(A_360)
      | ~ v5_orders_2(A_360) ) ),
    inference(resolution,[status(thm)],[c_640,c_8])).

tff(c_781,plain,(
    ! [B_44,D_56] :
      ( m1_subset_1('#skF_3'('#skF_8',B_44,D_56,D_56),u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_44),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_44)))
      | ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ r3_waybel_9('#skF_8',B_44,D_56)
      | ~ v11_waybel_0(B_44,'#skF_8')
      | ~ m1_subset_1(D_56,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_44,'#skF_8')
      | ~ v7_waybel_0(B_44)
      | ~ v4_orders_2(B_44)
      | v2_struct_0(B_44) ) ),
    inference(resolution,[status(thm)],[c_234,c_779])).

tff(c_796,plain,(
    ! [B_363,D_364] :
      ( m1_subset_1('#skF_3'('#skF_8',B_363,D_364,D_364),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_363),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_363)))
      | ~ r3_waybel_9('#skF_8',B_363,D_364)
      | ~ v11_waybel_0(B_363,'#skF_8')
      | ~ m1_subset_1(D_364,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_363,'#skF_8')
      | ~ v7_waybel_0(B_363)
      | ~ v4_orders_2(B_363)
      | v2_struct_0(B_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89,c_84,c_82,c_80,c_78,c_74,c_72,c_70,c_68,c_781])).

tff(c_300,plain,(
    ! [A_242,B_243,D_244,E_245] :
      ( ~ v5_pre_topc(k4_waybel_1(A_242,'#skF_3'(A_242,B_243,D_244,D_244)),A_242,A_242)
      | r1_orders_2(A_242,E_245,D_244)
      | ~ r1_lattice3(A_242,k2_relset_1(u1_struct_0(B_243),u1_struct_0(A_242),u1_waybel_0(A_242,B_243)),E_245)
      | ~ m1_subset_1(E_245,u1_struct_0(A_242))
      | ~ r3_waybel_9(A_242,B_243,D_244)
      | ~ m1_subset_1(D_244,u1_struct_0(A_242))
      | ~ l1_waybel_0(B_243,A_242)
      | ~ v7_waybel_0(B_243)
      | ~ v4_orders_2(B_243)
      | v2_struct_0(B_243)
      | ~ l1_waybel_9(A_242)
      | ~ v1_compts_1(A_242)
      | ~ v2_lattice3(A_242)
      | ~ v1_lattice3(A_242)
      | ~ v5_orders_2(A_242)
      | ~ v4_orders_2(A_242)
      | ~ v3_orders_2(A_242)
      | ~ v8_pre_topc(A_242)
      | ~ v2_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_303,plain,(
    ! [E_245,D_244,B_243] :
      ( r1_orders_2('#skF_8',E_245,D_244)
      | ~ r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_243),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_243)),E_245)
      | ~ m1_subset_1(E_245,u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8',B_243,D_244)
      | ~ m1_subset_1(D_244,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_243,'#skF_8')
      | ~ v7_waybel_0(B_243)
      | ~ v4_orders_2(B_243)
      | v2_struct_0(B_243)
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_8',B_243,D_244,D_244),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_66,c_300])).

tff(c_307,plain,(
    ! [E_246,D_247,B_248] :
      ( r1_orders_2('#skF_8',E_246,D_247)
      | ~ r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_248),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_248)),E_246)
      | ~ m1_subset_1(E_246,u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8',B_248,D_247)
      | ~ m1_subset_1(D_247,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_248,'#skF_8')
      | ~ v7_waybel_0(B_248)
      | ~ v4_orders_2(B_248)
      | v2_struct_0(B_248)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_248,D_247,D_247),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_303])).

tff(c_318,plain,(
    ! [B_14,B_248,D_247] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8',B_14,k2_relset_1(u1_struct_0(B_248),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_248))),D_247)
      | ~ m1_subset_1('#skF_1'('#skF_8',B_14,k2_relset_1(u1_struct_0(B_248),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_248))),u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8',B_248,D_247)
      | ~ m1_subset_1(D_247,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_248,'#skF_8')
      | ~ v7_waybel_0(B_248)
      | ~ v4_orders_2(B_248)
      | v2_struct_0(B_248)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_248,D_247,D_247),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_248),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_248)))
      | ~ r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_248),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_248)),B_14)
      | ~ m1_subset_1(B_14,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_10,c_307])).

tff(c_431,plain,(
    ! [B_278,B_279,D_280] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8',B_278,k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279))),D_280)
      | ~ m1_subset_1('#skF_1'('#skF_8',B_278,k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279))),u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8',B_279,D_280)
      | ~ m1_subset_1(D_280,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_279,'#skF_8')
      | ~ v7_waybel_0(B_279)
      | ~ v4_orders_2(B_279)
      | v2_struct_0(B_279)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_279,D_280,D_280),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279)))
      | ~ r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279)),B_278)
      | ~ m1_subset_1(B_278,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89,c_318])).

tff(c_437,plain,(
    ! [B_14,B_279,D_280] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8',B_14,k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279))),D_280)
      | ~ r3_waybel_9('#skF_8',B_279,D_280)
      | ~ m1_subset_1(D_280,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_279,'#skF_8')
      | ~ v7_waybel_0(B_279)
      | ~ v4_orders_2(B_279)
      | v2_struct_0(B_279)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_279,D_280,D_280),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279)))
      | ~ r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279)),B_14)
      | ~ m1_subset_1(B_14,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_12,c_431])).

tff(c_443,plain,(
    ! [B_14,B_279,D_280] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8',B_14,k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279))),D_280)
      | ~ r3_waybel_9('#skF_8',B_279,D_280)
      | ~ m1_subset_1(D_280,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_279,'#skF_8')
      | ~ v7_waybel_0(B_279)
      | ~ v4_orders_2(B_279)
      | v2_struct_0(B_279)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_279,D_280,D_280),u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279)))
      | ~ r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_279),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_279)),B_14)
      | ~ m1_subset_1(B_14,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89,c_437])).

tff(c_866,plain,(
    ! [B_373,B_374,D_375] :
      ( r1_orders_2('#skF_8','#skF_1'('#skF_8',B_373,k2_relset_1(u1_struct_0(B_374),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_374))),D_375)
      | ~ r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_374),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_374)),B_373)
      | ~ m1_subset_1(B_373,u1_struct_0('#skF_8'))
      | r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_374),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_374)))
      | ~ r3_waybel_9('#skF_8',B_374,D_375)
      | ~ v11_waybel_0(B_374,'#skF_8')
      | ~ m1_subset_1(D_375,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_374,'#skF_8')
      | ~ v7_waybel_0(B_374)
      | ~ v4_orders_2(B_374)
      | v2_struct_0(B_374) ) ),
    inference(resolution,[status(thm)],[c_796,c_443])).

tff(c_874,plain,(
    ! [B_374,D_375] :
      ( ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_374),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_374)),D_375)
      | r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_374),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_374)))
      | ~ r3_waybel_9('#skF_8',B_374,D_375)
      | ~ v11_waybel_0(B_374,'#skF_8')
      | ~ m1_subset_1(D_375,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_374,'#skF_8')
      | ~ v7_waybel_0(B_374)
      | ~ v4_orders_2(B_374)
      | v2_struct_0(B_374) ) ),
    inference(resolution,[status(thm)],[c_866,c_8])).

tff(c_881,plain,(
    ! [B_376,D_377] :
      ( ~ r1_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_376),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_376)),D_377)
      | r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_376),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_376)))
      | ~ r3_waybel_9('#skF_8',B_376,D_377)
      | ~ v11_waybel_0(B_376,'#skF_8')
      | ~ m1_subset_1(D_377,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_376,'#skF_8')
      | ~ v7_waybel_0(B_376)
      | ~ v4_orders_2(B_376)
      | v2_struct_0(B_376) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_89,c_874])).

tff(c_907,plain,(
    ! [B_378,D_379] :
      ( r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_378),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_378)))
      | ~ r3_waybel_9('#skF_8',B_378,D_379)
      | ~ v11_waybel_0(B_378,'#skF_8')
      | ~ m1_subset_1(D_379,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_378,'#skF_8')
      | ~ v7_waybel_0(B_378)
      | ~ v4_orders_2(B_378)
      | v2_struct_0(B_378) ) ),
    inference(resolution,[status(thm)],[c_234,c_881])).

tff(c_916,plain,(
    ! [B_108] :
      ( r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_108),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_108)))
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_108),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_36,c_907])).

tff(c_927,plain,(
    ! [B_108] :
      ( r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_108),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_108)))
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_108),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_916])).

tff(c_929,plain,(
    ! [B_380] :
      ( r2_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_380),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_380)))
      | ~ v11_waybel_0(B_380,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_380),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_380,'#skF_8')
      | ~ v7_waybel_0(B_380)
      | ~ v4_orders_2(B_380)
      | v2_struct_0(B_380) ) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_927])).

tff(c_20,plain,(
    ! [A_24,B_26] :
      ( r2_waybel_9(A_24,B_26)
      | ~ r2_yellow_0(A_24,k2_relset_1(u1_struct_0(B_26),u1_struct_0(A_24),u1_waybel_0(A_24,B_26)))
      | ~ l1_waybel_0(B_26,A_24)
      | ~ l1_orders_2(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_932,plain,(
    ! [B_380] :
      ( r2_waybel_9('#skF_8',B_380)
      | ~ l1_orders_2('#skF_8')
      | ~ v11_waybel_0(B_380,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_380),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_380,'#skF_8')
      | ~ v7_waybel_0(B_380)
      | ~ v4_orders_2(B_380)
      | v2_struct_0(B_380) ) ),
    inference(resolution,[status(thm)],[c_929,c_20])).

tff(c_936,plain,(
    ! [B_381] :
      ( r2_waybel_9('#skF_8',B_381)
      | ~ v11_waybel_0(B_381,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_381),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_381,'#skF_8')
      | ~ v7_waybel_0(B_381)
      | ~ v4_orders_2(B_381)
      | v2_struct_0(B_381) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_932])).

tff(c_940,plain,(
    ! [B_108] :
      ( r2_waybel_9('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_38,c_936])).

tff(c_943,plain,(
    ! [B_108] :
      ( r2_waybel_9('#skF_8',B_108)
      | ~ v11_waybel_0(B_108,'#skF_8')
      | ~ l1_waybel_0(B_108,'#skF_8')
      | ~ v7_waybel_0(B_108)
      | ~ v4_orders_2(B_108)
      | v2_struct_0(B_108)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_940])).

tff(c_945,plain,(
    ! [B_382] :
      ( r2_waybel_9('#skF_8',B_382)
      | ~ v11_waybel_0(B_382,'#skF_8')
      | ~ l1_waybel_0(B_382,'#skF_8')
      | ~ v7_waybel_0(B_382)
      | ~ v4_orders_2(B_382)
      | v2_struct_0(B_382) ) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_943])).

tff(c_948,plain,
    ( r2_waybel_9('#skF_8','#skF_9')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_945])).

tff(c_951,plain,
    ( r2_waybel_9('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_58,c_948])).

tff(c_953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_97,c_951])).

tff(c_954,plain,(
    ~ r2_hidden(k1_waybel_9('#skF_8','#skF_9'),k10_yellow_6('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_975,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_9('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_972,c_954])).

tff(c_978,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_9('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_975])).

tff(c_979,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_9('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_978])).

tff(c_980,plain,(
    ~ m1_subset_1(k1_waybel_9('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_979])).

tff(c_1086,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1085,c_980])).

tff(c_1094,plain,
    ( ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_38,c_1086])).

tff(c_1097,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1094])).

tff(c_1099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1059,c_64,c_1097])).

tff(c_1100,plain,
    ( ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8')
    | m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_979])).

tff(c_1110,plain,(
    ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1100])).

tff(c_1210,plain,(
    ~ r3_waybel_9('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1209,c_1110])).

tff(c_1254,plain,
    ( ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_36,c_1210])).

tff(c_1257,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1254])).

tff(c_1259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1181,c_64,c_1257])).

tff(c_1260,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_1262,plain,(
    v2_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1260])).

tff(c_1265,plain,
    ( ~ v1_lattice3('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_1262,c_2])).

tff(c_1269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_74,c_1265])).

tff(c_1271,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1260])).

tff(c_1101,plain,(
    m1_subset_1(k1_waybel_9('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_979])).

tff(c_1261,plain,(
    r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1100])).

tff(c_1283,plain,(
    ! [A_479,B_480,C_481] :
      ( '#skF_6'(A_479,B_480) != '#skF_5'(A_479,B_480)
      | r2_hidden(C_481,k10_yellow_6(A_479,B_480))
      | ~ r3_waybel_9(A_479,B_480,C_481)
      | ~ m1_subset_1(C_481,u1_struct_0(A_479))
      | ~ l1_waybel_0(B_480,A_479)
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480)
      | ~ l1_pre_topc(A_479)
      | ~ v1_compts_1(A_479)
      | ~ v8_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1286,plain,
    ( '#skF_6'('#skF_8','#skF_9') != '#skF_5'('#skF_8','#skF_9')
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_9('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1283,c_954])).

tff(c_1289,plain,
    ( '#skF_6'('#skF_8','#skF_9') != '#skF_5'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1101,c_1261,c_1286])).

tff(c_1290,plain,(
    '#skF_6'('#skF_8','#skF_9') != '#skF_5'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1271,c_64,c_1289])).

tff(c_1270,plain,(
    m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_1260])).

tff(c_1272,plain,(
    ! [A_476,B_477,C_478] :
      ( r3_waybel_9(A_476,B_477,'#skF_5'(A_476,B_477))
      | r2_hidden(C_478,k10_yellow_6(A_476,B_477))
      | ~ r3_waybel_9(A_476,B_477,C_478)
      | ~ m1_subset_1(C_478,u1_struct_0(A_476))
      | ~ l1_waybel_0(B_477,A_476)
      | ~ v7_waybel_0(B_477)
      | ~ v4_orders_2(B_477)
      | v2_struct_0(B_477)
      | ~ l1_pre_topc(A_476)
      | ~ v1_compts_1(A_476)
      | ~ v8_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1275,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_9('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1272,c_954])).

tff(c_1278,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9'))
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1101,c_1261,c_1275])).

tff(c_1279,plain,(
    r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_1271,c_64,c_1278])).

tff(c_1300,plain,(
    ! [A_488,B_489,C_490] :
      ( ~ v5_pre_topc(k4_waybel_1(A_488,'#skF_7'(A_488,B_489,C_490)),A_488,A_488)
      | k1_waybel_9(A_488,C_490) = B_489
      | ~ r3_waybel_9(A_488,C_490,B_489)
      | ~ v11_waybel_0(C_490,A_488)
      | ~ l1_waybel_0(C_490,A_488)
      | ~ v7_waybel_0(C_490)
      | ~ v4_orders_2(C_490)
      | v2_struct_0(C_490)
      | ~ m1_subset_1(B_489,u1_struct_0(A_488))
      | ~ l1_waybel_9(A_488)
      | ~ v1_compts_1(A_488)
      | ~ v2_lattice3(A_488)
      | ~ v1_lattice3(A_488)
      | ~ v5_orders_2(A_488)
      | ~ v4_orders_2(A_488)
      | ~ v3_orders_2(A_488)
      | ~ v8_pre_topc(A_488)
      | ~ v2_pre_topc(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_286])).

tff(c_1304,plain,(
    ! [C_490,B_489] :
      ( k1_waybel_9('#skF_8',C_490) = B_489
      | ~ r3_waybel_9('#skF_8',C_490,B_489)
      | ~ v11_waybel_0(C_490,'#skF_8')
      | ~ l1_waybel_0(C_490,'#skF_8')
      | ~ v7_waybel_0(C_490)
      | ~ v4_orders_2(C_490)
      | v2_struct_0(C_490)
      | ~ m1_subset_1(B_489,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_7'('#skF_8',B_489,C_490),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_66,c_1300])).

tff(c_1309,plain,(
    ! [C_494,B_495] :
      ( k1_waybel_9('#skF_8',C_494) = B_495
      | ~ r3_waybel_9('#skF_8',C_494,B_495)
      | ~ v11_waybel_0(C_494,'#skF_8')
      | ~ l1_waybel_0(C_494,'#skF_8')
      | ~ v7_waybel_0(C_494)
      | ~ v4_orders_2(C_494)
      | v2_struct_0(C_494)
      | ~ m1_subset_1(B_495,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_7'('#skF_8',B_495,C_494),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1304])).

tff(c_1313,plain,(
    ! [C_139,B_135] :
      ( k1_waybel_9('#skF_8',C_139) = B_135
      | ~ r3_waybel_9('#skF_8',C_139,B_135)
      | ~ v11_waybel_0(C_139,'#skF_8')
      | ~ l1_waybel_0(C_139,'#skF_8')
      | ~ v7_waybel_0(C_139)
      | ~ v4_orders_2(C_139)
      | v2_struct_0(C_139)
      | ~ m1_subset_1(B_135,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_1309])).

tff(c_1317,plain,(
    ! [C_496,B_497] :
      ( k1_waybel_9('#skF_8',C_496) = B_497
      | ~ r3_waybel_9('#skF_8',C_496,B_497)
      | ~ v11_waybel_0(C_496,'#skF_8')
      | ~ l1_waybel_0(C_496,'#skF_8')
      | ~ v7_waybel_0(C_496)
      | ~ v4_orders_2(C_496)
      | v2_struct_0(C_496)
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_1313])).

tff(c_1321,plain,
    ( k1_waybel_9('#skF_8','#skF_9') = '#skF_5'('#skF_8','#skF_9')
    | ~ v11_waybel_0('#skF_9','#skF_8')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1279,c_1317])).

tff(c_1339,plain,
    ( k1_waybel_9('#skF_8','#skF_9') = '#skF_5'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_62,c_60,c_58,c_56,c_1321])).

tff(c_1340,plain,(
    k1_waybel_9('#skF_8','#skF_9') = '#skF_5'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1339])).

tff(c_1291,plain,(
    ! [A_482,B_483,C_484] :
      ( m1_subset_1('#skF_6'(A_482,B_483),u1_struct_0(A_482))
      | r2_hidden(C_484,k10_yellow_6(A_482,B_483))
      | ~ r3_waybel_9(A_482,B_483,C_484)
      | ~ m1_subset_1(C_484,u1_struct_0(A_482))
      | ~ l1_waybel_0(B_483,A_482)
      | ~ v7_waybel_0(B_483)
      | ~ v4_orders_2(B_483)
      | v2_struct_0(B_483)
      | ~ l1_pre_topc(A_482)
      | ~ v1_compts_1(A_482)
      | ~ v8_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1294,plain,
    ( m1_subset_1('#skF_6'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_9('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1291,c_954])).

tff(c_1297,plain,
    ( m1_subset_1('#skF_6'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1101,c_1261,c_1294])).

tff(c_1298,plain,(
    m1_subset_1('#skF_6'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1271,c_64,c_1297])).

tff(c_1102,plain,(
    ! [A_446,B_447,C_448] :
      ( r3_waybel_9(A_446,B_447,'#skF_6'(A_446,B_447))
      | r2_hidden(C_448,k10_yellow_6(A_446,B_447))
      | ~ r3_waybel_9(A_446,B_447,C_448)
      | ~ m1_subset_1(C_448,u1_struct_0(A_446))
      | ~ l1_waybel_0(B_447,A_446)
      | ~ v7_waybel_0(B_447)
      | ~ v4_orders_2(B_447)
      | v2_struct_0(B_447)
      | ~ l1_pre_topc(A_446)
      | ~ v1_compts_1(A_446)
      | ~ v8_pre_topc(A_446)
      | ~ v2_pre_topc(A_446)
      | v2_struct_0(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1105,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_9('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1102,c_954])).

tff(c_1108,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_70,c_94,c_62,c_60,c_58,c_1101,c_1105])).

tff(c_1109,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_9('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1108])).

tff(c_1281,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1261,c_1109])).

tff(c_1282,plain,(
    r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_1271,c_1281])).

tff(c_1319,plain,
    ( k1_waybel_9('#skF_8','#skF_9') = '#skF_6'('#skF_8','#skF_9')
    | ~ v11_waybel_0('#skF_9','#skF_8')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1282,c_1317])).

tff(c_1335,plain,
    ( k1_waybel_9('#skF_8','#skF_9') = '#skF_6'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1298,c_62,c_60,c_58,c_56,c_1319])).

tff(c_1336,plain,(
    k1_waybel_9('#skF_8','#skF_9') = '#skF_6'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1335])).

tff(c_1367,plain,(
    '#skF_6'('#skF_8','#skF_9') = '#skF_5'('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1340,c_1336])).

tff(c_1369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1290,c_1367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.07/1.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/1.86  
% 5.07/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/1.87  %$ v5_pre_topc > r3_waybel_9 > r1_orders_2 > r1_lattice3 > v11_waybel_0 > r2_yellow_0 > r2_waybel_9 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_compts_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_waybel_1 > k2_yellow_0 > k1_waybel_9 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 5.07/1.87  
% 5.07/1.87  %Foreground sorts:
% 5.07/1.87  
% 5.07/1.87  
% 5.07/1.87  %Background operators:
% 5.07/1.87  
% 5.07/1.87  
% 5.07/1.87  %Foreground operators:
% 5.07/1.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.07/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.07/1.87  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 5.07/1.87  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.07/1.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.07/1.87  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.07/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.07/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.07/1.87  tff(r2_waybel_9, type, r2_waybel_9: ($i * $i) > $o).
% 5.07/1.87  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.07/1.87  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 5.07/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.07/1.87  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.07/1.87  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 5.07/1.87  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 5.07/1.87  tff(v11_waybel_0, type, v11_waybel_0: ($i * $i) > $o).
% 5.07/1.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.07/1.87  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 5.07/1.87  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 5.07/1.87  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 5.07/1.87  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.07/1.87  tff('#skF_9', type, '#skF_9': $i).
% 5.07/1.87  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.07/1.87  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.07/1.87  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.07/1.87  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 5.07/1.87  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 5.07/1.87  tff('#skF_8', type, '#skF_8': $i).
% 5.07/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.07/1.87  tff(k1_waybel_9, type, k1_waybel_9: ($i * $i) > $i).
% 5.07/1.87  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.07/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.07/1.87  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.07/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.07/1.87  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 5.07/1.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.07/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.07/1.87  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 5.07/1.87  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.07/1.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.07/1.87  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 5.07/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.07/1.87  
% 5.07/1.90  tff(f_326, negated_conjecture, ~(![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => ((![B]: (m1_subset_1(B, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, B), A, A))) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v11_waybel_0(B, A) => (r2_waybel_9(A, B) & r2_hidden(k1_waybel_9(A, B), k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_waybel_9)).
% 5.07/1.90  tff(f_81, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 5.07/1.90  tff(f_204, axiom, (![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_waybel_9)).
% 5.07/1.90  tff(f_286, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => ((((![D]: (m1_subset_1(D, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, D), A, A))) & v11_waybel_0(C, A)) & r3_waybel_9(A, C, B)) => (B = k1_waybel_9(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_waybel_9)).
% 5.07/1.90  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 5.07/1.90  tff(f_244, axiom, (![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r3_waybel_9(A, B, C) & r3_waybel_9(A, B, D)) => (C = D)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) => r2_hidden(C, k10_yellow_6(A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_waybel_9)).
% 5.07/1.90  tff(f_128, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & v11_waybel_0(B, A)) & r3_waybel_9(A, B, C)) => r1_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_waybel_9)).
% 5.07/1.90  tff(f_66, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C)) => (r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B)))))) & ((r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B))))) => ((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_yellow_0)).
% 5.07/1.90  tff(f_178, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & r3_waybel_9(A, B, C)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r1_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), E) => r1_orders_2(A, E, D))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l52_waybel_9)).
% 5.07/1.90  tff(f_75, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_waybel_0(B, A) => (r2_waybel_9(A, B) <=> r2_yellow_0(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_waybel_9)).
% 5.07/1.90  tff(c_68, plain, (l1_waybel_9('#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_85, plain, (![A_144]: (l1_orders_2(A_144) | ~l1_waybel_9(A_144))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.07/1.90  tff(c_89, plain, (l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_68, c_85])).
% 5.07/1.90  tff(c_74, plain, (v1_lattice3('#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_84, plain, (v2_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_82, plain, (v8_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_70, plain, (v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_90, plain, (![A_145]: (l1_pre_topc(A_145) | ~l1_waybel_9(A_145))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.07/1.90  tff(c_94, plain, (l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_68, c_90])).
% 5.07/1.90  tff(c_36, plain, (![A_104, B_108]: (r3_waybel_9(A_104, B_108, '#skF_4'(A_104, B_108)) | ~l1_waybel_0(B_108, A_104) | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | ~l1_pre_topc(A_104) | ~v1_compts_1(A_104) | ~v8_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.07/1.90  tff(c_80, plain, (v3_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_78, plain, (v4_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_76, plain, (v5_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_72, plain, (v2_lattice3('#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_52, plain, (![A_127, B_135, C_139]: (m1_subset_1('#skF_7'(A_127, B_135, C_139), u1_struct_0(A_127)) | k1_waybel_9(A_127, C_139)=B_135 | ~r3_waybel_9(A_127, C_139, B_135) | ~v11_waybel_0(C_139, A_127) | ~l1_waybel_0(C_139, A_127) | ~v7_waybel_0(C_139) | ~v4_orders_2(C_139) | v2_struct_0(C_139) | ~m1_subset_1(B_135, u1_struct_0(A_127)) | ~l1_waybel_9(A_127) | ~v1_compts_1(A_127) | ~v2_lattice3(A_127) | ~v1_lattice3(A_127) | ~v5_orders_2(A_127) | ~v4_orders_2(A_127) | ~v3_orders_2(A_127) | ~v8_pre_topc(A_127) | ~v2_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.07/1.90  tff(c_66, plain, (![B_143]: (v5_pre_topc(k4_waybel_1('#skF_8', B_143), '#skF_8', '#skF_8') | ~m1_subset_1(B_143, u1_struct_0('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_1136, plain, (![A_461, B_462, C_463]: (~v5_pre_topc(k4_waybel_1(A_461, '#skF_7'(A_461, B_462, C_463)), A_461, A_461) | k1_waybel_9(A_461, C_463)=B_462 | ~r3_waybel_9(A_461, C_463, B_462) | ~v11_waybel_0(C_463, A_461) | ~l1_waybel_0(C_463, A_461) | ~v7_waybel_0(C_463) | ~v4_orders_2(C_463) | v2_struct_0(C_463) | ~m1_subset_1(B_462, u1_struct_0(A_461)) | ~l1_waybel_9(A_461) | ~v1_compts_1(A_461) | ~v2_lattice3(A_461) | ~v1_lattice3(A_461) | ~v5_orders_2(A_461) | ~v4_orders_2(A_461) | ~v3_orders_2(A_461) | ~v8_pre_topc(A_461) | ~v2_pre_topc(A_461))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.07/1.90  tff(c_1140, plain, (![C_463, B_462]: (k1_waybel_9('#skF_8', C_463)=B_462 | ~r3_waybel_9('#skF_8', C_463, B_462) | ~v11_waybel_0(C_463, '#skF_8') | ~l1_waybel_0(C_463, '#skF_8') | ~v7_waybel_0(C_463) | ~v4_orders_2(C_463) | v2_struct_0(C_463) | ~m1_subset_1(B_462, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_7'('#skF_8', B_462, C_463), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_66, c_1136])).
% 5.07/1.90  tff(c_1144, plain, (![C_464, B_465]: (k1_waybel_9('#skF_8', C_464)=B_465 | ~r3_waybel_9('#skF_8', C_464, B_465) | ~v11_waybel_0(C_464, '#skF_8') | ~l1_waybel_0(C_464, '#skF_8') | ~v7_waybel_0(C_464) | ~v4_orders_2(C_464) | v2_struct_0(C_464) | ~m1_subset_1(B_465, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_7'('#skF_8', B_465, C_464), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1140])).
% 5.07/1.90  tff(c_1148, plain, (![C_139, B_135]: (k1_waybel_9('#skF_8', C_139)=B_135 | ~r3_waybel_9('#skF_8', C_139, B_135) | ~v11_waybel_0(C_139, '#skF_8') | ~l1_waybel_0(C_139, '#skF_8') | ~v7_waybel_0(C_139) | ~v4_orders_2(C_139) | v2_struct_0(C_139) | ~m1_subset_1(B_135, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_52, c_1144])).
% 5.07/1.90  tff(c_1153, plain, (![C_469, B_470]: (k1_waybel_9('#skF_8', C_469)=B_470 | ~r3_waybel_9('#skF_8', C_469, B_470) | ~v11_waybel_0(C_469, '#skF_8') | ~l1_waybel_0(C_469, '#skF_8') | ~v7_waybel_0(C_469) | ~v4_orders_2(C_469) | v2_struct_0(C_469) | ~m1_subset_1(B_470, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1148])).
% 5.07/1.90  tff(c_1162, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_108), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_1153])).
% 5.07/1.90  tff(c_1171, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_108), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1162])).
% 5.07/1.90  tff(c_1172, plain, (v2_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1171])).
% 5.07/1.90  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v1_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.07/1.90  tff(c_1175, plain, (~v1_lattice3('#skF_8') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_1172, c_2])).
% 5.07/1.90  tff(c_1179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_74, c_1175])).
% 5.07/1.90  tff(c_1181, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1171])).
% 5.07/1.90  tff(c_64, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_62, plain, (v4_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_60, plain, (v7_waybel_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_58, plain, (l1_waybel_0('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_56, plain, (v11_waybel_0('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_38, plain, (![A_104, B_108]: (m1_subset_1('#skF_4'(A_104, B_108), u1_struct_0(A_104)) | ~l1_waybel_0(B_108, A_104) | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | ~l1_pre_topc(A_104) | ~v1_compts_1(A_104) | ~v8_pre_topc(A_104) | ~v2_pre_topc(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_204])).
% 5.07/1.90  tff(c_1186, plain, (![B_471]: (k1_waybel_9('#skF_8', B_471)='#skF_4'('#skF_8', B_471) | ~v11_waybel_0(B_471, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_471), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_471, '#skF_8') | ~v7_waybel_0(B_471) | ~v4_orders_2(B_471) | v2_struct_0(B_471))), inference(splitRight, [status(thm)], [c_1171])).
% 5.07/1.90  tff(c_1190, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_1186])).
% 5.07/1.90  tff(c_1193, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1190])).
% 5.07/1.90  tff(c_1202, plain, (![B_475]: (k1_waybel_9('#skF_8', B_475)='#skF_4'('#skF_8', B_475) | ~v11_waybel_0(B_475, '#skF_8') | ~l1_waybel_0(B_475, '#skF_8') | ~v7_waybel_0(B_475) | ~v4_orders_2(B_475) | v2_struct_0(B_475))), inference(negUnitSimplification, [status(thm)], [c_1181, c_1193])).
% 5.07/1.90  tff(c_1205, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_56, c_1202])).
% 5.07/1.90  tff(c_1208, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1205])).
% 5.07/1.90  tff(c_1209, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_64, c_1208])).
% 5.07/1.90  tff(c_1014, plain, (![A_432, B_433, C_434]: (~v5_pre_topc(k4_waybel_1(A_432, '#skF_7'(A_432, B_433, C_434)), A_432, A_432) | k1_waybel_9(A_432, C_434)=B_433 | ~r3_waybel_9(A_432, C_434, B_433) | ~v11_waybel_0(C_434, A_432) | ~l1_waybel_0(C_434, A_432) | ~v7_waybel_0(C_434) | ~v4_orders_2(C_434) | v2_struct_0(C_434) | ~m1_subset_1(B_433, u1_struct_0(A_432)) | ~l1_waybel_9(A_432) | ~v1_compts_1(A_432) | ~v2_lattice3(A_432) | ~v1_lattice3(A_432) | ~v5_orders_2(A_432) | ~v4_orders_2(A_432) | ~v3_orders_2(A_432) | ~v8_pre_topc(A_432) | ~v2_pre_topc(A_432))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.07/1.90  tff(c_1018, plain, (![C_434, B_433]: (k1_waybel_9('#skF_8', C_434)=B_433 | ~r3_waybel_9('#skF_8', C_434, B_433) | ~v11_waybel_0(C_434, '#skF_8') | ~l1_waybel_0(C_434, '#skF_8') | ~v7_waybel_0(C_434) | ~v4_orders_2(C_434) | v2_struct_0(C_434) | ~m1_subset_1(B_433, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_7'('#skF_8', B_433, C_434), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_66, c_1014])).
% 5.07/1.90  tff(c_1022, plain, (![C_435, B_436]: (k1_waybel_9('#skF_8', C_435)=B_436 | ~r3_waybel_9('#skF_8', C_435, B_436) | ~v11_waybel_0(C_435, '#skF_8') | ~l1_waybel_0(C_435, '#skF_8') | ~v7_waybel_0(C_435) | ~v4_orders_2(C_435) | v2_struct_0(C_435) | ~m1_subset_1(B_436, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_7'('#skF_8', B_436, C_435), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1018])).
% 5.07/1.90  tff(c_1026, plain, (![C_139, B_135]: (k1_waybel_9('#skF_8', C_139)=B_135 | ~r3_waybel_9('#skF_8', C_139, B_135) | ~v11_waybel_0(C_139, '#skF_8') | ~l1_waybel_0(C_139, '#skF_8') | ~v7_waybel_0(C_139) | ~v4_orders_2(C_139) | v2_struct_0(C_139) | ~m1_subset_1(B_135, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_52, c_1022])).
% 5.07/1.90  tff(c_1030, plain, (![C_437, B_438]: (k1_waybel_9('#skF_8', C_437)=B_438 | ~r3_waybel_9('#skF_8', C_437, B_438) | ~v11_waybel_0(C_437, '#skF_8') | ~l1_waybel_0(C_437, '#skF_8') | ~v7_waybel_0(C_437) | ~v4_orders_2(C_437) | v2_struct_0(C_437) | ~m1_subset_1(B_438, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1026])).
% 5.07/1.90  tff(c_1039, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_108), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_1030])).
% 5.07/1.90  tff(c_1048, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_108), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1039])).
% 5.07/1.90  tff(c_1050, plain, (v2_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1048])).
% 5.07/1.90  tff(c_1053, plain, (~v1_lattice3('#skF_8') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_1050, c_2])).
% 5.07/1.90  tff(c_1057, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_74, c_1053])).
% 5.07/1.90  tff(c_1059, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1048])).
% 5.07/1.90  tff(c_1069, plain, (![B_444]: (k1_waybel_9('#skF_8', B_444)='#skF_4'('#skF_8', B_444) | ~v11_waybel_0(B_444, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_444), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_444, '#skF_8') | ~v7_waybel_0(B_444) | ~v4_orders_2(B_444) | v2_struct_0(B_444))), inference(splitRight, [status(thm)], [c_1048])).
% 5.07/1.90  tff(c_1073, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_1069])).
% 5.07/1.90  tff(c_1076, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_1073])).
% 5.07/1.90  tff(c_1078, plain, (![B_445]: (k1_waybel_9('#skF_8', B_445)='#skF_4'('#skF_8', B_445) | ~v11_waybel_0(B_445, '#skF_8') | ~l1_waybel_0(B_445, '#skF_8') | ~v7_waybel_0(B_445) | ~v4_orders_2(B_445) | v2_struct_0(B_445))), inference(negUnitSimplification, [status(thm)], [c_1059, c_1076])).
% 5.07/1.90  tff(c_1081, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_56, c_1078])).
% 5.07/1.90  tff(c_1084, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_1081])).
% 5.07/1.90  tff(c_1085, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_64, c_1084])).
% 5.07/1.90  tff(c_972, plain, (![A_414, B_415, C_416]: (m1_subset_1('#skF_5'(A_414, B_415), u1_struct_0(A_414)) | r2_hidden(C_416, k10_yellow_6(A_414, B_415)) | ~r3_waybel_9(A_414, B_415, C_416) | ~m1_subset_1(C_416, u1_struct_0(A_414)) | ~l1_waybel_0(B_415, A_414) | ~v7_waybel_0(B_415) | ~v4_orders_2(B_415) | v2_struct_0(B_415) | ~l1_pre_topc(A_414) | ~v1_compts_1(A_414) | ~v8_pre_topc(A_414) | ~v2_pre_topc(A_414) | v2_struct_0(A_414))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.90  tff(c_54, plain, (~r2_hidden(k1_waybel_9('#skF_8', '#skF_9'), k10_yellow_6('#skF_8', '#skF_9')) | ~r2_waybel_9('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_326])).
% 5.07/1.90  tff(c_97, plain, (~r2_waybel_9('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_54])).
% 5.07/1.90  tff(c_120, plain, (![A_197, B_198, C_199]: (~v5_pre_topc(k4_waybel_1(A_197, '#skF_7'(A_197, B_198, C_199)), A_197, A_197) | k1_waybel_9(A_197, C_199)=B_198 | ~r3_waybel_9(A_197, C_199, B_198) | ~v11_waybel_0(C_199, A_197) | ~l1_waybel_0(C_199, A_197) | ~v7_waybel_0(C_199) | ~v4_orders_2(C_199) | v2_struct_0(C_199) | ~m1_subset_1(B_198, u1_struct_0(A_197)) | ~l1_waybel_9(A_197) | ~v1_compts_1(A_197) | ~v2_lattice3(A_197) | ~v1_lattice3(A_197) | ~v5_orders_2(A_197) | ~v4_orders_2(A_197) | ~v3_orders_2(A_197) | ~v8_pre_topc(A_197) | ~v2_pre_topc(A_197))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.07/1.90  tff(c_124, plain, (![C_199, B_198]: (k1_waybel_9('#skF_8', C_199)=B_198 | ~r3_waybel_9('#skF_8', C_199, B_198) | ~v11_waybel_0(C_199, '#skF_8') | ~l1_waybel_0(C_199, '#skF_8') | ~v7_waybel_0(C_199) | ~v4_orders_2(C_199) | v2_struct_0(C_199) | ~m1_subset_1(B_198, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_7'('#skF_8', B_198, C_199), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_66, c_120])).
% 5.07/1.90  tff(c_128, plain, (![C_200, B_201]: (k1_waybel_9('#skF_8', C_200)=B_201 | ~r3_waybel_9('#skF_8', C_200, B_201) | ~v11_waybel_0(C_200, '#skF_8') | ~l1_waybel_0(C_200, '#skF_8') | ~v7_waybel_0(C_200) | ~v4_orders_2(C_200) | v2_struct_0(C_200) | ~m1_subset_1(B_201, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_7'('#skF_8', B_201, C_200), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_124])).
% 5.07/1.90  tff(c_132, plain, (![C_139, B_135]: (k1_waybel_9('#skF_8', C_139)=B_135 | ~r3_waybel_9('#skF_8', C_139, B_135) | ~v11_waybel_0(C_139, '#skF_8') | ~l1_waybel_0(C_139, '#skF_8') | ~v7_waybel_0(C_139) | ~v4_orders_2(C_139) | v2_struct_0(C_139) | ~m1_subset_1(B_135, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_52, c_128])).
% 5.07/1.90  tff(c_136, plain, (![C_202, B_203]: (k1_waybel_9('#skF_8', C_202)=B_203 | ~r3_waybel_9('#skF_8', C_202, B_203) | ~v11_waybel_0(C_202, '#skF_8') | ~l1_waybel_0(C_202, '#skF_8') | ~v7_waybel_0(C_202) | ~v4_orders_2(C_202) | v2_struct_0(C_202) | ~m1_subset_1(B_203, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_132])).
% 5.07/1.90  tff(c_145, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_108), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_136])).
% 5.07/1.90  tff(c_154, plain, (![B_108]: (k1_waybel_9('#skF_8', B_108)='#skF_4'('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_108), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_145])).
% 5.07/1.90  tff(c_155, plain, (v2_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_154])).
% 5.07/1.90  tff(c_158, plain, (~v1_lattice3('#skF_8') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_155, c_2])).
% 5.07/1.90  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_74, c_158])).
% 5.07/1.90  tff(c_164, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_154])).
% 5.07/1.90  tff(c_30, plain, (![A_28, B_44, D_56]: (m1_subset_1('#skF_2'(A_28, B_44, D_56, D_56), u1_struct_0(A_28)) | r1_lattice3(A_28, k2_relset_1(u1_struct_0(B_44), u1_struct_0(A_28), u1_waybel_0(A_28, B_44)), D_56) | ~r3_waybel_9(A_28, B_44, D_56) | ~v11_waybel_0(B_44, A_28) | ~m1_subset_1(D_56, u1_struct_0(A_28)) | ~l1_waybel_0(B_44, A_28) | ~v7_waybel_0(B_44) | ~v4_orders_2(B_44) | v2_struct_0(B_44) | ~l1_waybel_9(A_28) | ~v1_compts_1(A_28) | ~v2_lattice3(A_28) | ~v1_lattice3(A_28) | ~v5_orders_2(A_28) | ~v4_orders_2(A_28) | ~v3_orders_2(A_28) | ~v8_pre_topc(A_28) | ~v2_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.07/1.90  tff(c_221, plain, (![A_218, B_219, D_220]: (~v5_pre_topc(k4_waybel_1(A_218, '#skF_2'(A_218, B_219, D_220, D_220)), A_218, A_218) | r1_lattice3(A_218, k2_relset_1(u1_struct_0(B_219), u1_struct_0(A_218), u1_waybel_0(A_218, B_219)), D_220) | ~r3_waybel_9(A_218, B_219, D_220) | ~v11_waybel_0(B_219, A_218) | ~m1_subset_1(D_220, u1_struct_0(A_218)) | ~l1_waybel_0(B_219, A_218) | ~v7_waybel_0(B_219) | ~v4_orders_2(B_219) | v2_struct_0(B_219) | ~l1_waybel_9(A_218) | ~v1_compts_1(A_218) | ~v2_lattice3(A_218) | ~v1_lattice3(A_218) | ~v5_orders_2(A_218) | ~v4_orders_2(A_218) | ~v3_orders_2(A_218) | ~v8_pre_topc(A_218) | ~v2_pre_topc(A_218))), inference(cnfTransformation, [status(thm)], [f_128])).
% 5.07/1.90  tff(c_224, plain, (![B_219, D_220]: (r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_219), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_219)), D_220) | ~r3_waybel_9('#skF_8', B_219, D_220) | ~v11_waybel_0(B_219, '#skF_8') | ~m1_subset_1(D_220, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_219, '#skF_8') | ~v7_waybel_0(B_219) | ~v4_orders_2(B_219) | v2_struct_0(B_219) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_2'('#skF_8', B_219, D_220, D_220), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_66, c_221])).
% 5.07/1.90  tff(c_228, plain, (![B_221, D_222]: (r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_221), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_221)), D_222) | ~r3_waybel_9('#skF_8', B_221, D_222) | ~v11_waybel_0(B_221, '#skF_8') | ~m1_subset_1(D_222, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_221, '#skF_8') | ~v7_waybel_0(B_221) | ~v4_orders_2(B_221) | v2_struct_0(B_221) | ~m1_subset_1('#skF_2'('#skF_8', B_221, D_222, D_222), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_224])).
% 5.07/1.90  tff(c_231, plain, (![B_44, D_56]: (r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_44), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_44)), D_56) | ~r3_waybel_9('#skF_8', B_44, D_56) | ~v11_waybel_0(B_44, '#skF_8') | ~m1_subset_1(D_56, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_44, '#skF_8') | ~v7_waybel_0(B_44) | ~v4_orders_2(B_44) | v2_struct_0(B_44) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_30, c_228])).
% 5.07/1.90  tff(c_234, plain, (![B_44, D_56]: (r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_44), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_44)), D_56) | ~r3_waybel_9('#skF_8', B_44, D_56) | ~v11_waybel_0(B_44, '#skF_8') | ~m1_subset_1(D_56, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_44, '#skF_8') | ~v7_waybel_0(B_44) | ~v4_orders_2(B_44) | v2_struct_0(B_44))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_231])).
% 5.07/1.90  tff(c_12, plain, (![A_2, B_14, C_20]: (m1_subset_1('#skF_1'(A_2, B_14, C_20), u1_struct_0(A_2)) | r2_yellow_0(A_2, C_20) | ~r1_lattice3(A_2, C_20, B_14) | ~m1_subset_1(B_14, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v5_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.07/1.90  tff(c_10, plain, (![A_2, C_20, B_14]: (r1_lattice3(A_2, C_20, '#skF_1'(A_2, B_14, C_20)) | r2_yellow_0(A_2, C_20) | ~r1_lattice3(A_2, C_20, B_14) | ~m1_subset_1(B_14, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v5_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.07/1.90  tff(c_252, plain, (![A_230, B_231, D_232, E_233]: (m1_subset_1('#skF_3'(A_230, B_231, D_232, D_232), u1_struct_0(A_230)) | r1_orders_2(A_230, E_233, D_232) | ~r1_lattice3(A_230, k2_relset_1(u1_struct_0(B_231), u1_struct_0(A_230), u1_waybel_0(A_230, B_231)), E_233) | ~m1_subset_1(E_233, u1_struct_0(A_230)) | ~r3_waybel_9(A_230, B_231, D_232) | ~m1_subset_1(D_232, u1_struct_0(A_230)) | ~l1_waybel_0(B_231, A_230) | ~v7_waybel_0(B_231) | ~v4_orders_2(B_231) | v2_struct_0(B_231) | ~l1_waybel_9(A_230) | ~v1_compts_1(A_230) | ~v2_lattice3(A_230) | ~v1_lattice3(A_230) | ~v5_orders_2(A_230) | ~v4_orders_2(A_230) | ~v3_orders_2(A_230) | ~v8_pre_topc(A_230) | ~v2_pre_topc(A_230))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.07/1.90  tff(c_496, plain, (![A_296, B_297, D_298, B_299]: (m1_subset_1('#skF_3'(A_296, B_297, D_298, D_298), u1_struct_0(A_296)) | r1_orders_2(A_296, '#skF_1'(A_296, B_299, k2_relset_1(u1_struct_0(B_297), u1_struct_0(A_296), u1_waybel_0(A_296, B_297))), D_298) | ~m1_subset_1('#skF_1'(A_296, B_299, k2_relset_1(u1_struct_0(B_297), u1_struct_0(A_296), u1_waybel_0(A_296, B_297))), u1_struct_0(A_296)) | ~r3_waybel_9(A_296, B_297, D_298) | ~m1_subset_1(D_298, u1_struct_0(A_296)) | ~l1_waybel_0(B_297, A_296) | ~v7_waybel_0(B_297) | ~v4_orders_2(B_297) | v2_struct_0(B_297) | ~l1_waybel_9(A_296) | ~v1_compts_1(A_296) | ~v2_lattice3(A_296) | ~v1_lattice3(A_296) | ~v4_orders_2(A_296) | ~v3_orders_2(A_296) | ~v8_pre_topc(A_296) | ~v2_pre_topc(A_296) | r2_yellow_0(A_296, k2_relset_1(u1_struct_0(B_297), u1_struct_0(A_296), u1_waybel_0(A_296, B_297))) | ~r1_lattice3(A_296, k2_relset_1(u1_struct_0(B_297), u1_struct_0(A_296), u1_waybel_0(A_296, B_297)), B_299) | ~m1_subset_1(B_299, u1_struct_0(A_296)) | ~l1_orders_2(A_296) | ~v5_orders_2(A_296))), inference(resolution, [status(thm)], [c_10, c_252])).
% 5.07/1.90  tff(c_640, plain, (![A_336, B_337, D_338, B_339]: (m1_subset_1('#skF_3'(A_336, B_337, D_338, D_338), u1_struct_0(A_336)) | r1_orders_2(A_336, '#skF_1'(A_336, B_339, k2_relset_1(u1_struct_0(B_337), u1_struct_0(A_336), u1_waybel_0(A_336, B_337))), D_338) | ~r3_waybel_9(A_336, B_337, D_338) | ~m1_subset_1(D_338, u1_struct_0(A_336)) | ~l1_waybel_0(B_337, A_336) | ~v7_waybel_0(B_337) | ~v4_orders_2(B_337) | v2_struct_0(B_337) | ~l1_waybel_9(A_336) | ~v1_compts_1(A_336) | ~v2_lattice3(A_336) | ~v1_lattice3(A_336) | ~v4_orders_2(A_336) | ~v3_orders_2(A_336) | ~v8_pre_topc(A_336) | ~v2_pre_topc(A_336) | r2_yellow_0(A_336, k2_relset_1(u1_struct_0(B_337), u1_struct_0(A_336), u1_waybel_0(A_336, B_337))) | ~r1_lattice3(A_336, k2_relset_1(u1_struct_0(B_337), u1_struct_0(A_336), u1_waybel_0(A_336, B_337)), B_339) | ~m1_subset_1(B_339, u1_struct_0(A_336)) | ~l1_orders_2(A_336) | ~v5_orders_2(A_336))), inference(resolution, [status(thm)], [c_12, c_496])).
% 5.07/1.90  tff(c_8, plain, (![A_2, B_14, C_20]: (~r1_orders_2(A_2, '#skF_1'(A_2, B_14, C_20), B_14) | r2_yellow_0(A_2, C_20) | ~r1_lattice3(A_2, C_20, B_14) | ~m1_subset_1(B_14, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v5_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.07/1.90  tff(c_779, plain, (![A_360, B_361, D_362]: (m1_subset_1('#skF_3'(A_360, B_361, D_362, D_362), u1_struct_0(A_360)) | ~r3_waybel_9(A_360, B_361, D_362) | ~l1_waybel_0(B_361, A_360) | ~v7_waybel_0(B_361) | ~v4_orders_2(B_361) | v2_struct_0(B_361) | ~l1_waybel_9(A_360) | ~v1_compts_1(A_360) | ~v2_lattice3(A_360) | ~v1_lattice3(A_360) | ~v4_orders_2(A_360) | ~v3_orders_2(A_360) | ~v8_pre_topc(A_360) | ~v2_pre_topc(A_360) | r2_yellow_0(A_360, k2_relset_1(u1_struct_0(B_361), u1_struct_0(A_360), u1_waybel_0(A_360, B_361))) | ~r1_lattice3(A_360, k2_relset_1(u1_struct_0(B_361), u1_struct_0(A_360), u1_waybel_0(A_360, B_361)), D_362) | ~m1_subset_1(D_362, u1_struct_0(A_360)) | ~l1_orders_2(A_360) | ~v5_orders_2(A_360))), inference(resolution, [status(thm)], [c_640, c_8])).
% 5.07/1.90  tff(c_781, plain, (![B_44, D_56]: (m1_subset_1('#skF_3'('#skF_8', B_44, D_56, D_56), u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_44), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_44))) | ~l1_orders_2('#skF_8') | ~v5_orders_2('#skF_8') | ~r3_waybel_9('#skF_8', B_44, D_56) | ~v11_waybel_0(B_44, '#skF_8') | ~m1_subset_1(D_56, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_44, '#skF_8') | ~v7_waybel_0(B_44) | ~v4_orders_2(B_44) | v2_struct_0(B_44))), inference(resolution, [status(thm)], [c_234, c_779])).
% 5.07/1.90  tff(c_796, plain, (![B_363, D_364]: (m1_subset_1('#skF_3'('#skF_8', B_363, D_364, D_364), u1_struct_0('#skF_8')) | r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_363), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_363))) | ~r3_waybel_9('#skF_8', B_363, D_364) | ~v11_waybel_0(B_363, '#skF_8') | ~m1_subset_1(D_364, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_363, '#skF_8') | ~v7_waybel_0(B_363) | ~v4_orders_2(B_363) | v2_struct_0(B_363))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89, c_84, c_82, c_80, c_78, c_74, c_72, c_70, c_68, c_781])).
% 5.07/1.90  tff(c_300, plain, (![A_242, B_243, D_244, E_245]: (~v5_pre_topc(k4_waybel_1(A_242, '#skF_3'(A_242, B_243, D_244, D_244)), A_242, A_242) | r1_orders_2(A_242, E_245, D_244) | ~r1_lattice3(A_242, k2_relset_1(u1_struct_0(B_243), u1_struct_0(A_242), u1_waybel_0(A_242, B_243)), E_245) | ~m1_subset_1(E_245, u1_struct_0(A_242)) | ~r3_waybel_9(A_242, B_243, D_244) | ~m1_subset_1(D_244, u1_struct_0(A_242)) | ~l1_waybel_0(B_243, A_242) | ~v7_waybel_0(B_243) | ~v4_orders_2(B_243) | v2_struct_0(B_243) | ~l1_waybel_9(A_242) | ~v1_compts_1(A_242) | ~v2_lattice3(A_242) | ~v1_lattice3(A_242) | ~v5_orders_2(A_242) | ~v4_orders_2(A_242) | ~v3_orders_2(A_242) | ~v8_pre_topc(A_242) | ~v2_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.07/1.90  tff(c_303, plain, (![E_245, D_244, B_243]: (r1_orders_2('#skF_8', E_245, D_244) | ~r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_243), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_243)), E_245) | ~m1_subset_1(E_245, u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', B_243, D_244) | ~m1_subset_1(D_244, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_243, '#skF_8') | ~v7_waybel_0(B_243) | ~v4_orders_2(B_243) | v2_struct_0(B_243) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_3'('#skF_8', B_243, D_244, D_244), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_66, c_300])).
% 5.07/1.90  tff(c_307, plain, (![E_246, D_247, B_248]: (r1_orders_2('#skF_8', E_246, D_247) | ~r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_248), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_248)), E_246) | ~m1_subset_1(E_246, u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', B_248, D_247) | ~m1_subset_1(D_247, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_248, '#skF_8') | ~v7_waybel_0(B_248) | ~v4_orders_2(B_248) | v2_struct_0(B_248) | ~m1_subset_1('#skF_3'('#skF_8', B_248, D_247, D_247), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_303])).
% 5.07/1.90  tff(c_318, plain, (![B_14, B_248, D_247]: (r1_orders_2('#skF_8', '#skF_1'('#skF_8', B_14, k2_relset_1(u1_struct_0(B_248), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_248))), D_247) | ~m1_subset_1('#skF_1'('#skF_8', B_14, k2_relset_1(u1_struct_0(B_248), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_248))), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', B_248, D_247) | ~m1_subset_1(D_247, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_248, '#skF_8') | ~v7_waybel_0(B_248) | ~v4_orders_2(B_248) | v2_struct_0(B_248) | ~m1_subset_1('#skF_3'('#skF_8', B_248, D_247, D_247), u1_struct_0('#skF_8')) | r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_248), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_248))) | ~r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_248), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_248)), B_14) | ~m1_subset_1(B_14, u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v5_orders_2('#skF_8'))), inference(resolution, [status(thm)], [c_10, c_307])).
% 5.07/1.90  tff(c_431, plain, (![B_278, B_279, D_280]: (r1_orders_2('#skF_8', '#skF_1'('#skF_8', B_278, k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279))), D_280) | ~m1_subset_1('#skF_1'('#skF_8', B_278, k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279))), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', B_279, D_280) | ~m1_subset_1(D_280, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_279, '#skF_8') | ~v7_waybel_0(B_279) | ~v4_orders_2(B_279) | v2_struct_0(B_279) | ~m1_subset_1('#skF_3'('#skF_8', B_279, D_280, D_280), u1_struct_0('#skF_8')) | r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279))) | ~r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279)), B_278) | ~m1_subset_1(B_278, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89, c_318])).
% 5.07/1.90  tff(c_437, plain, (![B_14, B_279, D_280]: (r1_orders_2('#skF_8', '#skF_1'('#skF_8', B_14, k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279))), D_280) | ~r3_waybel_9('#skF_8', B_279, D_280) | ~m1_subset_1(D_280, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_279, '#skF_8') | ~v7_waybel_0(B_279) | ~v4_orders_2(B_279) | v2_struct_0(B_279) | ~m1_subset_1('#skF_3'('#skF_8', B_279, D_280, D_280), u1_struct_0('#skF_8')) | r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279))) | ~r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279)), B_14) | ~m1_subset_1(B_14, u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v5_orders_2('#skF_8'))), inference(resolution, [status(thm)], [c_12, c_431])).
% 5.07/1.90  tff(c_443, plain, (![B_14, B_279, D_280]: (r1_orders_2('#skF_8', '#skF_1'('#skF_8', B_14, k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279))), D_280) | ~r3_waybel_9('#skF_8', B_279, D_280) | ~m1_subset_1(D_280, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_279, '#skF_8') | ~v7_waybel_0(B_279) | ~v4_orders_2(B_279) | v2_struct_0(B_279) | ~m1_subset_1('#skF_3'('#skF_8', B_279, D_280, D_280), u1_struct_0('#skF_8')) | r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279))) | ~r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_279), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_279)), B_14) | ~m1_subset_1(B_14, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89, c_437])).
% 5.07/1.90  tff(c_866, plain, (![B_373, B_374, D_375]: (r1_orders_2('#skF_8', '#skF_1'('#skF_8', B_373, k2_relset_1(u1_struct_0(B_374), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_374))), D_375) | ~r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_374), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_374)), B_373) | ~m1_subset_1(B_373, u1_struct_0('#skF_8')) | r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_374), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_374))) | ~r3_waybel_9('#skF_8', B_374, D_375) | ~v11_waybel_0(B_374, '#skF_8') | ~m1_subset_1(D_375, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_374, '#skF_8') | ~v7_waybel_0(B_374) | ~v4_orders_2(B_374) | v2_struct_0(B_374))), inference(resolution, [status(thm)], [c_796, c_443])).
% 5.07/1.90  tff(c_874, plain, (![B_374, D_375]: (~l1_orders_2('#skF_8') | ~v5_orders_2('#skF_8') | ~r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_374), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_374)), D_375) | r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_374), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_374))) | ~r3_waybel_9('#skF_8', B_374, D_375) | ~v11_waybel_0(B_374, '#skF_8') | ~m1_subset_1(D_375, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_374, '#skF_8') | ~v7_waybel_0(B_374) | ~v4_orders_2(B_374) | v2_struct_0(B_374))), inference(resolution, [status(thm)], [c_866, c_8])).
% 5.07/1.90  tff(c_881, plain, (![B_376, D_377]: (~r1_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_376), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_376)), D_377) | r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_376), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_376))) | ~r3_waybel_9('#skF_8', B_376, D_377) | ~v11_waybel_0(B_376, '#skF_8') | ~m1_subset_1(D_377, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_376, '#skF_8') | ~v7_waybel_0(B_376) | ~v4_orders_2(B_376) | v2_struct_0(B_376))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_89, c_874])).
% 5.07/1.90  tff(c_907, plain, (![B_378, D_379]: (r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_378), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_378))) | ~r3_waybel_9('#skF_8', B_378, D_379) | ~v11_waybel_0(B_378, '#skF_8') | ~m1_subset_1(D_379, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_378, '#skF_8') | ~v7_waybel_0(B_378) | ~v4_orders_2(B_378) | v2_struct_0(B_378))), inference(resolution, [status(thm)], [c_234, c_881])).
% 5.07/1.90  tff(c_916, plain, (![B_108]: (r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_108), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_108))) | ~v11_waybel_0(B_108, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_108), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_36, c_907])).
% 5.07/1.90  tff(c_927, plain, (![B_108]: (r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_108), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_108))) | ~v11_waybel_0(B_108, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_108), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_916])).
% 5.07/1.90  tff(c_929, plain, (![B_380]: (r2_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_380), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_380))) | ~v11_waybel_0(B_380, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_380), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_380, '#skF_8') | ~v7_waybel_0(B_380) | ~v4_orders_2(B_380) | v2_struct_0(B_380))), inference(negUnitSimplification, [status(thm)], [c_164, c_927])).
% 5.07/1.90  tff(c_20, plain, (![A_24, B_26]: (r2_waybel_9(A_24, B_26) | ~r2_yellow_0(A_24, k2_relset_1(u1_struct_0(B_26), u1_struct_0(A_24), u1_waybel_0(A_24, B_26))) | ~l1_waybel_0(B_26, A_24) | ~l1_orders_2(A_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.07/1.90  tff(c_932, plain, (![B_380]: (r2_waybel_9('#skF_8', B_380) | ~l1_orders_2('#skF_8') | ~v11_waybel_0(B_380, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_380), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_380, '#skF_8') | ~v7_waybel_0(B_380) | ~v4_orders_2(B_380) | v2_struct_0(B_380))), inference(resolution, [status(thm)], [c_929, c_20])).
% 5.07/1.90  tff(c_936, plain, (![B_381]: (r2_waybel_9('#skF_8', B_381) | ~v11_waybel_0(B_381, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_381), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_381, '#skF_8') | ~v7_waybel_0(B_381) | ~v4_orders_2(B_381) | v2_struct_0(B_381))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_932])).
% 5.07/1.90  tff(c_940, plain, (![B_108]: (r2_waybel_9('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_38, c_936])).
% 5.07/1.90  tff(c_943, plain, (![B_108]: (r2_waybel_9('#skF_8', B_108) | ~v11_waybel_0(B_108, '#skF_8') | ~l1_waybel_0(B_108, '#skF_8') | ~v7_waybel_0(B_108) | ~v4_orders_2(B_108) | v2_struct_0(B_108) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_940])).
% 5.07/1.90  tff(c_945, plain, (![B_382]: (r2_waybel_9('#skF_8', B_382) | ~v11_waybel_0(B_382, '#skF_8') | ~l1_waybel_0(B_382, '#skF_8') | ~v7_waybel_0(B_382) | ~v4_orders_2(B_382) | v2_struct_0(B_382))), inference(negUnitSimplification, [status(thm)], [c_164, c_943])).
% 5.07/1.90  tff(c_948, plain, (r2_waybel_9('#skF_8', '#skF_9') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_56, c_945])).
% 5.07/1.90  tff(c_951, plain, (r2_waybel_9('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_58, c_948])).
% 5.07/1.90  tff(c_953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_97, c_951])).
% 5.07/1.90  tff(c_954, plain, (~r2_hidden(k1_waybel_9('#skF_8', '#skF_9'), k10_yellow_6('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_54])).
% 5.07/1.90  tff(c_975, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_9('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_972, c_954])).
% 5.07/1.90  tff(c_978, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_9('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_975])).
% 5.07/1.90  tff(c_979, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_9('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_978])).
% 5.07/1.90  tff(c_980, plain, (~m1_subset_1(k1_waybel_9('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_979])).
% 5.07/1.90  tff(c_1086, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1085, c_980])).
% 5.07/1.90  tff(c_1094, plain, (~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_38, c_1086])).
% 5.07/1.90  tff(c_1097, plain, (v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1094])).
% 5.07/1.90  tff(c_1099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1059, c_64, c_1097])).
% 5.07/1.90  tff(c_1100, plain, (~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | v2_struct_0('#skF_8') | m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_979])).
% 5.07/1.90  tff(c_1110, plain, (~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_1100])).
% 5.07/1.90  tff(c_1210, plain, (~r3_waybel_9('#skF_8', '#skF_9', '#skF_4'('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1209, c_1110])).
% 5.07/1.90  tff(c_1254, plain, (~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_36, c_1210])).
% 5.07/1.90  tff(c_1257, plain, (v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1254])).
% 5.07/1.90  tff(c_1259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1181, c_64, c_1257])).
% 5.07/1.90  tff(c_1260, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1100])).
% 5.07/1.90  tff(c_1262, plain, (v2_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1260])).
% 5.07/1.90  tff(c_1265, plain, (~v1_lattice3('#skF_8') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_1262, c_2])).
% 5.07/1.90  tff(c_1269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_74, c_1265])).
% 5.07/1.90  tff(c_1271, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1260])).
% 5.07/1.90  tff(c_1101, plain, (m1_subset_1(k1_waybel_9('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_979])).
% 5.07/1.90  tff(c_1261, plain, (r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_1100])).
% 5.07/1.90  tff(c_1283, plain, (![A_479, B_480, C_481]: ('#skF_6'(A_479, B_480)!='#skF_5'(A_479, B_480) | r2_hidden(C_481, k10_yellow_6(A_479, B_480)) | ~r3_waybel_9(A_479, B_480, C_481) | ~m1_subset_1(C_481, u1_struct_0(A_479)) | ~l1_waybel_0(B_480, A_479) | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480) | ~l1_pre_topc(A_479) | ~v1_compts_1(A_479) | ~v8_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.90  tff(c_1286, plain, ('#skF_6'('#skF_8', '#skF_9')!='#skF_5'('#skF_8', '#skF_9') | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_9('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1283, c_954])).
% 5.07/1.90  tff(c_1289, plain, ('#skF_6'('#skF_8', '#skF_9')!='#skF_5'('#skF_8', '#skF_9') | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1101, c_1261, c_1286])).
% 5.07/1.90  tff(c_1290, plain, ('#skF_6'('#skF_8', '#skF_9')!='#skF_5'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_1271, c_64, c_1289])).
% 5.07/1.90  tff(c_1270, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_1260])).
% 5.07/1.90  tff(c_1272, plain, (![A_476, B_477, C_478]: (r3_waybel_9(A_476, B_477, '#skF_5'(A_476, B_477)) | r2_hidden(C_478, k10_yellow_6(A_476, B_477)) | ~r3_waybel_9(A_476, B_477, C_478) | ~m1_subset_1(C_478, u1_struct_0(A_476)) | ~l1_waybel_0(B_477, A_476) | ~v7_waybel_0(B_477) | ~v4_orders_2(B_477) | v2_struct_0(B_477) | ~l1_pre_topc(A_476) | ~v1_compts_1(A_476) | ~v8_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.90  tff(c_1275, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', '#skF_9')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_9('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1272, c_954])).
% 5.07/1.90  tff(c_1278, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', '#skF_9')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1101, c_1261, c_1275])).
% 5.07/1.90  tff(c_1279, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1271, c_64, c_1278])).
% 5.07/1.90  tff(c_1300, plain, (![A_488, B_489, C_490]: (~v5_pre_topc(k4_waybel_1(A_488, '#skF_7'(A_488, B_489, C_490)), A_488, A_488) | k1_waybel_9(A_488, C_490)=B_489 | ~r3_waybel_9(A_488, C_490, B_489) | ~v11_waybel_0(C_490, A_488) | ~l1_waybel_0(C_490, A_488) | ~v7_waybel_0(C_490) | ~v4_orders_2(C_490) | v2_struct_0(C_490) | ~m1_subset_1(B_489, u1_struct_0(A_488)) | ~l1_waybel_9(A_488) | ~v1_compts_1(A_488) | ~v2_lattice3(A_488) | ~v1_lattice3(A_488) | ~v5_orders_2(A_488) | ~v4_orders_2(A_488) | ~v3_orders_2(A_488) | ~v8_pre_topc(A_488) | ~v2_pre_topc(A_488))), inference(cnfTransformation, [status(thm)], [f_286])).
% 5.07/1.90  tff(c_1304, plain, (![C_490, B_489]: (k1_waybel_9('#skF_8', C_490)=B_489 | ~r3_waybel_9('#skF_8', C_490, B_489) | ~v11_waybel_0(C_490, '#skF_8') | ~l1_waybel_0(C_490, '#skF_8') | ~v7_waybel_0(C_490) | ~v4_orders_2(C_490) | v2_struct_0(C_490) | ~m1_subset_1(B_489, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_7'('#skF_8', B_489, C_490), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_66, c_1300])).
% 5.07/1.90  tff(c_1309, plain, (![C_494, B_495]: (k1_waybel_9('#skF_8', C_494)=B_495 | ~r3_waybel_9('#skF_8', C_494, B_495) | ~v11_waybel_0(C_494, '#skF_8') | ~l1_waybel_0(C_494, '#skF_8') | ~v7_waybel_0(C_494) | ~v4_orders_2(C_494) | v2_struct_0(C_494) | ~m1_subset_1(B_495, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_7'('#skF_8', B_495, C_494), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1304])).
% 5.07/1.90  tff(c_1313, plain, (![C_139, B_135]: (k1_waybel_9('#skF_8', C_139)=B_135 | ~r3_waybel_9('#skF_8', C_139, B_135) | ~v11_waybel_0(C_139, '#skF_8') | ~l1_waybel_0(C_139, '#skF_8') | ~v7_waybel_0(C_139) | ~v4_orders_2(C_139) | v2_struct_0(C_139) | ~m1_subset_1(B_135, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_52, c_1309])).
% 5.07/1.90  tff(c_1317, plain, (![C_496, B_497]: (k1_waybel_9('#skF_8', C_496)=B_497 | ~r3_waybel_9('#skF_8', C_496, B_497) | ~v11_waybel_0(C_496, '#skF_8') | ~l1_waybel_0(C_496, '#skF_8') | ~v7_waybel_0(C_496) | ~v4_orders_2(C_496) | v2_struct_0(C_496) | ~m1_subset_1(B_497, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_1313])).
% 5.07/1.90  tff(c_1321, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_5'('#skF_8', '#skF_9') | ~v11_waybel_0('#skF_9', '#skF_8') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1279, c_1317])).
% 5.07/1.90  tff(c_1339, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_5'('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1270, c_62, c_60, c_58, c_56, c_1321])).
% 5.07/1.90  tff(c_1340, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_5'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_64, c_1339])).
% 5.07/1.90  tff(c_1291, plain, (![A_482, B_483, C_484]: (m1_subset_1('#skF_6'(A_482, B_483), u1_struct_0(A_482)) | r2_hidden(C_484, k10_yellow_6(A_482, B_483)) | ~r3_waybel_9(A_482, B_483, C_484) | ~m1_subset_1(C_484, u1_struct_0(A_482)) | ~l1_waybel_0(B_483, A_482) | ~v7_waybel_0(B_483) | ~v4_orders_2(B_483) | v2_struct_0(B_483) | ~l1_pre_topc(A_482) | ~v1_compts_1(A_482) | ~v8_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.90  tff(c_1294, plain, (m1_subset_1('#skF_6'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_9('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1291, c_954])).
% 5.07/1.90  tff(c_1297, plain, (m1_subset_1('#skF_6'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1101, c_1261, c_1294])).
% 5.07/1.90  tff(c_1298, plain, (m1_subset_1('#skF_6'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1271, c_64, c_1297])).
% 5.07/1.90  tff(c_1102, plain, (![A_446, B_447, C_448]: (r3_waybel_9(A_446, B_447, '#skF_6'(A_446, B_447)) | r2_hidden(C_448, k10_yellow_6(A_446, B_447)) | ~r3_waybel_9(A_446, B_447, C_448) | ~m1_subset_1(C_448, u1_struct_0(A_446)) | ~l1_waybel_0(B_447, A_446) | ~v7_waybel_0(B_447) | ~v4_orders_2(B_447) | v2_struct_0(B_447) | ~l1_pre_topc(A_446) | ~v1_compts_1(A_446) | ~v8_pre_topc(A_446) | ~v2_pre_topc(A_446) | v2_struct_0(A_446))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.07/1.90  tff(c_1105, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_9('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1102, c_954])).
% 5.07/1.90  tff(c_1108, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_70, c_94, c_62, c_60, c_58, c_1101, c_1105])).
% 5.07/1.90  tff(c_1109, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_9('#skF_8', '#skF_9')) | v2_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_1108])).
% 5.07/1.90  tff(c_1281, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9')) | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1261, c_1109])).
% 5.07/1.90  tff(c_1282, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1271, c_1281])).
% 5.07/1.90  tff(c_1319, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_6'('#skF_8', '#skF_9') | ~v11_waybel_0('#skF_9', '#skF_8') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~m1_subset_1('#skF_6'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1282, c_1317])).
% 5.07/1.90  tff(c_1335, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_6'('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1298, c_62, c_60, c_58, c_56, c_1319])).
% 5.07/1.90  tff(c_1336, plain, (k1_waybel_9('#skF_8', '#skF_9')='#skF_6'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_64, c_1335])).
% 5.07/1.90  tff(c_1367, plain, ('#skF_6'('#skF_8', '#skF_9')='#skF_5'('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1340, c_1336])).
% 5.07/1.90  tff(c_1369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1290, c_1367])).
% 5.07/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.07/1.90  
% 5.07/1.90  Inference rules
% 5.07/1.90  ----------------------
% 5.07/1.90  #Ref     : 0
% 5.07/1.90  #Sup     : 160
% 5.07/1.90  #Fact    : 24
% 5.07/1.90  #Define  : 0
% 5.07/1.90  #Split   : 8
% 5.07/1.90  #Chain   : 0
% 5.07/1.90  #Close   : 0
% 5.07/1.90  
% 5.07/1.90  Ordering : KBO
% 5.07/1.90  
% 5.07/1.90  Simplification rules
% 5.07/1.90  ----------------------
% 5.07/1.90  #Subsume      : 89
% 5.07/1.90  #Demod        : 653
% 5.07/1.90  #Tautology    : 13
% 5.07/1.90  #SimpNegUnit  : 74
% 5.07/1.90  #BackRed      : 9
% 5.07/1.90  
% 5.07/1.90  #Partial instantiations: 0
% 5.07/1.90  #Strategies tried      : 1
% 5.07/1.90  
% 5.07/1.90  Timing (in seconds)
% 5.07/1.90  ----------------------
% 5.07/1.91  Preprocessing        : 0.41
% 5.07/1.91  Parsing              : 0.21
% 5.07/1.91  CNF conversion       : 0.04
% 5.07/1.91  Main loop            : 0.70
% 5.07/1.91  Inferencing          : 0.31
% 5.07/1.91  Reduction            : 0.19
% 5.07/1.91  Demodulation         : 0.13
% 5.07/1.91  BG Simplification    : 0.04
% 5.07/1.91  Subsumption          : 0.13
% 5.07/1.91  Abstraction          : 0.03
% 5.07/1.91  MUC search           : 0.00
% 5.07/1.91  Cooper               : 0.00
% 5.07/1.91  Total                : 1.17
% 5.07/1.91  Index Insertion      : 0.00
% 5.07/1.91  Index Deletion       : 0.00
% 5.07/1.91  Index Matching       : 0.00
% 5.07/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
