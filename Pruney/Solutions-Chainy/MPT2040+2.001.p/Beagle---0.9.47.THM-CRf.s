%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:22 EST 2020

% Result     : Theorem 4.96s
% Output     : CNFRefutation 5.56s
% Verified   : 
% Statistics : Number of formulae       :  252 (2562 expanded)
%              Number of leaves         :   52 (1068 expanded)
%              Depth                    :   22
%              Number of atoms          : 1471 (22106 expanded)
%              Number of equality atoms :   73 ( 316 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > r3_waybel_9 > r1_orders_2 > r1_lattice3 > v11_waybel_0 > r2_yellow_0 > r2_waybel_9 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_compts_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_waybel_1 > k1_waybel_9 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_6 > #skF_1 > #skF_10 > #skF_9 > #skF_4 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_5

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(v11_waybel_0,type,(
    v11_waybel_0: ( $i * $i ) > $o )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

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

tff(k1_waybel_9,type,(
    k1_waybel_9: ( $i * $i ) > $i )).

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

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_311,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_waybel_9)).

tff(f_66,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_189,axiom,(
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

tff(f_271,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_waybel_9)).

tff(f_32,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_229,axiom,(
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

tff(f_113,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( r2_yellow_0(A,B)
        <=> ? [C] :
              ( m1_subset_1(C,u1_struct_0(A))
              & r1_lattice3(A,B,C)
              & ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r1_lattice3(A,B,D)
                   => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_yellow_0)).

tff(f_163,axiom,(
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

tff(f_60,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ( r2_waybel_9(A,B)
          <=> r2_yellow_0(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_waybel_9)).

tff(c_64,plain,(
    l1_waybel_9('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_81,plain,(
    ! [A_147] :
      ( l1_orders_2(A_147)
      | ~ l1_waybel_9(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_85,plain,(
    l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_81])).

tff(c_70,plain,(
    v1_lattice3('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_80,plain,(
    v2_pre_topc('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_78,plain,(
    v8_pre_topc('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_66,plain,(
    v1_compts_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_86,plain,(
    ! [A_148] :
      ( l1_pre_topc(A_148)
      | ~ l1_waybel_9(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_90,plain,(
    l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_64,c_86])).

tff(c_58,plain,(
    v4_orders_2('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_56,plain,(
    v7_waybel_0('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_54,plain,(
    l1_waybel_0('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_32,plain,(
    ! [A_107,B_111] :
      ( r3_waybel_9(A_107,B_111,'#skF_5'(A_107,B_111))
      | ~ l1_waybel_0(B_111,A_107)
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_107)
      | ~ v1_compts_1(A_107)
      | ~ v8_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_76,plain,(
    v3_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_74,plain,(
    v4_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_72,plain,(
    v5_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_68,plain,(
    v2_lattice3('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_48,plain,(
    ! [A_130,B_138,C_142] :
      ( m1_subset_1('#skF_8'(A_130,B_138,C_142),u1_struct_0(A_130))
      | k1_waybel_9(A_130,C_142) = B_138
      | ~ r3_waybel_9(A_130,C_142,B_138)
      | ~ v11_waybel_0(C_142,A_130)
      | ~ l1_waybel_0(C_142,A_130)
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0(A_130))
      | ~ l1_waybel_9(A_130)
      | ~ v1_compts_1(A_130)
      | ~ v2_lattice3(A_130)
      | ~ v1_lattice3(A_130)
      | ~ v5_orders_2(A_130)
      | ~ v4_orders_2(A_130)
      | ~ v3_orders_2(A_130)
      | ~ v8_pre_topc(A_130)
      | ~ v2_pre_topc(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_62,plain,(
    ! [B_146] :
      ( v5_pre_topc(k4_waybel_1('#skF_9',B_146),'#skF_9','#skF_9')
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_9')) ) ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_1026,plain,(
    ! [A_440,B_441,C_442] :
      ( ~ v5_pre_topc(k4_waybel_1(A_440,'#skF_8'(A_440,B_441,C_442)),A_440,A_440)
      | k1_waybel_9(A_440,C_442) = B_441
      | ~ r3_waybel_9(A_440,C_442,B_441)
      | ~ v11_waybel_0(C_442,A_440)
      | ~ l1_waybel_0(C_442,A_440)
      | ~ v7_waybel_0(C_442)
      | ~ v4_orders_2(C_442)
      | v2_struct_0(C_442)
      | ~ m1_subset_1(B_441,u1_struct_0(A_440))
      | ~ l1_waybel_9(A_440)
      | ~ v1_compts_1(A_440)
      | ~ v2_lattice3(A_440)
      | ~ v1_lattice3(A_440)
      | ~ v5_orders_2(A_440)
      | ~ v4_orders_2(A_440)
      | ~ v3_orders_2(A_440)
      | ~ v8_pre_topc(A_440)
      | ~ v2_pre_topc(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_1030,plain,(
    ! [C_442,B_441] :
      ( k1_waybel_9('#skF_9',C_442) = B_441
      | ~ r3_waybel_9('#skF_9',C_442,B_441)
      | ~ v11_waybel_0(C_442,'#skF_9')
      | ~ l1_waybel_0(C_442,'#skF_9')
      | ~ v7_waybel_0(C_442)
      | ~ v4_orders_2(C_442)
      | v2_struct_0(C_442)
      | ~ m1_subset_1(B_441,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_8'('#skF_9',B_441,C_442),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_62,c_1026])).

tff(c_1034,plain,(
    ! [C_443,B_444] :
      ( k1_waybel_9('#skF_9',C_443) = B_444
      | ~ r3_waybel_9('#skF_9',C_443,B_444)
      | ~ v11_waybel_0(C_443,'#skF_9')
      | ~ l1_waybel_0(C_443,'#skF_9')
      | ~ v7_waybel_0(C_443)
      | ~ v4_orders_2(C_443)
      | v2_struct_0(C_443)
      | ~ m1_subset_1(B_444,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_8'('#skF_9',B_444,C_443),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_1030])).

tff(c_1038,plain,(
    ! [C_142,B_138] :
      ( k1_waybel_9('#skF_9',C_142) = B_138
      | ~ r3_waybel_9('#skF_9',C_142,B_138)
      | ~ v11_waybel_0(C_142,'#skF_9')
      | ~ l1_waybel_0(C_142,'#skF_9')
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_1034])).

tff(c_1042,plain,(
    ! [C_445,B_446] :
      ( k1_waybel_9('#skF_9',C_445) = B_446
      | ~ r3_waybel_9('#skF_9',C_445,B_446)
      | ~ v11_waybel_0(C_445,'#skF_9')
      | ~ l1_waybel_0(C_445,'#skF_9')
      | ~ v7_waybel_0(C_445)
      | ~ v4_orders_2(C_445)
      | v2_struct_0(C_445)
      | ~ m1_subset_1(B_446,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_1038])).

tff(c_1051,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_1042])).

tff(c_1060,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_1051])).

tff(c_1061,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1060])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v2_struct_0(A_1)
      | ~ v1_lattice3(A_1)
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1064,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_1061,c_2])).

tff(c_1068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_1064])).

tff(c_1070,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_34,plain,(
    ! [A_107,B_111] :
      ( m1_subset_1('#skF_5'(A_107,B_111),u1_struct_0(A_107))
      | ~ l1_waybel_0(B_111,A_107)
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_107)
      | ~ v1_compts_1(A_107)
      | ~ v8_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_52,plain,(
    v11_waybel_0('#skF_10','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_1071,plain,(
    ! [B_447] :
      ( k1_waybel_9('#skF_9',B_447) = '#skF_5'('#skF_9',B_447)
      | ~ v11_waybel_0(B_447,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_447),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_447,'#skF_9')
      | ~ v7_waybel_0(B_447)
      | ~ v4_orders_2(B_447)
      | v2_struct_0(B_447) ) ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_1075,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_1071])).

tff(c_1078,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_1075])).

tff(c_1080,plain,(
    ! [B_448] :
      ( k1_waybel_9('#skF_9',B_448) = '#skF_5'('#skF_9',B_448)
      | ~ v11_waybel_0(B_448,'#skF_9')
      | ~ l1_waybel_0(B_448,'#skF_9')
      | ~ v7_waybel_0(B_448)
      | ~ v4_orders_2(B_448)
      | v2_struct_0(B_448) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1070,c_1078])).

tff(c_1083,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_52,c_1080])).

tff(c_1086,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1083])).

tff(c_1087,plain,(
    k1_waybel_9('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1086])).

tff(c_979,plain,(
    ! [A_419,B_420,C_421] :
      ( '#skF_6'(A_419,B_420) != '#skF_7'(A_419,B_420)
      | r2_hidden(C_421,k10_yellow_6(A_419,B_420))
      | ~ r3_waybel_9(A_419,B_420,C_421)
      | ~ m1_subset_1(C_421,u1_struct_0(A_419))
      | ~ l1_waybel_0(B_420,A_419)
      | ~ v7_waybel_0(B_420)
      | ~ v4_orders_2(B_420)
      | v2_struct_0(B_420)
      | ~ l1_pre_topc(A_419)
      | ~ v1_compts_1(A_419)
      | ~ v8_pre_topc(A_419)
      | ~ v2_pre_topc(A_419)
      | v2_struct_0(A_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_50,plain,
    ( ~ r2_hidden(k1_waybel_9('#skF_9','#skF_10'),k10_yellow_6('#skF_9','#skF_10'))
    | ~ r2_waybel_9('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_311])).

tff(c_92,plain,(
    ~ r2_waybel_9('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_124,plain,(
    ! [A_196,B_197,C_198] :
      ( ~ v5_pre_topc(k4_waybel_1(A_196,'#skF_8'(A_196,B_197,C_198)),A_196,A_196)
      | k1_waybel_9(A_196,C_198) = B_197
      | ~ r3_waybel_9(A_196,C_198,B_197)
      | ~ v11_waybel_0(C_198,A_196)
      | ~ l1_waybel_0(C_198,A_196)
      | ~ v7_waybel_0(C_198)
      | ~ v4_orders_2(C_198)
      | v2_struct_0(C_198)
      | ~ m1_subset_1(B_197,u1_struct_0(A_196))
      | ~ l1_waybel_9(A_196)
      | ~ v1_compts_1(A_196)
      | ~ v2_lattice3(A_196)
      | ~ v1_lattice3(A_196)
      | ~ v5_orders_2(A_196)
      | ~ v4_orders_2(A_196)
      | ~ v3_orders_2(A_196)
      | ~ v8_pre_topc(A_196)
      | ~ v2_pre_topc(A_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_128,plain,(
    ! [C_198,B_197] :
      ( k1_waybel_9('#skF_9',C_198) = B_197
      | ~ r3_waybel_9('#skF_9',C_198,B_197)
      | ~ v11_waybel_0(C_198,'#skF_9')
      | ~ l1_waybel_0(C_198,'#skF_9')
      | ~ v7_waybel_0(C_198)
      | ~ v4_orders_2(C_198)
      | v2_struct_0(C_198)
      | ~ m1_subset_1(B_197,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_8'('#skF_9',B_197,C_198),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_62,c_124])).

tff(c_132,plain,(
    ! [C_199,B_200] :
      ( k1_waybel_9('#skF_9',C_199) = B_200
      | ~ r3_waybel_9('#skF_9',C_199,B_200)
      | ~ v11_waybel_0(C_199,'#skF_9')
      | ~ l1_waybel_0(C_199,'#skF_9')
      | ~ v7_waybel_0(C_199)
      | ~ v4_orders_2(C_199)
      | v2_struct_0(C_199)
      | ~ m1_subset_1(B_200,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_8'('#skF_9',B_200,C_199),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_128])).

tff(c_136,plain,(
    ! [C_142,B_138] :
      ( k1_waybel_9('#skF_9',C_142) = B_138
      | ~ r3_waybel_9('#skF_9',C_142,B_138)
      | ~ v11_waybel_0(C_142,'#skF_9')
      | ~ l1_waybel_0(C_142,'#skF_9')
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_132])).

tff(c_140,plain,(
    ! [C_201,B_202] :
      ( k1_waybel_9('#skF_9',C_201) = B_202
      | ~ r3_waybel_9('#skF_9',C_201,B_202)
      | ~ v11_waybel_0(C_201,'#skF_9')
      | ~ l1_waybel_0(C_201,'#skF_9')
      | ~ v7_waybel_0(C_201)
      | ~ v4_orders_2(C_201)
      | v2_struct_0(C_201)
      | ~ m1_subset_1(B_202,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_136])).

tff(c_149,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_140])).

tff(c_158,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_149])).

tff(c_159,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_162,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_159,c_2])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_162])).

tff(c_168,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_26,plain,(
    ! [A_31,B_47,D_59] :
      ( m1_subset_1('#skF_3'(A_31,B_47,D_59,D_59),u1_struct_0(A_31))
      | r1_lattice3(A_31,k2_relset_1(u1_struct_0(B_47),u1_struct_0(A_31),u1_waybel_0(A_31,B_47)),D_59)
      | ~ r3_waybel_9(A_31,B_47,D_59)
      | ~ v11_waybel_0(B_47,A_31)
      | ~ m1_subset_1(D_59,u1_struct_0(A_31))
      | ~ l1_waybel_0(B_47,A_31)
      | ~ v7_waybel_0(B_47)
      | ~ v4_orders_2(B_47)
      | v2_struct_0(B_47)
      | ~ l1_waybel_9(A_31)
      | ~ v1_compts_1(A_31)
      | ~ v2_lattice3(A_31)
      | ~ v1_lattice3(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | ~ v8_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_241,plain,(
    ! [A_220,B_221,D_222] :
      ( ~ v5_pre_topc(k4_waybel_1(A_220,'#skF_3'(A_220,B_221,D_222,D_222)),A_220,A_220)
      | r1_lattice3(A_220,k2_relset_1(u1_struct_0(B_221),u1_struct_0(A_220),u1_waybel_0(A_220,B_221)),D_222)
      | ~ r3_waybel_9(A_220,B_221,D_222)
      | ~ v11_waybel_0(B_221,A_220)
      | ~ m1_subset_1(D_222,u1_struct_0(A_220))
      | ~ l1_waybel_0(B_221,A_220)
      | ~ v7_waybel_0(B_221)
      | ~ v4_orders_2(B_221)
      | v2_struct_0(B_221)
      | ~ l1_waybel_9(A_220)
      | ~ v1_compts_1(A_220)
      | ~ v2_lattice3(A_220)
      | ~ v1_lattice3(A_220)
      | ~ v5_orders_2(A_220)
      | ~ v4_orders_2(A_220)
      | ~ v3_orders_2(A_220)
      | ~ v8_pre_topc(A_220)
      | ~ v2_pre_topc(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_244,plain,(
    ! [B_221,D_222] :
      ( r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_221),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_221)),D_222)
      | ~ r3_waybel_9('#skF_9',B_221,D_222)
      | ~ v11_waybel_0(B_221,'#skF_9')
      | ~ m1_subset_1(D_222,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_221,'#skF_9')
      | ~ v7_waybel_0(B_221)
      | ~ v4_orders_2(B_221)
      | v2_struct_0(B_221)
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_3'('#skF_9',B_221,D_222,D_222),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_62,c_241])).

tff(c_249,plain,(
    ! [B_225,D_226] :
      ( r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_225),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_225)),D_226)
      | ~ r3_waybel_9('#skF_9',B_225,D_226)
      | ~ v11_waybel_0(B_225,'#skF_9')
      | ~ m1_subset_1(D_226,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_225,'#skF_9')
      | ~ v7_waybel_0(B_225)
      | ~ v4_orders_2(B_225)
      | v2_struct_0(B_225)
      | ~ m1_subset_1('#skF_3'('#skF_9',B_225,D_226,D_226),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_244])).

tff(c_252,plain,(
    ! [B_47,D_59] :
      ( r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_47),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_47)),D_59)
      | ~ r3_waybel_9('#skF_9',B_47,D_59)
      | ~ v11_waybel_0(B_47,'#skF_9')
      | ~ m1_subset_1(D_59,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_47,'#skF_9')
      | ~ v7_waybel_0(B_47)
      | ~ v4_orders_2(B_47)
      | v2_struct_0(B_47)
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_26,c_249])).

tff(c_255,plain,(
    ! [B_47,D_59] :
      ( r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_47),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_47)),D_59)
      | ~ r3_waybel_9('#skF_9',B_47,D_59)
      | ~ v11_waybel_0(B_47,'#skF_9')
      | ~ m1_subset_1(D_59,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_47,'#skF_9')
      | ~ v7_waybel_0(B_47)
      | ~ v4_orders_2(B_47)
      | v2_struct_0(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_252])).

tff(c_14,plain,(
    ! [A_2,B_16,C_23] :
      ( m1_subset_1('#skF_1'(A_2,B_16,C_23),u1_struct_0(A_2))
      | r2_yellow_0(A_2,B_16)
      | ~ r1_lattice3(A_2,B_16,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v5_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_2,B_16,C_23] :
      ( r1_lattice3(A_2,B_16,'#skF_1'(A_2,B_16,C_23))
      | r2_yellow_0(A_2,B_16)
      | ~ r1_lattice3(A_2,B_16,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v5_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_263,plain,(
    ! [A_229,B_230,D_231,E_232] :
      ( m1_subset_1('#skF_4'(A_229,B_230,D_231,D_231),u1_struct_0(A_229))
      | r1_orders_2(A_229,E_232,D_231)
      | ~ r1_lattice3(A_229,k2_relset_1(u1_struct_0(B_230),u1_struct_0(A_229),u1_waybel_0(A_229,B_230)),E_232)
      | ~ m1_subset_1(E_232,u1_struct_0(A_229))
      | ~ r3_waybel_9(A_229,B_230,D_231)
      | ~ m1_subset_1(D_231,u1_struct_0(A_229))
      | ~ l1_waybel_0(B_230,A_229)
      | ~ v7_waybel_0(B_230)
      | ~ v4_orders_2(B_230)
      | v2_struct_0(B_230)
      | ~ l1_waybel_9(A_229)
      | ~ v1_compts_1(A_229)
      | ~ v2_lattice3(A_229)
      | ~ v1_lattice3(A_229)
      | ~ v5_orders_2(A_229)
      | ~ v4_orders_2(A_229)
      | ~ v3_orders_2(A_229)
      | ~ v8_pre_topc(A_229)
      | ~ v2_pre_topc(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_581,plain,(
    ! [A_322,B_323,D_324,C_325] :
      ( m1_subset_1('#skF_4'(A_322,B_323,D_324,D_324),u1_struct_0(A_322))
      | r1_orders_2(A_322,'#skF_1'(A_322,k2_relset_1(u1_struct_0(B_323),u1_struct_0(A_322),u1_waybel_0(A_322,B_323)),C_325),D_324)
      | ~ m1_subset_1('#skF_1'(A_322,k2_relset_1(u1_struct_0(B_323),u1_struct_0(A_322),u1_waybel_0(A_322,B_323)),C_325),u1_struct_0(A_322))
      | ~ r3_waybel_9(A_322,B_323,D_324)
      | ~ m1_subset_1(D_324,u1_struct_0(A_322))
      | ~ l1_waybel_0(B_323,A_322)
      | ~ v7_waybel_0(B_323)
      | ~ v4_orders_2(B_323)
      | v2_struct_0(B_323)
      | ~ l1_waybel_9(A_322)
      | ~ v1_compts_1(A_322)
      | ~ v2_lattice3(A_322)
      | ~ v1_lattice3(A_322)
      | ~ v4_orders_2(A_322)
      | ~ v3_orders_2(A_322)
      | ~ v8_pre_topc(A_322)
      | ~ v2_pre_topc(A_322)
      | r2_yellow_0(A_322,k2_relset_1(u1_struct_0(B_323),u1_struct_0(A_322),u1_waybel_0(A_322,B_323)))
      | ~ r1_lattice3(A_322,k2_relset_1(u1_struct_0(B_323),u1_struct_0(A_322),u1_waybel_0(A_322,B_323)),C_325)
      | ~ m1_subset_1(C_325,u1_struct_0(A_322))
      | ~ l1_orders_2(A_322)
      | ~ v5_orders_2(A_322) ) ),
    inference(resolution,[status(thm)],[c_12,c_263])).

tff(c_725,plain,(
    ! [A_357,B_358,D_359,C_360] :
      ( m1_subset_1('#skF_4'(A_357,B_358,D_359,D_359),u1_struct_0(A_357))
      | r1_orders_2(A_357,'#skF_1'(A_357,k2_relset_1(u1_struct_0(B_358),u1_struct_0(A_357),u1_waybel_0(A_357,B_358)),C_360),D_359)
      | ~ r3_waybel_9(A_357,B_358,D_359)
      | ~ m1_subset_1(D_359,u1_struct_0(A_357))
      | ~ l1_waybel_0(B_358,A_357)
      | ~ v7_waybel_0(B_358)
      | ~ v4_orders_2(B_358)
      | v2_struct_0(B_358)
      | ~ l1_waybel_9(A_357)
      | ~ v1_compts_1(A_357)
      | ~ v2_lattice3(A_357)
      | ~ v1_lattice3(A_357)
      | ~ v4_orders_2(A_357)
      | ~ v3_orders_2(A_357)
      | ~ v8_pre_topc(A_357)
      | ~ v2_pre_topc(A_357)
      | r2_yellow_0(A_357,k2_relset_1(u1_struct_0(B_358),u1_struct_0(A_357),u1_waybel_0(A_357,B_358)))
      | ~ r1_lattice3(A_357,k2_relset_1(u1_struct_0(B_358),u1_struct_0(A_357),u1_waybel_0(A_357,B_358)),C_360)
      | ~ m1_subset_1(C_360,u1_struct_0(A_357))
      | ~ l1_orders_2(A_357)
      | ~ v5_orders_2(A_357) ) ),
    inference(resolution,[status(thm)],[c_14,c_581])).

tff(c_10,plain,(
    ! [A_2,B_16,C_23] :
      ( ~ r1_orders_2(A_2,'#skF_1'(A_2,B_16,C_23),C_23)
      | r2_yellow_0(A_2,B_16)
      | ~ r1_lattice3(A_2,B_16,C_23)
      | ~ m1_subset_1(C_23,u1_struct_0(A_2))
      | ~ l1_orders_2(A_2)
      | ~ v5_orders_2(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_765,plain,(
    ! [A_365,B_366,D_367] :
      ( m1_subset_1('#skF_4'(A_365,B_366,D_367,D_367),u1_struct_0(A_365))
      | ~ r3_waybel_9(A_365,B_366,D_367)
      | ~ l1_waybel_0(B_366,A_365)
      | ~ v7_waybel_0(B_366)
      | ~ v4_orders_2(B_366)
      | v2_struct_0(B_366)
      | ~ l1_waybel_9(A_365)
      | ~ v1_compts_1(A_365)
      | ~ v2_lattice3(A_365)
      | ~ v1_lattice3(A_365)
      | ~ v4_orders_2(A_365)
      | ~ v3_orders_2(A_365)
      | ~ v8_pre_topc(A_365)
      | ~ v2_pre_topc(A_365)
      | r2_yellow_0(A_365,k2_relset_1(u1_struct_0(B_366),u1_struct_0(A_365),u1_waybel_0(A_365,B_366)))
      | ~ r1_lattice3(A_365,k2_relset_1(u1_struct_0(B_366),u1_struct_0(A_365),u1_waybel_0(A_365,B_366)),D_367)
      | ~ m1_subset_1(D_367,u1_struct_0(A_365))
      | ~ l1_orders_2(A_365)
      | ~ v5_orders_2(A_365) ) ),
    inference(resolution,[status(thm)],[c_725,c_10])).

tff(c_767,plain,(
    ! [B_47,D_59] :
      ( m1_subset_1('#skF_4'('#skF_9',B_47,D_59,D_59),u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_47),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_47)))
      | ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ r3_waybel_9('#skF_9',B_47,D_59)
      | ~ v11_waybel_0(B_47,'#skF_9')
      | ~ m1_subset_1(D_59,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_47,'#skF_9')
      | ~ v7_waybel_0(B_47)
      | ~ v4_orders_2(B_47)
      | v2_struct_0(B_47) ) ),
    inference(resolution,[status(thm)],[c_255,c_765])).

tff(c_782,plain,(
    ! [B_368,D_369] :
      ( m1_subset_1('#skF_4'('#skF_9',B_368,D_369,D_369),u1_struct_0('#skF_9'))
      | r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_368),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_368)))
      | ~ r3_waybel_9('#skF_9',B_368,D_369)
      | ~ v11_waybel_0(B_368,'#skF_9')
      | ~ m1_subset_1(D_369,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_368,'#skF_9')
      | ~ v7_waybel_0(B_368)
      | ~ v4_orders_2(B_368)
      | v2_struct_0(B_368) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_85,c_80,c_78,c_76,c_74,c_70,c_68,c_66,c_64,c_767])).

tff(c_312,plain,(
    ! [A_244,B_245,D_246,E_247] :
      ( ~ v5_pre_topc(k4_waybel_1(A_244,'#skF_4'(A_244,B_245,D_246,D_246)),A_244,A_244)
      | r1_orders_2(A_244,E_247,D_246)
      | ~ r1_lattice3(A_244,k2_relset_1(u1_struct_0(B_245),u1_struct_0(A_244),u1_waybel_0(A_244,B_245)),E_247)
      | ~ m1_subset_1(E_247,u1_struct_0(A_244))
      | ~ r3_waybel_9(A_244,B_245,D_246)
      | ~ m1_subset_1(D_246,u1_struct_0(A_244))
      | ~ l1_waybel_0(B_245,A_244)
      | ~ v7_waybel_0(B_245)
      | ~ v4_orders_2(B_245)
      | v2_struct_0(B_245)
      | ~ l1_waybel_9(A_244)
      | ~ v1_compts_1(A_244)
      | ~ v2_lattice3(A_244)
      | ~ v1_lattice3(A_244)
      | ~ v5_orders_2(A_244)
      | ~ v4_orders_2(A_244)
      | ~ v3_orders_2(A_244)
      | ~ v8_pre_topc(A_244)
      | ~ v2_pre_topc(A_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_315,plain,(
    ! [E_247,D_246,B_245] :
      ( r1_orders_2('#skF_9',E_247,D_246)
      | ~ r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_245),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_245)),E_247)
      | ~ m1_subset_1(E_247,u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9',B_245,D_246)
      | ~ m1_subset_1(D_246,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_245,'#skF_9')
      | ~ v7_waybel_0(B_245)
      | ~ v4_orders_2(B_245)
      | v2_struct_0(B_245)
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_4'('#skF_9',B_245,D_246,D_246),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_62,c_312])).

tff(c_319,plain,(
    ! [E_248,D_249,B_250] :
      ( r1_orders_2('#skF_9',E_248,D_249)
      | ~ r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_250),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_250)),E_248)
      | ~ m1_subset_1(E_248,u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9',B_250,D_249)
      | ~ m1_subset_1(D_249,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_250,'#skF_9')
      | ~ v7_waybel_0(B_250)
      | ~ v4_orders_2(B_250)
      | v2_struct_0(B_250)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_250,D_249,D_249),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_315])).

tff(c_327,plain,(
    ! [B_250,C_23,D_249] :
      ( r1_orders_2('#skF_9','#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_250),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_250)),C_23),D_249)
      | ~ m1_subset_1('#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_250),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_250)),C_23),u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9',B_250,D_249)
      | ~ m1_subset_1(D_249,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_250,'#skF_9')
      | ~ v7_waybel_0(B_250)
      | ~ v4_orders_2(B_250)
      | v2_struct_0(B_250)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_250,D_249,D_249),u1_struct_0('#skF_9'))
      | r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_250),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_250)))
      | ~ r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_250),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_250)),C_23)
      | ~ m1_subset_1(C_23,u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_12,c_319])).

tff(c_535,plain,(
    ! [B_305,C_306,D_307] :
      ( r1_orders_2('#skF_9','#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)),C_306),D_307)
      | ~ m1_subset_1('#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)),C_306),u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9',B_305,D_307)
      | ~ m1_subset_1(D_307,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_305,'#skF_9')
      | ~ v7_waybel_0(B_305)
      | ~ v4_orders_2(B_305)
      | v2_struct_0(B_305)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_305,D_307,D_307),u1_struct_0('#skF_9'))
      | r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)))
      | ~ r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)),C_306)
      | ~ m1_subset_1(C_306,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_85,c_327])).

tff(c_538,plain,(
    ! [B_305,C_23,D_307] :
      ( r1_orders_2('#skF_9','#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)),C_23),D_307)
      | ~ r3_waybel_9('#skF_9',B_305,D_307)
      | ~ m1_subset_1(D_307,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_305,'#skF_9')
      | ~ v7_waybel_0(B_305)
      | ~ v4_orders_2(B_305)
      | v2_struct_0(B_305)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_305,D_307,D_307),u1_struct_0('#skF_9'))
      | r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)))
      | ~ r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)),C_23)
      | ~ m1_subset_1(C_23,u1_struct_0('#skF_9'))
      | ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_14,c_535])).

tff(c_541,plain,(
    ! [B_305,C_23,D_307] :
      ( r1_orders_2('#skF_9','#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)),C_23),D_307)
      | ~ r3_waybel_9('#skF_9',B_305,D_307)
      | ~ m1_subset_1(D_307,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_305,'#skF_9')
      | ~ v7_waybel_0(B_305)
      | ~ v4_orders_2(B_305)
      | v2_struct_0(B_305)
      | ~ m1_subset_1('#skF_4'('#skF_9',B_305,D_307,D_307),u1_struct_0('#skF_9'))
      | r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)))
      | ~ r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_305),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_305)),C_23)
      | ~ m1_subset_1(C_23,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_85,c_538])).

tff(c_876,plain,(
    ! [B_384,C_385,D_386] :
      ( r1_orders_2('#skF_9','#skF_1'('#skF_9',k2_relset_1(u1_struct_0(B_384),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_384)),C_385),D_386)
      | ~ r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_384),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_384)),C_385)
      | ~ m1_subset_1(C_385,u1_struct_0('#skF_9'))
      | r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_384),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_384)))
      | ~ r3_waybel_9('#skF_9',B_384,D_386)
      | ~ v11_waybel_0(B_384,'#skF_9')
      | ~ m1_subset_1(D_386,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_384,'#skF_9')
      | ~ v7_waybel_0(B_384)
      | ~ v4_orders_2(B_384)
      | v2_struct_0(B_384) ) ),
    inference(resolution,[status(thm)],[c_782,c_541])).

tff(c_880,plain,(
    ! [B_384,D_386] :
      ( ~ l1_orders_2('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_384),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_384)),D_386)
      | r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_384),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_384)))
      | ~ r3_waybel_9('#skF_9',B_384,D_386)
      | ~ v11_waybel_0(B_384,'#skF_9')
      | ~ m1_subset_1(D_386,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_384,'#skF_9')
      | ~ v7_waybel_0(B_384)
      | ~ v4_orders_2(B_384)
      | v2_struct_0(B_384) ) ),
    inference(resolution,[status(thm)],[c_876,c_10])).

tff(c_884,plain,(
    ! [B_387,D_388] :
      ( ~ r1_lattice3('#skF_9',k2_relset_1(u1_struct_0(B_387),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_387)),D_388)
      | r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_387),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_387)))
      | ~ r3_waybel_9('#skF_9',B_387,D_388)
      | ~ v11_waybel_0(B_387,'#skF_9')
      | ~ m1_subset_1(D_388,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_387,'#skF_9')
      | ~ v7_waybel_0(B_387)
      | ~ v4_orders_2(B_387)
      | v2_struct_0(B_387) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_85,c_880])).

tff(c_910,plain,(
    ! [B_389,D_390] :
      ( r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_389),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_389)))
      | ~ r3_waybel_9('#skF_9',B_389,D_390)
      | ~ v11_waybel_0(B_389,'#skF_9')
      | ~ m1_subset_1(D_390,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_389,'#skF_9')
      | ~ v7_waybel_0(B_389)
      | ~ v4_orders_2(B_389)
      | v2_struct_0(B_389) ) ),
    inference(resolution,[status(thm)],[c_255,c_884])).

tff(c_919,plain,(
    ! [B_111] :
      ( r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_111),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_111)))
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_910])).

tff(c_930,plain,(
    ! [B_111] :
      ( r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_111),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_111)))
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_919])).

tff(c_932,plain,(
    ! [B_391] :
      ( r2_yellow_0('#skF_9',k2_relset_1(u1_struct_0(B_391),u1_struct_0('#skF_9'),u1_waybel_0('#skF_9',B_391)))
      | ~ v11_waybel_0(B_391,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_391),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_391,'#skF_9')
      | ~ v7_waybel_0(B_391)
      | ~ v4_orders_2(B_391)
      | v2_struct_0(B_391) ) ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_930])).

tff(c_16,plain,(
    ! [A_27,B_29] :
      ( r2_waybel_9(A_27,B_29)
      | ~ r2_yellow_0(A_27,k2_relset_1(u1_struct_0(B_29),u1_struct_0(A_27),u1_waybel_0(A_27,B_29)))
      | ~ l1_waybel_0(B_29,A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_935,plain,(
    ! [B_391] :
      ( r2_waybel_9('#skF_9',B_391)
      | ~ l1_orders_2('#skF_9')
      | ~ v11_waybel_0(B_391,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_391),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_391,'#skF_9')
      | ~ v7_waybel_0(B_391)
      | ~ v4_orders_2(B_391)
      | v2_struct_0(B_391) ) ),
    inference(resolution,[status(thm)],[c_932,c_16])).

tff(c_939,plain,(
    ! [B_392] :
      ( r2_waybel_9('#skF_9',B_392)
      | ~ v11_waybel_0(B_392,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_392),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_392,'#skF_9')
      | ~ v7_waybel_0(B_392)
      | ~ v4_orders_2(B_392)
      | v2_struct_0(B_392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_935])).

tff(c_943,plain,(
    ! [B_111] :
      ( r2_waybel_9('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_939])).

tff(c_946,plain,(
    ! [B_111] :
      ( r2_waybel_9('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_943])).

tff(c_948,plain,(
    ! [B_393] :
      ( r2_waybel_9('#skF_9',B_393)
      | ~ v11_waybel_0(B_393,'#skF_9')
      | ~ l1_waybel_0(B_393,'#skF_9')
      | ~ v7_waybel_0(B_393)
      | ~ v4_orders_2(B_393)
      | v2_struct_0(B_393) ) ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_946])).

tff(c_951,plain,
    ( r2_waybel_9('#skF_9','#skF_10')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_52,c_948])).

tff(c_954,plain,
    ( r2_waybel_9('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_951])).

tff(c_956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_92,c_954])).

tff(c_957,plain,(
    ~ r2_hidden(k1_waybel_9('#skF_9','#skF_10'),k10_yellow_6('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_982,plain,
    ( '#skF_6'('#skF_9','#skF_10') != '#skF_7'('#skF_9','#skF_10')
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_9('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_979,c_957])).

tff(c_985,plain,
    ( '#skF_6'('#skF_9','#skF_10') != '#skF_7'('#skF_9','#skF_10')
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_9('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_58,c_56,c_54,c_982])).

tff(c_986,plain,
    ( '#skF_6'('#skF_9','#skF_10') != '#skF_7'('#skF_9','#skF_10')
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_9('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_985])).

tff(c_987,plain,(
    ~ m1_subset_1(k1_waybel_9('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_986])).

tff(c_1090,plain,(
    ~ m1_subset_1('#skF_5'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1087,c_987])).

tff(c_1098,plain,
    ( ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_34,c_1090])).

tff(c_1101,plain,
    ( v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_58,c_56,c_54,c_1098])).

tff(c_1103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1070,c_60,c_1101])).

tff(c_1104,plain,
    ( ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | '#skF_6'('#skF_9','#skF_10') != '#skF_7'('#skF_9','#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_986])).

tff(c_1106,plain,(
    '#skF_6'('#skF_9','#skF_10') != '#skF_7'('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1104])).

tff(c_1105,plain,(
    m1_subset_1(k1_waybel_9('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_986])).

tff(c_1146,plain,(
    ! [A_470,B_471,C_472] :
      ( ~ v5_pre_topc(k4_waybel_1(A_470,'#skF_8'(A_470,B_471,C_472)),A_470,A_470)
      | k1_waybel_9(A_470,C_472) = B_471
      | ~ r3_waybel_9(A_470,C_472,B_471)
      | ~ v11_waybel_0(C_472,A_470)
      | ~ l1_waybel_0(C_472,A_470)
      | ~ v7_waybel_0(C_472)
      | ~ v4_orders_2(C_472)
      | v2_struct_0(C_472)
      | ~ m1_subset_1(B_471,u1_struct_0(A_470))
      | ~ l1_waybel_9(A_470)
      | ~ v1_compts_1(A_470)
      | ~ v2_lattice3(A_470)
      | ~ v1_lattice3(A_470)
      | ~ v5_orders_2(A_470)
      | ~ v4_orders_2(A_470)
      | ~ v3_orders_2(A_470)
      | ~ v8_pre_topc(A_470)
      | ~ v2_pre_topc(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_1150,plain,(
    ! [C_472,B_471] :
      ( k1_waybel_9('#skF_9',C_472) = B_471
      | ~ r3_waybel_9('#skF_9',C_472,B_471)
      | ~ v11_waybel_0(C_472,'#skF_9')
      | ~ l1_waybel_0(C_472,'#skF_9')
      | ~ v7_waybel_0(C_472)
      | ~ v4_orders_2(C_472)
      | v2_struct_0(C_472)
      | ~ m1_subset_1(B_471,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_8'('#skF_9',B_471,C_472),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_62,c_1146])).

tff(c_1154,plain,(
    ! [C_473,B_474] :
      ( k1_waybel_9('#skF_9',C_473) = B_474
      | ~ r3_waybel_9('#skF_9',C_473,B_474)
      | ~ v11_waybel_0(C_473,'#skF_9')
      | ~ l1_waybel_0(C_473,'#skF_9')
      | ~ v7_waybel_0(C_473)
      | ~ v4_orders_2(C_473)
      | v2_struct_0(C_473)
      | ~ m1_subset_1(B_474,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_8'('#skF_9',B_474,C_473),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_1150])).

tff(c_1158,plain,(
    ! [C_142,B_138] :
      ( k1_waybel_9('#skF_9',C_142) = B_138
      | ~ r3_waybel_9('#skF_9',C_142,B_138)
      | ~ v11_waybel_0(C_142,'#skF_9')
      | ~ l1_waybel_0(C_142,'#skF_9')
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_1154])).

tff(c_1162,plain,(
    ! [C_475,B_476] :
      ( k1_waybel_9('#skF_9',C_475) = B_476
      | ~ r3_waybel_9('#skF_9',C_475,B_476)
      | ~ v11_waybel_0(C_475,'#skF_9')
      | ~ l1_waybel_0(C_475,'#skF_9')
      | ~ v7_waybel_0(C_475)
      | ~ v4_orders_2(C_475)
      | v2_struct_0(C_475)
      | ~ m1_subset_1(B_476,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_1158])).

tff(c_1171,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_1162])).

tff(c_1180,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_1171])).

tff(c_1181,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1180])).

tff(c_1184,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_1181,c_2])).

tff(c_1188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_1184])).

tff(c_1190,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1180])).

tff(c_1193,plain,(
    ! [B_480] :
      ( k1_waybel_9('#skF_9',B_480) = '#skF_5'('#skF_9',B_480)
      | ~ v11_waybel_0(B_480,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_480),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_480,'#skF_9')
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480) ) ),
    inference(splitRight,[status(thm)],[c_1180])).

tff(c_1197,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_1193])).

tff(c_1200,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_1197])).

tff(c_1202,plain,(
    ! [B_481] :
      ( k1_waybel_9('#skF_9',B_481) = '#skF_5'('#skF_9',B_481)
      | ~ v11_waybel_0(B_481,'#skF_9')
      | ~ l1_waybel_0(B_481,'#skF_9')
      | ~ v7_waybel_0(B_481)
      | ~ v4_orders_2(B_481)
      | v2_struct_0(B_481) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1190,c_1200])).

tff(c_1205,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_52,c_1202])).

tff(c_1208,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1205])).

tff(c_1209,plain,(
    k1_waybel_9('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1208])).

tff(c_1107,plain,(
    ! [A_452,B_453,C_454] :
      ( m1_subset_1('#skF_6'(A_452,B_453),u1_struct_0(A_452))
      | r2_hidden(C_454,k10_yellow_6(A_452,B_453))
      | ~ r3_waybel_9(A_452,B_453,C_454)
      | ~ m1_subset_1(C_454,u1_struct_0(A_452))
      | ~ l1_waybel_0(B_453,A_452)
      | ~ v7_waybel_0(B_453)
      | ~ v4_orders_2(B_453)
      | v2_struct_0(B_453)
      | ~ l1_pre_topc(A_452)
      | ~ v1_compts_1(A_452)
      | ~ v8_pre_topc(A_452)
      | ~ v2_pre_topc(A_452)
      | v2_struct_0(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1110,plain,
    ( m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_9('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1107,c_957])).

tff(c_1113,plain,
    ( m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_58,c_56,c_54,c_1105,c_1110])).

tff(c_1114,plain,
    ( m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | v2_struct_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1113])).

tff(c_1115,plain,(
    ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1114])).

tff(c_1210,plain,(
    ~ r3_waybel_9('#skF_9','#skF_10','#skF_5'('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1209,c_1115])).

tff(c_1254,plain,
    ( ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_1210])).

tff(c_1257,plain,
    ( v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_58,c_56,c_54,c_1254])).

tff(c_1259,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1190,c_60,c_1257])).

tff(c_1261,plain,(
    r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_1263,plain,(
    ! [A_482,B_483,C_484] :
      ( r3_waybel_9(A_482,B_483,'#skF_7'(A_482,B_483))
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
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1266,plain,
    ( r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9','#skF_10'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_9('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1263,c_957])).

tff(c_1269,plain,
    ( r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9','#skF_10'))
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_58,c_56,c_54,c_1105,c_1261,c_1266])).

tff(c_1270,plain,
    ( r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9','#skF_10'))
    | v2_struct_0('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1269])).

tff(c_1271,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1270])).

tff(c_1274,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_1271,c_2])).

tff(c_1278,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_1274])).

tff(c_1280,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1270])).

tff(c_1281,plain,(
    ! [A_485,B_486,C_487] :
      ( m1_subset_1('#skF_7'(A_485,B_486),u1_struct_0(A_485))
      | r2_hidden(C_487,k10_yellow_6(A_485,B_486))
      | ~ r3_waybel_9(A_485,B_486,C_487)
      | ~ m1_subset_1(C_487,u1_struct_0(A_485))
      | ~ l1_waybel_0(B_486,A_485)
      | ~ v7_waybel_0(B_486)
      | ~ v4_orders_2(B_486)
      | v2_struct_0(B_486)
      | ~ l1_pre_topc(A_485)
      | ~ v1_compts_1(A_485)
      | ~ v8_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1284,plain,
    ( m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_9('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1281,c_957])).

tff(c_1287,plain,
    ( m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_58,c_56,c_54,c_1105,c_1261,c_1284])).

tff(c_1288,plain,(
    m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_1280,c_60,c_1287])).

tff(c_1279,plain,(
    r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_1270])).

tff(c_1303,plain,(
    ! [A_497,B_498,C_499] :
      ( ~ v5_pre_topc(k4_waybel_1(A_497,'#skF_8'(A_497,B_498,C_499)),A_497,A_497)
      | k1_waybel_9(A_497,C_499) = B_498
      | ~ r3_waybel_9(A_497,C_499,B_498)
      | ~ v11_waybel_0(C_499,A_497)
      | ~ l1_waybel_0(C_499,A_497)
      | ~ v7_waybel_0(C_499)
      | ~ v4_orders_2(C_499)
      | v2_struct_0(C_499)
      | ~ m1_subset_1(B_498,u1_struct_0(A_497))
      | ~ l1_waybel_9(A_497)
      | ~ v1_compts_1(A_497)
      | ~ v2_lattice3(A_497)
      | ~ v1_lattice3(A_497)
      | ~ v5_orders_2(A_497)
      | ~ v4_orders_2(A_497)
      | ~ v3_orders_2(A_497)
      | ~ v8_pre_topc(A_497)
      | ~ v2_pre_topc(A_497) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_1307,plain,(
    ! [C_499,B_498] :
      ( k1_waybel_9('#skF_9',C_499) = B_498
      | ~ r3_waybel_9('#skF_9',C_499,B_498)
      | ~ v11_waybel_0(C_499,'#skF_9')
      | ~ l1_waybel_0(C_499,'#skF_9')
      | ~ v7_waybel_0(C_499)
      | ~ v4_orders_2(C_499)
      | v2_struct_0(C_499)
      | ~ m1_subset_1(B_498,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_8'('#skF_9',B_498,C_499),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_62,c_1303])).

tff(c_1311,plain,(
    ! [C_500,B_501] :
      ( k1_waybel_9('#skF_9',C_500) = B_501
      | ~ r3_waybel_9('#skF_9',C_500,B_501)
      | ~ v11_waybel_0(C_500,'#skF_9')
      | ~ l1_waybel_0(C_500,'#skF_9')
      | ~ v7_waybel_0(C_500)
      | ~ v4_orders_2(C_500)
      | v2_struct_0(C_500)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_8'('#skF_9',B_501,C_500),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_1307])).

tff(c_1315,plain,(
    ! [C_142,B_138] :
      ( k1_waybel_9('#skF_9',C_142) = B_138
      | ~ r3_waybel_9('#skF_9',C_142,B_138)
      | ~ v11_waybel_0(C_142,'#skF_9')
      | ~ l1_waybel_0(C_142,'#skF_9')
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_1311])).

tff(c_1319,plain,(
    ! [C_502,B_503] :
      ( k1_waybel_9('#skF_9',C_502) = B_503
      | ~ r3_waybel_9('#skF_9',C_502,B_503)
      | ~ v11_waybel_0(C_502,'#skF_9')
      | ~ l1_waybel_0(C_502,'#skF_9')
      | ~ v7_waybel_0(C_502)
      | ~ v4_orders_2(C_502)
      | v2_struct_0(C_502)
      | ~ m1_subset_1(B_503,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_1315])).

tff(c_1326,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_7'('#skF_9','#skF_10')
    | ~ v11_waybel_0('#skF_10','#skF_9')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_1279,c_1319])).

tff(c_1345,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_7'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_58,c_56,c_54,c_52,c_1326])).

tff(c_1346,plain,(
    k1_waybel_9('#skF_9','#skF_10') = '#skF_7'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1345])).

tff(c_1260,plain,
    ( v2_struct_0('#skF_9')
    | m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1114])).

tff(c_1262,plain,(
    m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1260])).

tff(c_1289,plain,(
    ! [A_488,B_489,C_490] :
      ( r3_waybel_9(A_488,B_489,'#skF_6'(A_488,B_489))
      | r2_hidden(C_490,k10_yellow_6(A_488,B_489))
      | ~ r3_waybel_9(A_488,B_489,C_490)
      | ~ m1_subset_1(C_490,u1_struct_0(A_488))
      | ~ l1_waybel_0(B_489,A_488)
      | ~ v7_waybel_0(B_489)
      | ~ v4_orders_2(B_489)
      | v2_struct_0(B_489)
      | ~ l1_pre_topc(A_488)
      | ~ v1_compts_1(A_488)
      | ~ v8_pre_topc(A_488)
      | ~ v2_pre_topc(A_488)
      | v2_struct_0(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1292,plain,
    ( r3_waybel_9('#skF_9','#skF_10','#skF_6'('#skF_9','#skF_10'))
    | ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | ~ m1_subset_1(k1_waybel_9('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_1289,c_957])).

tff(c_1295,plain,
    ( r3_waybel_9('#skF_9','#skF_10','#skF_6'('#skF_9','#skF_10'))
    | v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_58,c_56,c_54,c_1105,c_1261,c_1292])).

tff(c_1296,plain,(
    r3_waybel_9('#skF_9','#skF_10','#skF_6'('#skF_9','#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_1280,c_60,c_1295])).

tff(c_1321,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_6'('#skF_9','#skF_10')
    | ~ v11_waybel_0('#skF_10','#skF_9')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ m1_subset_1('#skF_6'('#skF_9','#skF_10'),u1_struct_0('#skF_9')) ),
    inference(resolution,[status(thm)],[c_1296,c_1319])).

tff(c_1337,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_6'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1262,c_58,c_56,c_54,c_52,c_1321])).

tff(c_1338,plain,(
    k1_waybel_9('#skF_9','#skF_10') = '#skF_6'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1337])).

tff(c_1369,plain,(
    '#skF_6'('#skF_9','#skF_10') = '#skF_7'('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1346,c_1338])).

tff(c_1370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1106,c_1369])).

tff(c_1371,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1260])).

tff(c_1375,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_1371,c_2])).

tff(c_1379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_1375])).

tff(c_1381,plain,(
    '#skF_6'('#skF_9','#skF_10') = '#skF_7'('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_1104])).

tff(c_1403,plain,(
    ! [A_510,B_511,C_512] :
      ( m1_subset_1('#skF_6'(A_510,B_511),u1_struct_0(A_510))
      | r2_hidden(C_512,k10_yellow_6(A_510,B_511))
      | ~ r3_waybel_9(A_510,B_511,C_512)
      | ~ m1_subset_1(C_512,u1_struct_0(A_510))
      | ~ l1_waybel_0(B_511,A_510)
      | ~ v7_waybel_0(B_511)
      | ~ v4_orders_2(B_511)
      | v2_struct_0(B_511)
      | ~ l1_pre_topc(A_510)
      | ~ v1_compts_1(A_510)
      | ~ v8_pre_topc(A_510)
      | ~ v2_pre_topc(A_510)
      | v2_struct_0(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_1409,plain,(
    ! [C_512] :
      ( m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
      | r2_hidden(C_512,k10_yellow_6('#skF_9','#skF_10'))
      | ~ r3_waybel_9('#skF_9','#skF_10',C_512)
      | ~ m1_subset_1(C_512,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0('#skF_10','#skF_9')
      | ~ v7_waybel_0('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1381,c_1403])).

tff(c_1415,plain,(
    ! [C_512] :
      ( m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
      | r2_hidden(C_512,k10_yellow_6('#skF_9','#skF_10'))
      | ~ r3_waybel_9('#skF_9','#skF_10',C_512)
      | ~ m1_subset_1(C_512,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_10')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_58,c_56,c_54,c_1409])).

tff(c_1416,plain,(
    ! [C_512] :
      ( m1_subset_1('#skF_7'('#skF_9','#skF_10'),u1_struct_0('#skF_9'))
      | r2_hidden(C_512,k10_yellow_6('#skF_9','#skF_10'))
      | ~ r3_waybel_9('#skF_9','#skF_10',C_512)
      | ~ m1_subset_1(C_512,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1415])).

tff(c_1417,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1416])).

tff(c_1420,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_1417,c_2])).

tff(c_1424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_1420])).

tff(c_1426,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1416])).

tff(c_1521,plain,(
    ! [A_536,B_537,C_538] :
      ( ~ v5_pre_topc(k4_waybel_1(A_536,'#skF_8'(A_536,B_537,C_538)),A_536,A_536)
      | k1_waybel_9(A_536,C_538) = B_537
      | ~ r3_waybel_9(A_536,C_538,B_537)
      | ~ v11_waybel_0(C_538,A_536)
      | ~ l1_waybel_0(C_538,A_536)
      | ~ v7_waybel_0(C_538)
      | ~ v4_orders_2(C_538)
      | v2_struct_0(C_538)
      | ~ m1_subset_1(B_537,u1_struct_0(A_536))
      | ~ l1_waybel_9(A_536)
      | ~ v1_compts_1(A_536)
      | ~ v2_lattice3(A_536)
      | ~ v1_lattice3(A_536)
      | ~ v5_orders_2(A_536)
      | ~ v4_orders_2(A_536)
      | ~ v3_orders_2(A_536)
      | ~ v8_pre_topc(A_536)
      | ~ v2_pre_topc(A_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_1525,plain,(
    ! [C_538,B_537] :
      ( k1_waybel_9('#skF_9',C_538) = B_537
      | ~ r3_waybel_9('#skF_9',C_538,B_537)
      | ~ v11_waybel_0(C_538,'#skF_9')
      | ~ l1_waybel_0(C_538,'#skF_9')
      | ~ v7_waybel_0(C_538)
      | ~ v4_orders_2(C_538)
      | v2_struct_0(C_538)
      | ~ m1_subset_1(B_537,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | ~ m1_subset_1('#skF_8'('#skF_9',B_537,C_538),u1_struct_0('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_62,c_1521])).

tff(c_1529,plain,(
    ! [C_539,B_540] :
      ( k1_waybel_9('#skF_9',C_539) = B_540
      | ~ r3_waybel_9('#skF_9',C_539,B_540)
      | ~ v11_waybel_0(C_539,'#skF_9')
      | ~ l1_waybel_0(C_539,'#skF_9')
      | ~ v7_waybel_0(C_539)
      | ~ v4_orders_2(C_539)
      | v2_struct_0(C_539)
      | ~ m1_subset_1(B_540,u1_struct_0('#skF_9'))
      | ~ m1_subset_1('#skF_8'('#skF_9',B_540,C_539),u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_1525])).

tff(c_1533,plain,(
    ! [C_142,B_138] :
      ( k1_waybel_9('#skF_9',C_142) = B_138
      | ~ r3_waybel_9('#skF_9',C_142,B_138)
      | ~ v11_waybel_0(C_142,'#skF_9')
      | ~ l1_waybel_0(C_142,'#skF_9')
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_9'))
      | ~ l1_waybel_9('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v2_lattice3('#skF_9')
      | ~ v1_lattice3('#skF_9')
      | ~ v5_orders_2('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | ~ v3_orders_2('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_48,c_1529])).

tff(c_1537,plain,(
    ! [C_541,B_542] :
      ( k1_waybel_9('#skF_9',C_541) = B_542
      | ~ r3_waybel_9('#skF_9',C_541,B_542)
      | ~ v11_waybel_0(C_541,'#skF_9')
      | ~ l1_waybel_0(C_541,'#skF_9')
      | ~ v7_waybel_0(C_541)
      | ~ v4_orders_2(C_541)
      | v2_struct_0(C_541)
      | ~ m1_subset_1(B_542,u1_struct_0('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_68,c_66,c_64,c_1533])).

tff(c_1546,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_32,c_1537])).

tff(c_1557,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_111),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_1546])).

tff(c_1559,plain,(
    ! [B_543] :
      ( k1_waybel_9('#skF_9',B_543) = '#skF_5'('#skF_9',B_543)
      | ~ v11_waybel_0(B_543,'#skF_9')
      | ~ m1_subset_1('#skF_5'('#skF_9',B_543),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_543,'#skF_9')
      | ~ v7_waybel_0(B_543)
      | ~ v4_orders_2(B_543)
      | v2_struct_0(B_543) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1426,c_1557])).

tff(c_1563,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_9')
      | ~ v1_compts_1('#skF_9')
      | ~ v8_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_34,c_1559])).

tff(c_1566,plain,(
    ! [B_111] :
      ( k1_waybel_9('#skF_9',B_111) = '#skF_5'('#skF_9',B_111)
      | ~ v11_waybel_0(B_111,'#skF_9')
      | ~ l1_waybel_0(B_111,'#skF_9')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_1563])).

tff(c_1568,plain,(
    ! [B_544] :
      ( k1_waybel_9('#skF_9',B_544) = '#skF_5'('#skF_9',B_544)
      | ~ v11_waybel_0(B_544,'#skF_9')
      | ~ l1_waybel_0(B_544,'#skF_9')
      | ~ v7_waybel_0(B_544)
      | ~ v4_orders_2(B_544)
      | v2_struct_0(B_544) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1426,c_1566])).

tff(c_1571,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_52,c_1568])).

tff(c_1574,plain,
    ( k1_waybel_9('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10')
    | v2_struct_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_54,c_1571])).

tff(c_1575,plain,(
    k1_waybel_9('#skF_9','#skF_10') = '#skF_5'('#skF_9','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1574])).

tff(c_1380,plain,
    ( ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10'))
    | v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1104])).

tff(c_1386,plain,(
    ~ r3_waybel_9('#skF_9','#skF_10',k1_waybel_9('#skF_9','#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_1380])).

tff(c_1576,plain,(
    ~ r3_waybel_9('#skF_9','#skF_10','#skF_5'('#skF_9','#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1575,c_1386])).

tff(c_1585,plain,
    ( ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ l1_pre_topc('#skF_9')
    | ~ v1_compts_1('#skF_9')
    | ~ v8_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_32,c_1576])).

tff(c_1588,plain,
    ( v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_66,c_90,c_58,c_56,c_54,c_1585])).

tff(c_1590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1426,c_60,c_1588])).

tff(c_1591,plain,(
    v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1380])).

tff(c_1603,plain,
    ( ~ v1_lattice3('#skF_9')
    | ~ l1_orders_2('#skF_9') ),
    inference(resolution,[status(thm)],[c_1591,c_2])).

tff(c_1607,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_70,c_1603])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.96/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/1.95  
% 5.32/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.32/1.95  %$ v5_pre_topc > r3_waybel_9 > r1_orders_2 > r1_lattice3 > v11_waybel_0 > r2_yellow_0 > r2_waybel_9 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_compts_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_waybel_1 > k1_waybel_9 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_6 > #skF_1 > #skF_10 > #skF_9 > #skF_4 > #skF_2 > #skF_3 > #skF_8 > #skF_7 > #skF_5
% 5.32/1.95  
% 5.32/1.95  %Foreground sorts:
% 5.32/1.95  
% 5.32/1.95  
% 5.32/1.95  %Background operators:
% 5.32/1.95  
% 5.32/1.95  
% 5.32/1.95  %Foreground operators:
% 5.32/1.95  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.32/1.95  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.32/1.95  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 5.32/1.95  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.32/1.95  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.32/1.95  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.32/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.32/1.95  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.32/1.95  tff(r2_waybel_9, type, r2_waybel_9: ($i * $i) > $o).
% 5.32/1.95  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.32/1.95  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 5.32/1.95  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.32/1.95  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.32/1.95  tff('#skF_10', type, '#skF_10': $i).
% 5.32/1.95  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 5.32/1.95  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 5.32/1.95  tff(v11_waybel_0, type, v11_waybel_0: ($i * $i) > $o).
% 5.32/1.95  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 5.32/1.95  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 5.32/1.95  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.32/1.95  tff('#skF_9', type, '#skF_9': $i).
% 5.32/1.95  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.32/1.95  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.32/1.95  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.32/1.95  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 5.32/1.95  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 5.32/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.32/1.95  tff(k1_waybel_9, type, k1_waybel_9: ($i * $i) > $i).
% 5.32/1.95  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.32/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.32/1.95  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.32/1.95  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.32/1.95  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.32/1.95  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 5.32/1.95  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.32/1.95  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 5.32/1.95  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.32/1.95  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.32/1.95  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 5.32/1.95  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.32/1.95  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 5.32/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.32/1.95  
% 5.56/1.99  tff(f_311, negated_conjecture, ~(![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => ((![B]: (m1_subset_1(B, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, B), A, A))) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v11_waybel_0(B, A) => (r2_waybel_9(A, B) & r2_hidden(k1_waybel_9(A, B), k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_waybel_9)).
% 5.56/1.99  tff(f_66, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 5.56/1.99  tff(f_189, axiom, (![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_waybel_9)).
% 5.56/1.99  tff(f_271, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => ((((![D]: (m1_subset_1(D, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, D), A, A))) & v11_waybel_0(C, A)) & r3_waybel_9(A, C, B)) => (B = k1_waybel_9(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_waybel_9)).
% 5.56/1.99  tff(f_32, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 5.56/1.99  tff(f_229, axiom, (![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r3_waybel_9(A, B, C) & r3_waybel_9(A, B, D)) => (C = D)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) => r2_hidden(C, k10_yellow_6(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_waybel_9)).
% 5.56/1.99  tff(f_113, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & v11_waybel_0(B, A)) & r3_waybel_9(A, B, C)) => r1_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_waybel_9)).
% 5.56/1.99  tff(f_51, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (r2_yellow_0(A, B) <=> (?[C]: ((m1_subset_1(C, u1_struct_0(A)) & r1_lattice3(A, B, C)) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, B, D) => r1_orders_2(A, D, C)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_yellow_0)).
% 5.56/1.99  tff(f_163, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & r3_waybel_9(A, B, C)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r1_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), E) => r1_orders_2(A, E, D))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l52_waybel_9)).
% 5.56/1.99  tff(f_60, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_waybel_0(B, A) => (r2_waybel_9(A, B) <=> r2_yellow_0(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_waybel_9)).
% 5.56/1.99  tff(c_64, plain, (l1_waybel_9('#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_81, plain, (![A_147]: (l1_orders_2(A_147) | ~l1_waybel_9(A_147))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.56/1.99  tff(c_85, plain, (l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_64, c_81])).
% 5.56/1.99  tff(c_70, plain, (v1_lattice3('#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_60, plain, (~v2_struct_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_80, plain, (v2_pre_topc('#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_78, plain, (v8_pre_topc('#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_66, plain, (v1_compts_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_86, plain, (![A_148]: (l1_pre_topc(A_148) | ~l1_waybel_9(A_148))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.56/1.99  tff(c_90, plain, (l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_64, c_86])).
% 5.56/1.99  tff(c_58, plain, (v4_orders_2('#skF_10')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_56, plain, (v7_waybel_0('#skF_10')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_54, plain, (l1_waybel_0('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_32, plain, (![A_107, B_111]: (r3_waybel_9(A_107, B_111, '#skF_5'(A_107, B_111)) | ~l1_waybel_0(B_111, A_107) | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_107) | ~v1_compts_1(A_107) | ~v8_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.56/1.99  tff(c_76, plain, (v3_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_74, plain, (v4_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_72, plain, (v5_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_68, plain, (v2_lattice3('#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_48, plain, (![A_130, B_138, C_142]: (m1_subset_1('#skF_8'(A_130, B_138, C_142), u1_struct_0(A_130)) | k1_waybel_9(A_130, C_142)=B_138 | ~r3_waybel_9(A_130, C_142, B_138) | ~v11_waybel_0(C_142, A_130) | ~l1_waybel_0(C_142, A_130) | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0(A_130)) | ~l1_waybel_9(A_130) | ~v1_compts_1(A_130) | ~v2_lattice3(A_130) | ~v1_lattice3(A_130) | ~v5_orders_2(A_130) | ~v4_orders_2(A_130) | ~v3_orders_2(A_130) | ~v8_pre_topc(A_130) | ~v2_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_271])).
% 5.56/1.99  tff(c_62, plain, (![B_146]: (v5_pre_topc(k4_waybel_1('#skF_9', B_146), '#skF_9', '#skF_9') | ~m1_subset_1(B_146, u1_struct_0('#skF_9')))), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_1026, plain, (![A_440, B_441, C_442]: (~v5_pre_topc(k4_waybel_1(A_440, '#skF_8'(A_440, B_441, C_442)), A_440, A_440) | k1_waybel_9(A_440, C_442)=B_441 | ~r3_waybel_9(A_440, C_442, B_441) | ~v11_waybel_0(C_442, A_440) | ~l1_waybel_0(C_442, A_440) | ~v7_waybel_0(C_442) | ~v4_orders_2(C_442) | v2_struct_0(C_442) | ~m1_subset_1(B_441, u1_struct_0(A_440)) | ~l1_waybel_9(A_440) | ~v1_compts_1(A_440) | ~v2_lattice3(A_440) | ~v1_lattice3(A_440) | ~v5_orders_2(A_440) | ~v4_orders_2(A_440) | ~v3_orders_2(A_440) | ~v8_pre_topc(A_440) | ~v2_pre_topc(A_440))), inference(cnfTransformation, [status(thm)], [f_271])).
% 5.56/1.99  tff(c_1030, plain, (![C_442, B_441]: (k1_waybel_9('#skF_9', C_442)=B_441 | ~r3_waybel_9('#skF_9', C_442, B_441) | ~v11_waybel_0(C_442, '#skF_9') | ~l1_waybel_0(C_442, '#skF_9') | ~v7_waybel_0(C_442) | ~v4_orders_2(C_442) | v2_struct_0(C_442) | ~m1_subset_1(B_441, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_8'('#skF_9', B_441, C_442), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_62, c_1026])).
% 5.56/1.99  tff(c_1034, plain, (![C_443, B_444]: (k1_waybel_9('#skF_9', C_443)=B_444 | ~r3_waybel_9('#skF_9', C_443, B_444) | ~v11_waybel_0(C_443, '#skF_9') | ~l1_waybel_0(C_443, '#skF_9') | ~v7_waybel_0(C_443) | ~v4_orders_2(C_443) | v2_struct_0(C_443) | ~m1_subset_1(B_444, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_8'('#skF_9', B_444, C_443), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_1030])).
% 5.56/1.99  tff(c_1038, plain, (![C_142, B_138]: (k1_waybel_9('#skF_9', C_142)=B_138 | ~r3_waybel_9('#skF_9', C_142, B_138) | ~v11_waybel_0(C_142, '#skF_9') | ~l1_waybel_0(C_142, '#skF_9') | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_1034])).
% 5.56/1.99  tff(c_1042, plain, (![C_445, B_446]: (k1_waybel_9('#skF_9', C_445)=B_446 | ~r3_waybel_9('#skF_9', C_445, B_446) | ~v11_waybel_0(C_445, '#skF_9') | ~l1_waybel_0(C_445, '#skF_9') | ~v7_waybel_0(C_445) | ~v4_orders_2(C_445) | v2_struct_0(C_445) | ~m1_subset_1(B_446, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_1038])).
% 5.56/1.99  tff(c_1051, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_1042])).
% 5.56/1.99  tff(c_1060, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_1051])).
% 5.56/1.99  tff(c_1061, plain, (v2_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1060])).
% 5.56/1.99  tff(c_2, plain, (![A_1]: (~v2_struct_0(A_1) | ~v1_lattice3(A_1) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.56/1.99  tff(c_1064, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_1061, c_2])).
% 5.56/1.99  tff(c_1068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_70, c_1064])).
% 5.56/1.99  tff(c_1070, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1060])).
% 5.56/1.99  tff(c_34, plain, (![A_107, B_111]: (m1_subset_1('#skF_5'(A_107, B_111), u1_struct_0(A_107)) | ~l1_waybel_0(B_111, A_107) | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_107) | ~v1_compts_1(A_107) | ~v8_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_189])).
% 5.56/1.99  tff(c_52, plain, (v11_waybel_0('#skF_10', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_1071, plain, (![B_447]: (k1_waybel_9('#skF_9', B_447)='#skF_5'('#skF_9', B_447) | ~v11_waybel_0(B_447, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_447), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_447, '#skF_9') | ~v7_waybel_0(B_447) | ~v4_orders_2(B_447) | v2_struct_0(B_447))), inference(splitRight, [status(thm)], [c_1060])).
% 5.56/1.99  tff(c_1075, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_1071])).
% 5.56/1.99  tff(c_1078, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_1075])).
% 5.56/1.99  tff(c_1080, plain, (![B_448]: (k1_waybel_9('#skF_9', B_448)='#skF_5'('#skF_9', B_448) | ~v11_waybel_0(B_448, '#skF_9') | ~l1_waybel_0(B_448, '#skF_9') | ~v7_waybel_0(B_448) | ~v4_orders_2(B_448) | v2_struct_0(B_448))), inference(negUnitSimplification, [status(thm)], [c_1070, c_1078])).
% 5.56/1.99  tff(c_1083, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_52, c_1080])).
% 5.56/1.99  tff(c_1086, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1083])).
% 5.56/1.99  tff(c_1087, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_60, c_1086])).
% 5.56/1.99  tff(c_979, plain, (![A_419, B_420, C_421]: ('#skF_6'(A_419, B_420)!='#skF_7'(A_419, B_420) | r2_hidden(C_421, k10_yellow_6(A_419, B_420)) | ~r3_waybel_9(A_419, B_420, C_421) | ~m1_subset_1(C_421, u1_struct_0(A_419)) | ~l1_waybel_0(B_420, A_419) | ~v7_waybel_0(B_420) | ~v4_orders_2(B_420) | v2_struct_0(B_420) | ~l1_pre_topc(A_419) | ~v1_compts_1(A_419) | ~v8_pre_topc(A_419) | ~v2_pre_topc(A_419) | v2_struct_0(A_419))), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.56/1.99  tff(c_50, plain, (~r2_hidden(k1_waybel_9('#skF_9', '#skF_10'), k10_yellow_6('#skF_9', '#skF_10')) | ~r2_waybel_9('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_311])).
% 5.56/1.99  tff(c_92, plain, (~r2_waybel_9('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_50])).
% 5.56/1.99  tff(c_124, plain, (![A_196, B_197, C_198]: (~v5_pre_topc(k4_waybel_1(A_196, '#skF_8'(A_196, B_197, C_198)), A_196, A_196) | k1_waybel_9(A_196, C_198)=B_197 | ~r3_waybel_9(A_196, C_198, B_197) | ~v11_waybel_0(C_198, A_196) | ~l1_waybel_0(C_198, A_196) | ~v7_waybel_0(C_198) | ~v4_orders_2(C_198) | v2_struct_0(C_198) | ~m1_subset_1(B_197, u1_struct_0(A_196)) | ~l1_waybel_9(A_196) | ~v1_compts_1(A_196) | ~v2_lattice3(A_196) | ~v1_lattice3(A_196) | ~v5_orders_2(A_196) | ~v4_orders_2(A_196) | ~v3_orders_2(A_196) | ~v8_pre_topc(A_196) | ~v2_pre_topc(A_196))), inference(cnfTransformation, [status(thm)], [f_271])).
% 5.56/1.99  tff(c_128, plain, (![C_198, B_197]: (k1_waybel_9('#skF_9', C_198)=B_197 | ~r3_waybel_9('#skF_9', C_198, B_197) | ~v11_waybel_0(C_198, '#skF_9') | ~l1_waybel_0(C_198, '#skF_9') | ~v7_waybel_0(C_198) | ~v4_orders_2(C_198) | v2_struct_0(C_198) | ~m1_subset_1(B_197, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_8'('#skF_9', B_197, C_198), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_62, c_124])).
% 5.56/1.99  tff(c_132, plain, (![C_199, B_200]: (k1_waybel_9('#skF_9', C_199)=B_200 | ~r3_waybel_9('#skF_9', C_199, B_200) | ~v11_waybel_0(C_199, '#skF_9') | ~l1_waybel_0(C_199, '#skF_9') | ~v7_waybel_0(C_199) | ~v4_orders_2(C_199) | v2_struct_0(C_199) | ~m1_subset_1(B_200, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_8'('#skF_9', B_200, C_199), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_128])).
% 5.56/1.99  tff(c_136, plain, (![C_142, B_138]: (k1_waybel_9('#skF_9', C_142)=B_138 | ~r3_waybel_9('#skF_9', C_142, B_138) | ~v11_waybel_0(C_142, '#skF_9') | ~l1_waybel_0(C_142, '#skF_9') | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_132])).
% 5.56/1.99  tff(c_140, plain, (![C_201, B_202]: (k1_waybel_9('#skF_9', C_201)=B_202 | ~r3_waybel_9('#skF_9', C_201, B_202) | ~v11_waybel_0(C_201, '#skF_9') | ~l1_waybel_0(C_201, '#skF_9') | ~v7_waybel_0(C_201) | ~v4_orders_2(C_201) | v2_struct_0(C_201) | ~m1_subset_1(B_202, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_136])).
% 5.56/1.99  tff(c_149, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_140])).
% 5.56/1.99  tff(c_158, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_149])).
% 5.56/1.99  tff(c_159, plain, (v2_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_158])).
% 5.56/1.99  tff(c_162, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_159, c_2])).
% 5.56/1.99  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_70, c_162])).
% 5.56/1.99  tff(c_168, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_158])).
% 5.56/1.99  tff(c_26, plain, (![A_31, B_47, D_59]: (m1_subset_1('#skF_3'(A_31, B_47, D_59, D_59), u1_struct_0(A_31)) | r1_lattice3(A_31, k2_relset_1(u1_struct_0(B_47), u1_struct_0(A_31), u1_waybel_0(A_31, B_47)), D_59) | ~r3_waybel_9(A_31, B_47, D_59) | ~v11_waybel_0(B_47, A_31) | ~m1_subset_1(D_59, u1_struct_0(A_31)) | ~l1_waybel_0(B_47, A_31) | ~v7_waybel_0(B_47) | ~v4_orders_2(B_47) | v2_struct_0(B_47) | ~l1_waybel_9(A_31) | ~v1_compts_1(A_31) | ~v2_lattice3(A_31) | ~v1_lattice3(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | ~v8_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.56/1.99  tff(c_241, plain, (![A_220, B_221, D_222]: (~v5_pre_topc(k4_waybel_1(A_220, '#skF_3'(A_220, B_221, D_222, D_222)), A_220, A_220) | r1_lattice3(A_220, k2_relset_1(u1_struct_0(B_221), u1_struct_0(A_220), u1_waybel_0(A_220, B_221)), D_222) | ~r3_waybel_9(A_220, B_221, D_222) | ~v11_waybel_0(B_221, A_220) | ~m1_subset_1(D_222, u1_struct_0(A_220)) | ~l1_waybel_0(B_221, A_220) | ~v7_waybel_0(B_221) | ~v4_orders_2(B_221) | v2_struct_0(B_221) | ~l1_waybel_9(A_220) | ~v1_compts_1(A_220) | ~v2_lattice3(A_220) | ~v1_lattice3(A_220) | ~v5_orders_2(A_220) | ~v4_orders_2(A_220) | ~v3_orders_2(A_220) | ~v8_pre_topc(A_220) | ~v2_pre_topc(A_220))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.56/1.99  tff(c_244, plain, (![B_221, D_222]: (r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_221), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_221)), D_222) | ~r3_waybel_9('#skF_9', B_221, D_222) | ~v11_waybel_0(B_221, '#skF_9') | ~m1_subset_1(D_222, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_221, '#skF_9') | ~v7_waybel_0(B_221) | ~v4_orders_2(B_221) | v2_struct_0(B_221) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_3'('#skF_9', B_221, D_222, D_222), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_62, c_241])).
% 5.56/1.99  tff(c_249, plain, (![B_225, D_226]: (r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_225), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_225)), D_226) | ~r3_waybel_9('#skF_9', B_225, D_226) | ~v11_waybel_0(B_225, '#skF_9') | ~m1_subset_1(D_226, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_225, '#skF_9') | ~v7_waybel_0(B_225) | ~v4_orders_2(B_225) | v2_struct_0(B_225) | ~m1_subset_1('#skF_3'('#skF_9', B_225, D_226, D_226), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_244])).
% 5.56/1.99  tff(c_252, plain, (![B_47, D_59]: (r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_47), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_47)), D_59) | ~r3_waybel_9('#skF_9', B_47, D_59) | ~v11_waybel_0(B_47, '#skF_9') | ~m1_subset_1(D_59, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_47, '#skF_9') | ~v7_waybel_0(B_47) | ~v4_orders_2(B_47) | v2_struct_0(B_47) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_26, c_249])).
% 5.56/1.99  tff(c_255, plain, (![B_47, D_59]: (r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_47), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_47)), D_59) | ~r3_waybel_9('#skF_9', B_47, D_59) | ~v11_waybel_0(B_47, '#skF_9') | ~m1_subset_1(D_59, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_47, '#skF_9') | ~v7_waybel_0(B_47) | ~v4_orders_2(B_47) | v2_struct_0(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_252])).
% 5.56/1.99  tff(c_14, plain, (![A_2, B_16, C_23]: (m1_subset_1('#skF_1'(A_2, B_16, C_23), u1_struct_0(A_2)) | r2_yellow_0(A_2, B_16) | ~r1_lattice3(A_2, B_16, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v5_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.56/1.99  tff(c_12, plain, (![A_2, B_16, C_23]: (r1_lattice3(A_2, B_16, '#skF_1'(A_2, B_16, C_23)) | r2_yellow_0(A_2, B_16) | ~r1_lattice3(A_2, B_16, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v5_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.56/1.99  tff(c_263, plain, (![A_229, B_230, D_231, E_232]: (m1_subset_1('#skF_4'(A_229, B_230, D_231, D_231), u1_struct_0(A_229)) | r1_orders_2(A_229, E_232, D_231) | ~r1_lattice3(A_229, k2_relset_1(u1_struct_0(B_230), u1_struct_0(A_229), u1_waybel_0(A_229, B_230)), E_232) | ~m1_subset_1(E_232, u1_struct_0(A_229)) | ~r3_waybel_9(A_229, B_230, D_231) | ~m1_subset_1(D_231, u1_struct_0(A_229)) | ~l1_waybel_0(B_230, A_229) | ~v7_waybel_0(B_230) | ~v4_orders_2(B_230) | v2_struct_0(B_230) | ~l1_waybel_9(A_229) | ~v1_compts_1(A_229) | ~v2_lattice3(A_229) | ~v1_lattice3(A_229) | ~v5_orders_2(A_229) | ~v4_orders_2(A_229) | ~v3_orders_2(A_229) | ~v8_pre_topc(A_229) | ~v2_pre_topc(A_229))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.56/1.99  tff(c_581, plain, (![A_322, B_323, D_324, C_325]: (m1_subset_1('#skF_4'(A_322, B_323, D_324, D_324), u1_struct_0(A_322)) | r1_orders_2(A_322, '#skF_1'(A_322, k2_relset_1(u1_struct_0(B_323), u1_struct_0(A_322), u1_waybel_0(A_322, B_323)), C_325), D_324) | ~m1_subset_1('#skF_1'(A_322, k2_relset_1(u1_struct_0(B_323), u1_struct_0(A_322), u1_waybel_0(A_322, B_323)), C_325), u1_struct_0(A_322)) | ~r3_waybel_9(A_322, B_323, D_324) | ~m1_subset_1(D_324, u1_struct_0(A_322)) | ~l1_waybel_0(B_323, A_322) | ~v7_waybel_0(B_323) | ~v4_orders_2(B_323) | v2_struct_0(B_323) | ~l1_waybel_9(A_322) | ~v1_compts_1(A_322) | ~v2_lattice3(A_322) | ~v1_lattice3(A_322) | ~v4_orders_2(A_322) | ~v3_orders_2(A_322) | ~v8_pre_topc(A_322) | ~v2_pre_topc(A_322) | r2_yellow_0(A_322, k2_relset_1(u1_struct_0(B_323), u1_struct_0(A_322), u1_waybel_0(A_322, B_323))) | ~r1_lattice3(A_322, k2_relset_1(u1_struct_0(B_323), u1_struct_0(A_322), u1_waybel_0(A_322, B_323)), C_325) | ~m1_subset_1(C_325, u1_struct_0(A_322)) | ~l1_orders_2(A_322) | ~v5_orders_2(A_322))), inference(resolution, [status(thm)], [c_12, c_263])).
% 5.56/1.99  tff(c_725, plain, (![A_357, B_358, D_359, C_360]: (m1_subset_1('#skF_4'(A_357, B_358, D_359, D_359), u1_struct_0(A_357)) | r1_orders_2(A_357, '#skF_1'(A_357, k2_relset_1(u1_struct_0(B_358), u1_struct_0(A_357), u1_waybel_0(A_357, B_358)), C_360), D_359) | ~r3_waybel_9(A_357, B_358, D_359) | ~m1_subset_1(D_359, u1_struct_0(A_357)) | ~l1_waybel_0(B_358, A_357) | ~v7_waybel_0(B_358) | ~v4_orders_2(B_358) | v2_struct_0(B_358) | ~l1_waybel_9(A_357) | ~v1_compts_1(A_357) | ~v2_lattice3(A_357) | ~v1_lattice3(A_357) | ~v4_orders_2(A_357) | ~v3_orders_2(A_357) | ~v8_pre_topc(A_357) | ~v2_pre_topc(A_357) | r2_yellow_0(A_357, k2_relset_1(u1_struct_0(B_358), u1_struct_0(A_357), u1_waybel_0(A_357, B_358))) | ~r1_lattice3(A_357, k2_relset_1(u1_struct_0(B_358), u1_struct_0(A_357), u1_waybel_0(A_357, B_358)), C_360) | ~m1_subset_1(C_360, u1_struct_0(A_357)) | ~l1_orders_2(A_357) | ~v5_orders_2(A_357))), inference(resolution, [status(thm)], [c_14, c_581])).
% 5.56/1.99  tff(c_10, plain, (![A_2, B_16, C_23]: (~r1_orders_2(A_2, '#skF_1'(A_2, B_16, C_23), C_23) | r2_yellow_0(A_2, B_16) | ~r1_lattice3(A_2, B_16, C_23) | ~m1_subset_1(C_23, u1_struct_0(A_2)) | ~l1_orders_2(A_2) | ~v5_orders_2(A_2))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.56/1.99  tff(c_765, plain, (![A_365, B_366, D_367]: (m1_subset_1('#skF_4'(A_365, B_366, D_367, D_367), u1_struct_0(A_365)) | ~r3_waybel_9(A_365, B_366, D_367) | ~l1_waybel_0(B_366, A_365) | ~v7_waybel_0(B_366) | ~v4_orders_2(B_366) | v2_struct_0(B_366) | ~l1_waybel_9(A_365) | ~v1_compts_1(A_365) | ~v2_lattice3(A_365) | ~v1_lattice3(A_365) | ~v4_orders_2(A_365) | ~v3_orders_2(A_365) | ~v8_pre_topc(A_365) | ~v2_pre_topc(A_365) | r2_yellow_0(A_365, k2_relset_1(u1_struct_0(B_366), u1_struct_0(A_365), u1_waybel_0(A_365, B_366))) | ~r1_lattice3(A_365, k2_relset_1(u1_struct_0(B_366), u1_struct_0(A_365), u1_waybel_0(A_365, B_366)), D_367) | ~m1_subset_1(D_367, u1_struct_0(A_365)) | ~l1_orders_2(A_365) | ~v5_orders_2(A_365))), inference(resolution, [status(thm)], [c_725, c_10])).
% 5.56/1.99  tff(c_767, plain, (![B_47, D_59]: (m1_subset_1('#skF_4'('#skF_9', B_47, D_59, D_59), u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_47), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_47))) | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9') | ~r3_waybel_9('#skF_9', B_47, D_59) | ~v11_waybel_0(B_47, '#skF_9') | ~m1_subset_1(D_59, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_47, '#skF_9') | ~v7_waybel_0(B_47) | ~v4_orders_2(B_47) | v2_struct_0(B_47))), inference(resolution, [status(thm)], [c_255, c_765])).
% 5.56/1.99  tff(c_782, plain, (![B_368, D_369]: (m1_subset_1('#skF_4'('#skF_9', B_368, D_369, D_369), u1_struct_0('#skF_9')) | r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_368), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_368))) | ~r3_waybel_9('#skF_9', B_368, D_369) | ~v11_waybel_0(B_368, '#skF_9') | ~m1_subset_1(D_369, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_368, '#skF_9') | ~v7_waybel_0(B_368) | ~v4_orders_2(B_368) | v2_struct_0(B_368))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_85, c_80, c_78, c_76, c_74, c_70, c_68, c_66, c_64, c_767])).
% 5.56/1.99  tff(c_312, plain, (![A_244, B_245, D_246, E_247]: (~v5_pre_topc(k4_waybel_1(A_244, '#skF_4'(A_244, B_245, D_246, D_246)), A_244, A_244) | r1_orders_2(A_244, E_247, D_246) | ~r1_lattice3(A_244, k2_relset_1(u1_struct_0(B_245), u1_struct_0(A_244), u1_waybel_0(A_244, B_245)), E_247) | ~m1_subset_1(E_247, u1_struct_0(A_244)) | ~r3_waybel_9(A_244, B_245, D_246) | ~m1_subset_1(D_246, u1_struct_0(A_244)) | ~l1_waybel_0(B_245, A_244) | ~v7_waybel_0(B_245) | ~v4_orders_2(B_245) | v2_struct_0(B_245) | ~l1_waybel_9(A_244) | ~v1_compts_1(A_244) | ~v2_lattice3(A_244) | ~v1_lattice3(A_244) | ~v5_orders_2(A_244) | ~v4_orders_2(A_244) | ~v3_orders_2(A_244) | ~v8_pre_topc(A_244) | ~v2_pre_topc(A_244))), inference(cnfTransformation, [status(thm)], [f_163])).
% 5.56/1.99  tff(c_315, plain, (![E_247, D_246, B_245]: (r1_orders_2('#skF_9', E_247, D_246) | ~r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_245), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_245)), E_247) | ~m1_subset_1(E_247, u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', B_245, D_246) | ~m1_subset_1(D_246, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_245, '#skF_9') | ~v7_waybel_0(B_245) | ~v4_orders_2(B_245) | v2_struct_0(B_245) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_4'('#skF_9', B_245, D_246, D_246), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_62, c_312])).
% 5.56/1.99  tff(c_319, plain, (![E_248, D_249, B_250]: (r1_orders_2('#skF_9', E_248, D_249) | ~r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_250), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_250)), E_248) | ~m1_subset_1(E_248, u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', B_250, D_249) | ~m1_subset_1(D_249, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_250, '#skF_9') | ~v7_waybel_0(B_250) | ~v4_orders_2(B_250) | v2_struct_0(B_250) | ~m1_subset_1('#skF_4'('#skF_9', B_250, D_249, D_249), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_315])).
% 5.56/1.99  tff(c_327, plain, (![B_250, C_23, D_249]: (r1_orders_2('#skF_9', '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_250), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_250)), C_23), D_249) | ~m1_subset_1('#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_250), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_250)), C_23), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', B_250, D_249) | ~m1_subset_1(D_249, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_250, '#skF_9') | ~v7_waybel_0(B_250) | ~v4_orders_2(B_250) | v2_struct_0(B_250) | ~m1_subset_1('#skF_4'('#skF_9', B_250, D_249, D_249), u1_struct_0('#skF_9')) | r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_250), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_250))) | ~r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_250), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_250)), C_23) | ~m1_subset_1(C_23, u1_struct_0('#skF_9')) | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9'))), inference(resolution, [status(thm)], [c_12, c_319])).
% 5.56/1.99  tff(c_535, plain, (![B_305, C_306, D_307]: (r1_orders_2('#skF_9', '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305)), C_306), D_307) | ~m1_subset_1('#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305)), C_306), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', B_305, D_307) | ~m1_subset_1(D_307, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_305, '#skF_9') | ~v7_waybel_0(B_305) | ~v4_orders_2(B_305) | v2_struct_0(B_305) | ~m1_subset_1('#skF_4'('#skF_9', B_305, D_307, D_307), u1_struct_0('#skF_9')) | r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305))) | ~r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305)), C_306) | ~m1_subset_1(C_306, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_85, c_327])).
% 5.56/1.99  tff(c_538, plain, (![B_305, C_23, D_307]: (r1_orders_2('#skF_9', '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305)), C_23), D_307) | ~r3_waybel_9('#skF_9', B_305, D_307) | ~m1_subset_1(D_307, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_305, '#skF_9') | ~v7_waybel_0(B_305) | ~v4_orders_2(B_305) | v2_struct_0(B_305) | ~m1_subset_1('#skF_4'('#skF_9', B_305, D_307, D_307), u1_struct_0('#skF_9')) | r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305))) | ~r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305)), C_23) | ~m1_subset_1(C_23, u1_struct_0('#skF_9')) | ~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9'))), inference(resolution, [status(thm)], [c_14, c_535])).
% 5.56/1.99  tff(c_541, plain, (![B_305, C_23, D_307]: (r1_orders_2('#skF_9', '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305)), C_23), D_307) | ~r3_waybel_9('#skF_9', B_305, D_307) | ~m1_subset_1(D_307, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_305, '#skF_9') | ~v7_waybel_0(B_305) | ~v4_orders_2(B_305) | v2_struct_0(B_305) | ~m1_subset_1('#skF_4'('#skF_9', B_305, D_307, D_307), u1_struct_0('#skF_9')) | r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305))) | ~r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_305), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_305)), C_23) | ~m1_subset_1(C_23, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_85, c_538])).
% 5.56/1.99  tff(c_876, plain, (![B_384, C_385, D_386]: (r1_orders_2('#skF_9', '#skF_1'('#skF_9', k2_relset_1(u1_struct_0(B_384), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_384)), C_385), D_386) | ~r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_384), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_384)), C_385) | ~m1_subset_1(C_385, u1_struct_0('#skF_9')) | r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_384), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_384))) | ~r3_waybel_9('#skF_9', B_384, D_386) | ~v11_waybel_0(B_384, '#skF_9') | ~m1_subset_1(D_386, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_384, '#skF_9') | ~v7_waybel_0(B_384) | ~v4_orders_2(B_384) | v2_struct_0(B_384))), inference(resolution, [status(thm)], [c_782, c_541])).
% 5.56/1.99  tff(c_880, plain, (![B_384, D_386]: (~l1_orders_2('#skF_9') | ~v5_orders_2('#skF_9') | ~r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_384), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_384)), D_386) | r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_384), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_384))) | ~r3_waybel_9('#skF_9', B_384, D_386) | ~v11_waybel_0(B_384, '#skF_9') | ~m1_subset_1(D_386, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_384, '#skF_9') | ~v7_waybel_0(B_384) | ~v4_orders_2(B_384) | v2_struct_0(B_384))), inference(resolution, [status(thm)], [c_876, c_10])).
% 5.56/1.99  tff(c_884, plain, (![B_387, D_388]: (~r1_lattice3('#skF_9', k2_relset_1(u1_struct_0(B_387), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_387)), D_388) | r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_387), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_387))) | ~r3_waybel_9('#skF_9', B_387, D_388) | ~v11_waybel_0(B_387, '#skF_9') | ~m1_subset_1(D_388, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_387, '#skF_9') | ~v7_waybel_0(B_387) | ~v4_orders_2(B_387) | v2_struct_0(B_387))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_85, c_880])).
% 5.56/1.99  tff(c_910, plain, (![B_389, D_390]: (r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_389), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_389))) | ~r3_waybel_9('#skF_9', B_389, D_390) | ~v11_waybel_0(B_389, '#skF_9') | ~m1_subset_1(D_390, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_389, '#skF_9') | ~v7_waybel_0(B_389) | ~v4_orders_2(B_389) | v2_struct_0(B_389))), inference(resolution, [status(thm)], [c_255, c_884])).
% 5.56/1.99  tff(c_919, plain, (![B_111]: (r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_111), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_111))) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_910])).
% 5.56/1.99  tff(c_930, plain, (![B_111]: (r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_111), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_111))) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_919])).
% 5.56/1.99  tff(c_932, plain, (![B_391]: (r2_yellow_0('#skF_9', k2_relset_1(u1_struct_0(B_391), u1_struct_0('#skF_9'), u1_waybel_0('#skF_9', B_391))) | ~v11_waybel_0(B_391, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_391), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_391, '#skF_9') | ~v7_waybel_0(B_391) | ~v4_orders_2(B_391) | v2_struct_0(B_391))), inference(negUnitSimplification, [status(thm)], [c_168, c_930])).
% 5.56/1.99  tff(c_16, plain, (![A_27, B_29]: (r2_waybel_9(A_27, B_29) | ~r2_yellow_0(A_27, k2_relset_1(u1_struct_0(B_29), u1_struct_0(A_27), u1_waybel_0(A_27, B_29))) | ~l1_waybel_0(B_29, A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.56/1.99  tff(c_935, plain, (![B_391]: (r2_waybel_9('#skF_9', B_391) | ~l1_orders_2('#skF_9') | ~v11_waybel_0(B_391, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_391), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_391, '#skF_9') | ~v7_waybel_0(B_391) | ~v4_orders_2(B_391) | v2_struct_0(B_391))), inference(resolution, [status(thm)], [c_932, c_16])).
% 5.56/1.99  tff(c_939, plain, (![B_392]: (r2_waybel_9('#skF_9', B_392) | ~v11_waybel_0(B_392, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_392), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_392, '#skF_9') | ~v7_waybel_0(B_392) | ~v4_orders_2(B_392) | v2_struct_0(B_392))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_935])).
% 5.56/1.99  tff(c_943, plain, (![B_111]: (r2_waybel_9('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_939])).
% 5.56/1.99  tff(c_946, plain, (![B_111]: (r2_waybel_9('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_943])).
% 5.56/1.99  tff(c_948, plain, (![B_393]: (r2_waybel_9('#skF_9', B_393) | ~v11_waybel_0(B_393, '#skF_9') | ~l1_waybel_0(B_393, '#skF_9') | ~v7_waybel_0(B_393) | ~v4_orders_2(B_393) | v2_struct_0(B_393))), inference(negUnitSimplification, [status(thm)], [c_168, c_946])).
% 5.56/1.99  tff(c_951, plain, (r2_waybel_9('#skF_9', '#skF_10') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_52, c_948])).
% 5.56/1.99  tff(c_954, plain, (r2_waybel_9('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_951])).
% 5.56/1.99  tff(c_956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_92, c_954])).
% 5.56/1.99  tff(c_957, plain, (~r2_hidden(k1_waybel_9('#skF_9', '#skF_10'), k10_yellow_6('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_50])).
% 5.56/1.99  tff(c_982, plain, ('#skF_6'('#skF_9', '#skF_10')!='#skF_7'('#skF_9', '#skF_10') | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_9('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_979, c_957])).
% 5.56/1.99  tff(c_985, plain, ('#skF_6'('#skF_9', '#skF_10')!='#skF_7'('#skF_9', '#skF_10') | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_9('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_58, c_56, c_54, c_982])).
% 5.56/1.99  tff(c_986, plain, ('#skF_6'('#skF_9', '#skF_10')!='#skF_7'('#skF_9', '#skF_10') | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_9('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_60, c_985])).
% 5.56/1.99  tff(c_987, plain, (~m1_subset_1(k1_waybel_9('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_986])).
% 5.56/1.99  tff(c_1090, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1087, c_987])).
% 5.56/1.99  tff(c_1098, plain, (~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_34, c_1090])).
% 5.56/1.99  tff(c_1101, plain, (v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_58, c_56, c_54, c_1098])).
% 5.56/1.99  tff(c_1103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1070, c_60, c_1101])).
% 5.56/1.99  tff(c_1104, plain, (~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | '#skF_6'('#skF_9', '#skF_10')!='#skF_7'('#skF_9', '#skF_10') | v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_986])).
% 5.56/1.99  tff(c_1106, plain, ('#skF_6'('#skF_9', '#skF_10')!='#skF_7'('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_1104])).
% 5.56/1.99  tff(c_1105, plain, (m1_subset_1(k1_waybel_9('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_986])).
% 5.56/1.99  tff(c_1146, plain, (![A_470, B_471, C_472]: (~v5_pre_topc(k4_waybel_1(A_470, '#skF_8'(A_470, B_471, C_472)), A_470, A_470) | k1_waybel_9(A_470, C_472)=B_471 | ~r3_waybel_9(A_470, C_472, B_471) | ~v11_waybel_0(C_472, A_470) | ~l1_waybel_0(C_472, A_470) | ~v7_waybel_0(C_472) | ~v4_orders_2(C_472) | v2_struct_0(C_472) | ~m1_subset_1(B_471, u1_struct_0(A_470)) | ~l1_waybel_9(A_470) | ~v1_compts_1(A_470) | ~v2_lattice3(A_470) | ~v1_lattice3(A_470) | ~v5_orders_2(A_470) | ~v4_orders_2(A_470) | ~v3_orders_2(A_470) | ~v8_pre_topc(A_470) | ~v2_pre_topc(A_470))), inference(cnfTransformation, [status(thm)], [f_271])).
% 5.56/1.99  tff(c_1150, plain, (![C_472, B_471]: (k1_waybel_9('#skF_9', C_472)=B_471 | ~r3_waybel_9('#skF_9', C_472, B_471) | ~v11_waybel_0(C_472, '#skF_9') | ~l1_waybel_0(C_472, '#skF_9') | ~v7_waybel_0(C_472) | ~v4_orders_2(C_472) | v2_struct_0(C_472) | ~m1_subset_1(B_471, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_8'('#skF_9', B_471, C_472), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_62, c_1146])).
% 5.56/1.99  tff(c_1154, plain, (![C_473, B_474]: (k1_waybel_9('#skF_9', C_473)=B_474 | ~r3_waybel_9('#skF_9', C_473, B_474) | ~v11_waybel_0(C_473, '#skF_9') | ~l1_waybel_0(C_473, '#skF_9') | ~v7_waybel_0(C_473) | ~v4_orders_2(C_473) | v2_struct_0(C_473) | ~m1_subset_1(B_474, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_8'('#skF_9', B_474, C_473), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_1150])).
% 5.56/1.99  tff(c_1158, plain, (![C_142, B_138]: (k1_waybel_9('#skF_9', C_142)=B_138 | ~r3_waybel_9('#skF_9', C_142, B_138) | ~v11_waybel_0(C_142, '#skF_9') | ~l1_waybel_0(C_142, '#skF_9') | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_1154])).
% 5.56/1.99  tff(c_1162, plain, (![C_475, B_476]: (k1_waybel_9('#skF_9', C_475)=B_476 | ~r3_waybel_9('#skF_9', C_475, B_476) | ~v11_waybel_0(C_475, '#skF_9') | ~l1_waybel_0(C_475, '#skF_9') | ~v7_waybel_0(C_475) | ~v4_orders_2(C_475) | v2_struct_0(C_475) | ~m1_subset_1(B_476, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_1158])).
% 5.56/1.99  tff(c_1171, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_1162])).
% 5.56/1.99  tff(c_1180, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_1171])).
% 5.56/1.99  tff(c_1181, plain, (v2_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1180])).
% 5.56/1.99  tff(c_1184, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_1181, c_2])).
% 5.56/1.99  tff(c_1188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_70, c_1184])).
% 5.56/1.99  tff(c_1190, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1180])).
% 5.56/1.99  tff(c_1193, plain, (![B_480]: (k1_waybel_9('#skF_9', B_480)='#skF_5'('#skF_9', B_480) | ~v11_waybel_0(B_480, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_480), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_480, '#skF_9') | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480))), inference(splitRight, [status(thm)], [c_1180])).
% 5.56/1.99  tff(c_1197, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_1193])).
% 5.56/1.99  tff(c_1200, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_1197])).
% 5.56/1.99  tff(c_1202, plain, (![B_481]: (k1_waybel_9('#skF_9', B_481)='#skF_5'('#skF_9', B_481) | ~v11_waybel_0(B_481, '#skF_9') | ~l1_waybel_0(B_481, '#skF_9') | ~v7_waybel_0(B_481) | ~v4_orders_2(B_481) | v2_struct_0(B_481))), inference(negUnitSimplification, [status(thm)], [c_1190, c_1200])).
% 5.56/1.99  tff(c_1205, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_52, c_1202])).
% 5.56/1.99  tff(c_1208, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1205])).
% 5.56/1.99  tff(c_1209, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_60, c_1208])).
% 5.56/1.99  tff(c_1107, plain, (![A_452, B_453, C_454]: (m1_subset_1('#skF_6'(A_452, B_453), u1_struct_0(A_452)) | r2_hidden(C_454, k10_yellow_6(A_452, B_453)) | ~r3_waybel_9(A_452, B_453, C_454) | ~m1_subset_1(C_454, u1_struct_0(A_452)) | ~l1_waybel_0(B_453, A_452) | ~v7_waybel_0(B_453) | ~v4_orders_2(B_453) | v2_struct_0(B_453) | ~l1_pre_topc(A_452) | ~v1_compts_1(A_452) | ~v8_pre_topc(A_452) | ~v2_pre_topc(A_452) | v2_struct_0(A_452))), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.56/1.99  tff(c_1110, plain, (m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_9('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1107, c_957])).
% 5.56/1.99  tff(c_1113, plain, (m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_58, c_56, c_54, c_1105, c_1110])).
% 5.56/1.99  tff(c_1114, plain, (m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | v2_struct_0('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_60, c_1113])).
% 5.56/1.99  tff(c_1115, plain, (~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_1114])).
% 5.56/1.99  tff(c_1210, plain, (~r3_waybel_9('#skF_9', '#skF_10', '#skF_5'('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1209, c_1115])).
% 5.56/1.99  tff(c_1254, plain, (~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_32, c_1210])).
% 5.56/1.99  tff(c_1257, plain, (v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_58, c_56, c_54, c_1254])).
% 5.56/1.99  tff(c_1259, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1190, c_60, c_1257])).
% 5.56/1.99  tff(c_1261, plain, (r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_1114])).
% 5.56/1.99  tff(c_1263, plain, (![A_482, B_483, C_484]: (r3_waybel_9(A_482, B_483, '#skF_7'(A_482, B_483)) | r2_hidden(C_484, k10_yellow_6(A_482, B_483)) | ~r3_waybel_9(A_482, B_483, C_484) | ~m1_subset_1(C_484, u1_struct_0(A_482)) | ~l1_waybel_0(B_483, A_482) | ~v7_waybel_0(B_483) | ~v4_orders_2(B_483) | v2_struct_0(B_483) | ~l1_pre_topc(A_482) | ~v1_compts_1(A_482) | ~v8_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.56/1.99  tff(c_1266, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', '#skF_10')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_9('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1263, c_957])).
% 5.56/1.99  tff(c_1269, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', '#skF_10')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_58, c_56, c_54, c_1105, c_1261, c_1266])).
% 5.56/1.99  tff(c_1270, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', '#skF_10')) | v2_struct_0('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_60, c_1269])).
% 5.56/1.99  tff(c_1271, plain, (v2_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1270])).
% 5.56/1.99  tff(c_1274, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_1271, c_2])).
% 5.56/1.99  tff(c_1278, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_70, c_1274])).
% 5.56/1.99  tff(c_1280, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1270])).
% 5.56/1.99  tff(c_1281, plain, (![A_485, B_486, C_487]: (m1_subset_1('#skF_7'(A_485, B_486), u1_struct_0(A_485)) | r2_hidden(C_487, k10_yellow_6(A_485, B_486)) | ~r3_waybel_9(A_485, B_486, C_487) | ~m1_subset_1(C_487, u1_struct_0(A_485)) | ~l1_waybel_0(B_486, A_485) | ~v7_waybel_0(B_486) | ~v4_orders_2(B_486) | v2_struct_0(B_486) | ~l1_pre_topc(A_485) | ~v1_compts_1(A_485) | ~v8_pre_topc(A_485) | ~v2_pre_topc(A_485) | v2_struct_0(A_485))), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.56/1.99  tff(c_1284, plain, (m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_9('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1281, c_957])).
% 5.56/1.99  tff(c_1287, plain, (m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_58, c_56, c_54, c_1105, c_1261, c_1284])).
% 5.56/1.99  tff(c_1288, plain, (m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1280, c_60, c_1287])).
% 5.56/1.99  tff(c_1279, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_1270])).
% 5.56/1.99  tff(c_1303, plain, (![A_497, B_498, C_499]: (~v5_pre_topc(k4_waybel_1(A_497, '#skF_8'(A_497, B_498, C_499)), A_497, A_497) | k1_waybel_9(A_497, C_499)=B_498 | ~r3_waybel_9(A_497, C_499, B_498) | ~v11_waybel_0(C_499, A_497) | ~l1_waybel_0(C_499, A_497) | ~v7_waybel_0(C_499) | ~v4_orders_2(C_499) | v2_struct_0(C_499) | ~m1_subset_1(B_498, u1_struct_0(A_497)) | ~l1_waybel_9(A_497) | ~v1_compts_1(A_497) | ~v2_lattice3(A_497) | ~v1_lattice3(A_497) | ~v5_orders_2(A_497) | ~v4_orders_2(A_497) | ~v3_orders_2(A_497) | ~v8_pre_topc(A_497) | ~v2_pre_topc(A_497))), inference(cnfTransformation, [status(thm)], [f_271])).
% 5.56/1.99  tff(c_1307, plain, (![C_499, B_498]: (k1_waybel_9('#skF_9', C_499)=B_498 | ~r3_waybel_9('#skF_9', C_499, B_498) | ~v11_waybel_0(C_499, '#skF_9') | ~l1_waybel_0(C_499, '#skF_9') | ~v7_waybel_0(C_499) | ~v4_orders_2(C_499) | v2_struct_0(C_499) | ~m1_subset_1(B_498, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_8'('#skF_9', B_498, C_499), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_62, c_1303])).
% 5.56/1.99  tff(c_1311, plain, (![C_500, B_501]: (k1_waybel_9('#skF_9', C_500)=B_501 | ~r3_waybel_9('#skF_9', C_500, B_501) | ~v11_waybel_0(C_500, '#skF_9') | ~l1_waybel_0(C_500, '#skF_9') | ~v7_waybel_0(C_500) | ~v4_orders_2(C_500) | v2_struct_0(C_500) | ~m1_subset_1(B_501, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_8'('#skF_9', B_501, C_500), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_1307])).
% 5.56/1.99  tff(c_1315, plain, (![C_142, B_138]: (k1_waybel_9('#skF_9', C_142)=B_138 | ~r3_waybel_9('#skF_9', C_142, B_138) | ~v11_waybel_0(C_142, '#skF_9') | ~l1_waybel_0(C_142, '#skF_9') | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_1311])).
% 5.56/1.99  tff(c_1319, plain, (![C_502, B_503]: (k1_waybel_9('#skF_9', C_502)=B_503 | ~r3_waybel_9('#skF_9', C_502, B_503) | ~v11_waybel_0(C_502, '#skF_9') | ~l1_waybel_0(C_502, '#skF_9') | ~v7_waybel_0(C_502) | ~v4_orders_2(C_502) | v2_struct_0(C_502) | ~m1_subset_1(B_503, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_1315])).
% 5.56/1.99  tff(c_1326, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_7'('#skF_9', '#skF_10') | ~v11_waybel_0('#skF_10', '#skF_9') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_1279, c_1319])).
% 5.56/1.99  tff(c_1345, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_7'('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_58, c_56, c_54, c_52, c_1326])).
% 5.56/1.99  tff(c_1346, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_7'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_60, c_1345])).
% 5.56/1.99  tff(c_1260, plain, (v2_struct_0('#skF_9') | m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(splitRight, [status(thm)], [c_1114])).
% 5.56/1.99  tff(c_1262, plain, (m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(splitLeft, [status(thm)], [c_1260])).
% 5.56/1.99  tff(c_1289, plain, (![A_488, B_489, C_490]: (r3_waybel_9(A_488, B_489, '#skF_6'(A_488, B_489)) | r2_hidden(C_490, k10_yellow_6(A_488, B_489)) | ~r3_waybel_9(A_488, B_489, C_490) | ~m1_subset_1(C_490, u1_struct_0(A_488)) | ~l1_waybel_0(B_489, A_488) | ~v7_waybel_0(B_489) | ~v4_orders_2(B_489) | v2_struct_0(B_489) | ~l1_pre_topc(A_488) | ~v1_compts_1(A_488) | ~v8_pre_topc(A_488) | ~v2_pre_topc(A_488) | v2_struct_0(A_488))), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.56/1.99  tff(c_1292, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_6'('#skF_9', '#skF_10')) | ~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | ~m1_subset_1(k1_waybel_9('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_1289, c_957])).
% 5.56/1.99  tff(c_1295, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_6'('#skF_9', '#skF_10')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_58, c_56, c_54, c_1105, c_1261, c_1292])).
% 5.56/1.99  tff(c_1296, plain, (r3_waybel_9('#skF_9', '#skF_10', '#skF_6'('#skF_9', '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_1280, c_60, c_1295])).
% 5.56/1.99  tff(c_1321, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_6'('#skF_9', '#skF_10') | ~v11_waybel_0('#skF_10', '#skF_9') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~m1_subset_1('#skF_6'('#skF_9', '#skF_10'), u1_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_1296, c_1319])).
% 5.56/1.99  tff(c_1337, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_6'('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1262, c_58, c_56, c_54, c_52, c_1321])).
% 5.56/1.99  tff(c_1338, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_6'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_60, c_1337])).
% 5.56/1.99  tff(c_1369, plain, ('#skF_6'('#skF_9', '#skF_10')='#skF_7'('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1346, c_1338])).
% 5.56/1.99  tff(c_1370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1106, c_1369])).
% 5.56/1.99  tff(c_1371, plain, (v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1260])).
% 5.56/1.99  tff(c_1375, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_1371, c_2])).
% 5.56/1.99  tff(c_1379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_70, c_1375])).
% 5.56/1.99  tff(c_1381, plain, ('#skF_6'('#skF_9', '#skF_10')='#skF_7'('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_1104])).
% 5.56/1.99  tff(c_1403, plain, (![A_510, B_511, C_512]: (m1_subset_1('#skF_6'(A_510, B_511), u1_struct_0(A_510)) | r2_hidden(C_512, k10_yellow_6(A_510, B_511)) | ~r3_waybel_9(A_510, B_511, C_512) | ~m1_subset_1(C_512, u1_struct_0(A_510)) | ~l1_waybel_0(B_511, A_510) | ~v7_waybel_0(B_511) | ~v4_orders_2(B_511) | v2_struct_0(B_511) | ~l1_pre_topc(A_510) | ~v1_compts_1(A_510) | ~v8_pre_topc(A_510) | ~v2_pre_topc(A_510) | v2_struct_0(A_510))), inference(cnfTransformation, [status(thm)], [f_229])).
% 5.56/1.99  tff(c_1409, plain, (![C_512]: (m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | r2_hidden(C_512, k10_yellow_6('#skF_9', '#skF_10')) | ~r3_waybel_9('#skF_9', '#skF_10', C_512) | ~m1_subset_1(C_512, u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1381, c_1403])).
% 5.56/1.99  tff(c_1415, plain, (![C_512]: (m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | r2_hidden(C_512, k10_yellow_6('#skF_9', '#skF_10')) | ~r3_waybel_9('#skF_9', '#skF_10', C_512) | ~m1_subset_1(C_512, u1_struct_0('#skF_9')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_58, c_56, c_54, c_1409])).
% 5.56/1.99  tff(c_1416, plain, (![C_512]: (m1_subset_1('#skF_7'('#skF_9', '#skF_10'), u1_struct_0('#skF_9')) | r2_hidden(C_512, k10_yellow_6('#skF_9', '#skF_10')) | ~r3_waybel_9('#skF_9', '#skF_10', C_512) | ~m1_subset_1(C_512, u1_struct_0('#skF_9')) | v2_struct_0('#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_60, c_1415])).
% 5.56/1.99  tff(c_1417, plain, (v2_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_1416])).
% 5.56/1.99  tff(c_1420, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_1417, c_2])).
% 5.56/1.99  tff(c_1424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_70, c_1420])).
% 5.56/1.99  tff(c_1426, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1416])).
% 5.56/1.99  tff(c_1521, plain, (![A_536, B_537, C_538]: (~v5_pre_topc(k4_waybel_1(A_536, '#skF_8'(A_536, B_537, C_538)), A_536, A_536) | k1_waybel_9(A_536, C_538)=B_537 | ~r3_waybel_9(A_536, C_538, B_537) | ~v11_waybel_0(C_538, A_536) | ~l1_waybel_0(C_538, A_536) | ~v7_waybel_0(C_538) | ~v4_orders_2(C_538) | v2_struct_0(C_538) | ~m1_subset_1(B_537, u1_struct_0(A_536)) | ~l1_waybel_9(A_536) | ~v1_compts_1(A_536) | ~v2_lattice3(A_536) | ~v1_lattice3(A_536) | ~v5_orders_2(A_536) | ~v4_orders_2(A_536) | ~v3_orders_2(A_536) | ~v8_pre_topc(A_536) | ~v2_pre_topc(A_536))), inference(cnfTransformation, [status(thm)], [f_271])).
% 5.56/1.99  tff(c_1525, plain, (![C_538, B_537]: (k1_waybel_9('#skF_9', C_538)=B_537 | ~r3_waybel_9('#skF_9', C_538, B_537) | ~v11_waybel_0(C_538, '#skF_9') | ~l1_waybel_0(C_538, '#skF_9') | ~v7_waybel_0(C_538) | ~v4_orders_2(C_538) | v2_struct_0(C_538) | ~m1_subset_1(B_537, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | ~m1_subset_1('#skF_8'('#skF_9', B_537, C_538), u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_62, c_1521])).
% 5.56/1.99  tff(c_1529, plain, (![C_539, B_540]: (k1_waybel_9('#skF_9', C_539)=B_540 | ~r3_waybel_9('#skF_9', C_539, B_540) | ~v11_waybel_0(C_539, '#skF_9') | ~l1_waybel_0(C_539, '#skF_9') | ~v7_waybel_0(C_539) | ~v4_orders_2(C_539) | v2_struct_0(C_539) | ~m1_subset_1(B_540, u1_struct_0('#skF_9')) | ~m1_subset_1('#skF_8'('#skF_9', B_540, C_539), u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_1525])).
% 5.56/1.99  tff(c_1533, plain, (![C_142, B_138]: (k1_waybel_9('#skF_9', C_142)=B_138 | ~r3_waybel_9('#skF_9', C_142, B_138) | ~v11_waybel_0(C_142, '#skF_9') | ~l1_waybel_0(C_142, '#skF_9') | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0('#skF_9')) | ~l1_waybel_9('#skF_9') | ~v1_compts_1('#skF_9') | ~v2_lattice3('#skF_9') | ~v1_lattice3('#skF_9') | ~v5_orders_2('#skF_9') | ~v4_orders_2('#skF_9') | ~v3_orders_2('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9'))), inference(resolution, [status(thm)], [c_48, c_1529])).
% 5.56/1.99  tff(c_1537, plain, (![C_541, B_542]: (k1_waybel_9('#skF_9', C_541)=B_542 | ~r3_waybel_9('#skF_9', C_541, B_542) | ~v11_waybel_0(C_541, '#skF_9') | ~l1_waybel_0(C_541, '#skF_9') | ~v7_waybel_0(C_541) | ~v4_orders_2(C_541) | v2_struct_0(C_541) | ~m1_subset_1(B_542, u1_struct_0('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_68, c_66, c_64, c_1533])).
% 5.56/1.99  tff(c_1546, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_32, c_1537])).
% 5.56/1.99  tff(c_1557, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_111), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_1546])).
% 5.56/1.99  tff(c_1559, plain, (![B_543]: (k1_waybel_9('#skF_9', B_543)='#skF_5'('#skF_9', B_543) | ~v11_waybel_0(B_543, '#skF_9') | ~m1_subset_1('#skF_5'('#skF_9', B_543), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_543, '#skF_9') | ~v7_waybel_0(B_543) | ~v4_orders_2(B_543) | v2_struct_0(B_543))), inference(negUnitSimplification, [status(thm)], [c_1426, c_1557])).
% 5.56/1.99  tff(c_1563, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_34, c_1559])).
% 5.56/1.99  tff(c_1566, plain, (![B_111]: (k1_waybel_9('#skF_9', B_111)='#skF_5'('#skF_9', B_111) | ~v11_waybel_0(B_111, '#skF_9') | ~l1_waybel_0(B_111, '#skF_9') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_1563])).
% 5.56/1.99  tff(c_1568, plain, (![B_544]: (k1_waybel_9('#skF_9', B_544)='#skF_5'('#skF_9', B_544) | ~v11_waybel_0(B_544, '#skF_9') | ~l1_waybel_0(B_544, '#skF_9') | ~v7_waybel_0(B_544) | ~v4_orders_2(B_544) | v2_struct_0(B_544))), inference(negUnitSimplification, [status(thm)], [c_1426, c_1566])).
% 5.56/1.99  tff(c_1571, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10')), inference(resolution, [status(thm)], [c_52, c_1568])).
% 5.56/1.99  tff(c_1574, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10') | v2_struct_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_54, c_1571])).
% 5.56/1.99  tff(c_1575, plain, (k1_waybel_9('#skF_9', '#skF_10')='#skF_5'('#skF_9', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_60, c_1574])).
% 5.56/1.99  tff(c_1380, plain, (~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10')) | v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1104])).
% 5.56/1.99  tff(c_1386, plain, (~r3_waybel_9('#skF_9', '#skF_10', k1_waybel_9('#skF_9', '#skF_10'))), inference(splitLeft, [status(thm)], [c_1380])).
% 5.56/1.99  tff(c_1576, plain, (~r3_waybel_9('#skF_9', '#skF_10', '#skF_5'('#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1575, c_1386])).
% 5.56/1.99  tff(c_1585, plain, (~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v1_compts_1('#skF_9') | ~v8_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_32, c_1576])).
% 5.56/1.99  tff(c_1588, plain, (v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_66, c_90, c_58, c_56, c_54, c_1585])).
% 5.56/1.99  tff(c_1590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1426, c_60, c_1588])).
% 5.56/1.99  tff(c_1591, plain, (v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_1380])).
% 5.56/1.99  tff(c_1603, plain, (~v1_lattice3('#skF_9') | ~l1_orders_2('#skF_9')), inference(resolution, [status(thm)], [c_1591, c_2])).
% 5.56/1.99  tff(c_1607, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_85, c_70, c_1603])).
% 5.56/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/1.99  
% 5.56/1.99  Inference rules
% 5.56/1.99  ----------------------
% 5.56/1.99  #Ref     : 0
% 5.56/1.99  #Sup     : 191
% 5.56/1.99  #Fact    : 26
% 5.56/1.99  #Define  : 0
% 5.56/1.99  #Split   : 13
% 5.56/1.99  #Chain   : 0
% 5.56/1.99  #Close   : 0
% 5.56/1.99  
% 5.56/1.99  Ordering : KBO
% 5.56/1.99  
% 5.56/1.99  Simplification rules
% 5.56/1.99  ----------------------
% 5.56/1.99  #Subsume      : 101
% 5.56/1.99  #Demod        : 816
% 5.56/1.99  #Tautology    : 26
% 5.56/1.99  #SimpNegUnit  : 88
% 5.56/1.99  #BackRed      : 14
% 5.56/1.99  
% 5.56/1.99  #Partial instantiations: 0
% 5.56/1.99  #Strategies tried      : 1
% 5.56/1.99  
% 5.56/1.99  Timing (in seconds)
% 5.56/1.99  ----------------------
% 5.56/2.00  Preprocessing        : 0.41
% 5.56/2.00  Parsing              : 0.22
% 5.56/2.00  CNF conversion       : 0.04
% 5.56/2.00  Main loop            : 0.76
% 5.56/2.00  Inferencing          : 0.33
% 5.56/2.00  Reduction            : 0.21
% 5.56/2.00  Demodulation         : 0.15
% 5.56/2.00  BG Simplification    : 0.04
% 5.56/2.00  Subsumption          : 0.14
% 5.56/2.00  Abstraction          : 0.03
% 5.56/2.00  MUC search           : 0.00
% 5.56/2.00  Cooper               : 0.00
% 5.56/2.00  Total                : 1.26
% 5.56/2.00  Index Insertion      : 0.00
% 5.56/2.00  Index Deletion       : 0.00
% 5.56/2.00  Index Matching       : 0.00
% 5.56/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
