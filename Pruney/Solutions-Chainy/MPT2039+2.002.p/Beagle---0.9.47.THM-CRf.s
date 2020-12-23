%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:22 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :  226 (1825 expanded)
%              Number of leaves         :   54 ( 763 expanded)
%              Depth                    :   29
%              Number of atoms          : 1354 (15610 expanded)
%              Number of equality atoms :   58 ( 171 expanded)
%              Maximal formula depth    :   28 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > r3_waybel_9 > r3_orders_2 > r2_lattice3 > r1_orders_2 > v10_waybel_0 > r2_hidden > r1_yellow_0 > r1_waybel_9 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_compts_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_waybel_1 > k1_yellow_0 > k1_waybel_2 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(r1_waybel_9,type,(
    r1_waybel_9: ( $i * $i ) > $o )).

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

tff(k1_waybel_2,type,(
    k1_waybel_2: ( $i * $i ) > $i )).

tff(l1_waybel_9,type,(
    l1_waybel_9: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_341,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_9)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_waybel_9(A)
     => ( l1_pre_topc(A)
        & l1_orders_2(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_9)).

tff(f_219,axiom,(
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

tff(f_301,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_waybel_9)).

tff(f_47,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

tff(f_259,axiom,(
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

tff(f_143,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_waybel_9)).

tff(f_81,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_193,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_waybel_9)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ( r1_waybel_9(A,B)
          <=> r1_yellow_0(A,k2_relset_1(u1_struct_0(B),u1_struct_0(A),u1_waybel_0(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_waybel_9)).

tff(c_72,plain,(
    l1_waybel_9('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_94,plain,(
    ! [A_148] :
      ( l1_orders_2(A_148)
      | ~ l1_waybel_9(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_98,plain,(
    l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_94])).

tff(c_78,plain,(
    v1_lattice3('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_84,plain,(
    v3_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_88,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_86,plain,(
    v8_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_74,plain,(
    v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_89,plain,(
    ! [A_147] :
      ( l1_pre_topc(A_147)
      | ~ l1_waybel_9(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_93,plain,(
    l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_72,c_89])).

tff(c_40,plain,(
    ! [A_107,B_111] :
      ( r3_waybel_9(A_107,B_111,'#skF_4'(A_107,B_111))
      | ~ l1_waybel_0(B_111,A_107)
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_107)
      | ~ v1_compts_1(A_107)
      | ~ v8_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_82,plain,(
    v4_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_80,plain,(
    v5_orders_2('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_76,plain,(
    v2_lattice3('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_56,plain,(
    ! [A_130,B_138,C_142] :
      ( m1_subset_1('#skF_7'(A_130,B_138,C_142),u1_struct_0(A_130))
      | k1_waybel_2(A_130,C_142) = B_138
      | ~ r3_waybel_9(A_130,C_142,B_138)
      | ~ v10_waybel_0(C_142,A_130)
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
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_70,plain,(
    ! [B_146] :
      ( v5_pre_topc(k4_waybel_1('#skF_8',B_146),'#skF_8','#skF_8')
      | ~ m1_subset_1(B_146,u1_struct_0('#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_1571,plain,(
    ! [A_589,B_590,C_591] :
      ( ~ v5_pre_topc(k4_waybel_1(A_589,'#skF_7'(A_589,B_590,C_591)),A_589,A_589)
      | k1_waybel_2(A_589,C_591) = B_590
      | ~ r3_waybel_9(A_589,C_591,B_590)
      | ~ v10_waybel_0(C_591,A_589)
      | ~ l1_waybel_0(C_591,A_589)
      | ~ v7_waybel_0(C_591)
      | ~ v4_orders_2(C_591)
      | v2_struct_0(C_591)
      | ~ m1_subset_1(B_590,u1_struct_0(A_589))
      | ~ l1_waybel_9(A_589)
      | ~ v1_compts_1(A_589)
      | ~ v2_lattice3(A_589)
      | ~ v1_lattice3(A_589)
      | ~ v5_orders_2(A_589)
      | ~ v4_orders_2(A_589)
      | ~ v3_orders_2(A_589)
      | ~ v8_pre_topc(A_589)
      | ~ v2_pre_topc(A_589) ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_1575,plain,(
    ! [C_591,B_590] :
      ( k1_waybel_2('#skF_8',C_591) = B_590
      | ~ r3_waybel_9('#skF_8',C_591,B_590)
      | ~ v10_waybel_0(C_591,'#skF_8')
      | ~ l1_waybel_0(C_591,'#skF_8')
      | ~ v7_waybel_0(C_591)
      | ~ v4_orders_2(C_591)
      | v2_struct_0(C_591)
      | ~ m1_subset_1(B_590,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_7'('#skF_8',B_590,C_591),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_1571])).

tff(c_1579,plain,(
    ! [C_592,B_593] :
      ( k1_waybel_2('#skF_8',C_592) = B_593
      | ~ r3_waybel_9('#skF_8',C_592,B_593)
      | ~ v10_waybel_0(C_592,'#skF_8')
      | ~ l1_waybel_0(C_592,'#skF_8')
      | ~ v7_waybel_0(C_592)
      | ~ v4_orders_2(C_592)
      | v2_struct_0(C_592)
      | ~ m1_subset_1(B_593,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_7'('#skF_8',B_593,C_592),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_1575])).

tff(c_1583,plain,(
    ! [C_142,B_138] :
      ( k1_waybel_2('#skF_8',C_142) = B_138
      | ~ r3_waybel_9('#skF_8',C_142,B_138)
      | ~ v10_waybel_0(C_142,'#skF_8')
      | ~ l1_waybel_0(C_142,'#skF_8')
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_1579])).

tff(c_1587,plain,(
    ! [C_594,B_595] :
      ( k1_waybel_2('#skF_8',C_594) = B_595
      | ~ r3_waybel_9('#skF_8',C_594,B_595)
      | ~ v10_waybel_0(C_594,'#skF_8')
      | ~ l1_waybel_0(C_594,'#skF_8')
      | ~ v7_waybel_0(C_594)
      | ~ v4_orders_2(C_594)
      | v2_struct_0(C_594)
      | ~ m1_subset_1(B_595,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_1583])).

tff(c_1596,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_111),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_1587])).

tff(c_1605,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_111),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_1596])).

tff(c_1606,plain,(
    v2_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1605])).

tff(c_6,plain,(
    ! [A_4] :
      ( ~ v2_struct_0(A_4)
      | ~ v1_lattice3(A_4)
      | ~ l1_orders_2(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1609,plain,
    ( ~ v1_lattice3('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_1606,c_6])).

tff(c_1613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_78,c_1609])).

tff(c_1615,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1605])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_66,plain,(
    v4_orders_2('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_64,plain,(
    v7_waybel_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_62,plain,(
    l1_waybel_0('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_42,plain,(
    ! [A_107,B_111] :
      ( m1_subset_1('#skF_4'(A_107,B_111),u1_struct_0(A_107))
      | ~ l1_waybel_0(B_111,A_107)
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_107)
      | ~ v1_compts_1(A_107)
      | ~ v8_pre_topc(A_107)
      | ~ v2_pre_topc(A_107)
      | v2_struct_0(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_60,plain,(
    v10_waybel_0('#skF_9','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_1616,plain,(
    ! [B_596] :
      ( k1_waybel_2('#skF_8',B_596) = '#skF_4'('#skF_8',B_596)
      | ~ v10_waybel_0(B_596,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_596),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_596,'#skF_8')
      | ~ v7_waybel_0(B_596)
      | ~ v4_orders_2(B_596)
      | v2_struct_0(B_596) ) ),
    inference(splitRight,[status(thm)],[c_1605])).

tff(c_1620,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_1616])).

tff(c_1623,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_1620])).

tff(c_1629,plain,(
    ! [B_600] :
      ( k1_waybel_2('#skF_8',B_600) = '#skF_4'('#skF_8',B_600)
      | ~ v10_waybel_0(B_600,'#skF_8')
      | ~ l1_waybel_0(B_600,'#skF_8')
      | ~ v7_waybel_0(B_600)
      | ~ v4_orders_2(B_600)
      | v2_struct_0(B_600) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_1623])).

tff(c_1632,plain,
    ( k1_waybel_2('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_1629])).

tff(c_1635,plain,
    ( k1_waybel_2('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1632])).

tff(c_1636,plain,(
    k1_waybel_2('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1635])).

tff(c_1512,plain,(
    ! [A_564,B_565,C_566] :
      ( r3_waybel_9(A_564,B_565,'#skF_6'(A_564,B_565))
      | r2_hidden(C_566,k10_yellow_6(A_564,B_565))
      | ~ r3_waybel_9(A_564,B_565,C_566)
      | ~ m1_subset_1(C_566,u1_struct_0(A_564))
      | ~ l1_waybel_0(B_565,A_564)
      | ~ v7_waybel_0(B_565)
      | ~ v4_orders_2(B_565)
      | v2_struct_0(B_565)
      | ~ l1_pre_topc(A_564)
      | ~ v1_compts_1(A_564)
      | ~ v8_pre_topc(A_564)
      | ~ v2_pre_topc(A_564)
      | v2_struct_0(A_564) ) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_58,plain,
    ( ~ r2_hidden(k1_waybel_2('#skF_8','#skF_9'),k10_yellow_6('#skF_8','#skF_9'))
    | ~ r1_waybel_9('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_341])).

tff(c_101,plain,(
    ~ r1_waybel_9('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_156,plain,(
    ! [A_217,B_218,C_219] :
      ( ~ v5_pre_topc(k4_waybel_1(A_217,'#skF_7'(A_217,B_218,C_219)),A_217,A_217)
      | k1_waybel_2(A_217,C_219) = B_218
      | ~ r3_waybel_9(A_217,C_219,B_218)
      | ~ v10_waybel_0(C_219,A_217)
      | ~ l1_waybel_0(C_219,A_217)
      | ~ v7_waybel_0(C_219)
      | ~ v4_orders_2(C_219)
      | v2_struct_0(C_219)
      | ~ m1_subset_1(B_218,u1_struct_0(A_217))
      | ~ l1_waybel_9(A_217)
      | ~ v1_compts_1(A_217)
      | ~ v2_lattice3(A_217)
      | ~ v1_lattice3(A_217)
      | ~ v5_orders_2(A_217)
      | ~ v4_orders_2(A_217)
      | ~ v3_orders_2(A_217)
      | ~ v8_pre_topc(A_217)
      | ~ v2_pre_topc(A_217) ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_160,plain,(
    ! [C_219,B_218] :
      ( k1_waybel_2('#skF_8',C_219) = B_218
      | ~ r3_waybel_9('#skF_8',C_219,B_218)
      | ~ v10_waybel_0(C_219,'#skF_8')
      | ~ l1_waybel_0(C_219,'#skF_8')
      | ~ v7_waybel_0(C_219)
      | ~ v4_orders_2(C_219)
      | v2_struct_0(C_219)
      | ~ m1_subset_1(B_218,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_7'('#skF_8',B_218,C_219),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_156])).

tff(c_164,plain,(
    ! [C_220,B_221] :
      ( k1_waybel_2('#skF_8',C_220) = B_221
      | ~ r3_waybel_9('#skF_8',C_220,B_221)
      | ~ v10_waybel_0(C_220,'#skF_8')
      | ~ l1_waybel_0(C_220,'#skF_8')
      | ~ v7_waybel_0(C_220)
      | ~ v4_orders_2(C_220)
      | v2_struct_0(C_220)
      | ~ m1_subset_1(B_221,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_7'('#skF_8',B_221,C_220),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_160])).

tff(c_168,plain,(
    ! [C_142,B_138] :
      ( k1_waybel_2('#skF_8',C_142) = B_138
      | ~ r3_waybel_9('#skF_8',C_142,B_138)
      | ~ v10_waybel_0(C_142,'#skF_8')
      | ~ l1_waybel_0(C_142,'#skF_8')
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_164])).

tff(c_172,plain,(
    ! [C_222,B_223] :
      ( k1_waybel_2('#skF_8',C_222) = B_223
      | ~ r3_waybel_9('#skF_8',C_222,B_223)
      | ~ v10_waybel_0(C_222,'#skF_8')
      | ~ l1_waybel_0(C_222,'#skF_8')
      | ~ v7_waybel_0(C_222)
      | ~ v4_orders_2(C_222)
      | v2_struct_0(C_222)
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_168])).

tff(c_181,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_111),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_172])).

tff(c_190,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_111),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_181])).

tff(c_191,plain,(
    v2_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_195,plain,
    ( ~ v1_lattice3('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_191,c_6])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_78,c_195])).

tff(c_201,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_34,plain,(
    ! [A_31,B_47,D_59] :
      ( m1_subset_1('#skF_2'(A_31,B_47,D_59,D_59),u1_struct_0(A_31))
      | r2_lattice3(A_31,k2_relset_1(u1_struct_0(B_47),u1_struct_0(A_31),u1_waybel_0(A_31,B_47)),D_59)
      | ~ r3_waybel_9(A_31,B_47,D_59)
      | ~ v10_waybel_0(B_47,A_31)
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
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_281,plain,(
    ! [A_247,B_248,D_249] :
      ( ~ v5_pre_topc(k4_waybel_1(A_247,'#skF_2'(A_247,B_248,D_249,D_249)),A_247,A_247)
      | r2_lattice3(A_247,k2_relset_1(u1_struct_0(B_248),u1_struct_0(A_247),u1_waybel_0(A_247,B_248)),D_249)
      | ~ r3_waybel_9(A_247,B_248,D_249)
      | ~ v10_waybel_0(B_248,A_247)
      | ~ m1_subset_1(D_249,u1_struct_0(A_247))
      | ~ l1_waybel_0(B_248,A_247)
      | ~ v7_waybel_0(B_248)
      | ~ v4_orders_2(B_248)
      | v2_struct_0(B_248)
      | ~ l1_waybel_9(A_247)
      | ~ v1_compts_1(A_247)
      | ~ v2_lattice3(A_247)
      | ~ v1_lattice3(A_247)
      | ~ v5_orders_2(A_247)
      | ~ v4_orders_2(A_247)
      | ~ v3_orders_2(A_247)
      | ~ v8_pre_topc(A_247)
      | ~ v2_pre_topc(A_247) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_284,plain,(
    ! [B_248,D_249] :
      ( r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_248),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_248)),D_249)
      | ~ r3_waybel_9('#skF_8',B_248,D_249)
      | ~ v10_waybel_0(B_248,'#skF_8')
      | ~ m1_subset_1(D_249,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_248,'#skF_8')
      | ~ v7_waybel_0(B_248)
      | ~ v4_orders_2(B_248)
      | v2_struct_0(B_248)
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_2'('#skF_8',B_248,D_249,D_249),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_281])).

tff(c_288,plain,(
    ! [B_250,D_251] :
      ( r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_250),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_250)),D_251)
      | ~ r3_waybel_9('#skF_8',B_250,D_251)
      | ~ v10_waybel_0(B_250,'#skF_8')
      | ~ m1_subset_1(D_251,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_250,'#skF_8')
      | ~ v7_waybel_0(B_250)
      | ~ v4_orders_2(B_250)
      | v2_struct_0(B_250)
      | ~ m1_subset_1('#skF_2'('#skF_8',B_250,D_251,D_251),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_284])).

tff(c_291,plain,(
    ! [B_47,D_59] :
      ( r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_47),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_47)),D_59)
      | ~ r3_waybel_9('#skF_8',B_47,D_59)
      | ~ v10_waybel_0(B_47,'#skF_8')
      | ~ m1_subset_1(D_59,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_47,'#skF_8')
      | ~ v7_waybel_0(B_47)
      | ~ v4_orders_2(B_47)
      | v2_struct_0(B_47)
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_34,c_288])).

tff(c_294,plain,(
    ! [B_47,D_59] :
      ( r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_47),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_47)),D_59)
      | ~ r3_waybel_9('#skF_8',B_47,D_59)
      | ~ v10_waybel_0(B_47,'#skF_8')
      | ~ m1_subset_1(D_59,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_47,'#skF_8')
      | ~ v7_waybel_0(B_47)
      | ~ v4_orders_2(B_47)
      | v2_struct_0(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_291])).

tff(c_16,plain,(
    ! [A_5,B_17,C_23] :
      ( m1_subset_1('#skF_1'(A_5,B_17,C_23),u1_struct_0(A_5))
      | r1_yellow_0(A_5,C_23)
      | ~ r2_lattice3(A_5,C_23,B_17)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_14,plain,(
    ! [A_5,C_23,B_17] :
      ( r2_lattice3(A_5,C_23,'#skF_1'(A_5,B_17,C_23))
      | r1_yellow_0(A_5,C_23)
      | ~ r2_lattice3(A_5,C_23,B_17)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_300,plain,(
    ! [A_258,B_259,D_260,E_261] :
      ( m1_subset_1('#skF_3'(A_258,B_259,D_260,D_260),u1_struct_0(A_258))
      | r3_orders_2(A_258,D_260,E_261)
      | ~ r2_lattice3(A_258,k2_relset_1(u1_struct_0(B_259),u1_struct_0(A_258),u1_waybel_0(A_258,B_259)),E_261)
      | ~ m1_subset_1(E_261,u1_struct_0(A_258))
      | ~ r3_waybel_9(A_258,B_259,D_260)
      | ~ m1_subset_1(D_260,u1_struct_0(A_258))
      | ~ l1_waybel_0(B_259,A_258)
      | ~ v7_waybel_0(B_259)
      | ~ v4_orders_2(B_259)
      | v2_struct_0(B_259)
      | ~ l1_waybel_9(A_258)
      | ~ v1_compts_1(A_258)
      | ~ v2_lattice3(A_258)
      | ~ v1_lattice3(A_258)
      | ~ v5_orders_2(A_258)
      | ~ v4_orders_2(A_258)
      | ~ v3_orders_2(A_258)
      | ~ v8_pre_topc(A_258)
      | ~ v2_pre_topc(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_835,plain,(
    ! [A_389,B_390,D_391,B_392] :
      ( m1_subset_1('#skF_3'(A_389,B_390,D_391,D_391),u1_struct_0(A_389))
      | r3_orders_2(A_389,D_391,'#skF_1'(A_389,B_392,k2_relset_1(u1_struct_0(B_390),u1_struct_0(A_389),u1_waybel_0(A_389,B_390))))
      | ~ m1_subset_1('#skF_1'(A_389,B_392,k2_relset_1(u1_struct_0(B_390),u1_struct_0(A_389),u1_waybel_0(A_389,B_390))),u1_struct_0(A_389))
      | ~ r3_waybel_9(A_389,B_390,D_391)
      | ~ m1_subset_1(D_391,u1_struct_0(A_389))
      | ~ l1_waybel_0(B_390,A_389)
      | ~ v7_waybel_0(B_390)
      | ~ v4_orders_2(B_390)
      | v2_struct_0(B_390)
      | ~ l1_waybel_9(A_389)
      | ~ v1_compts_1(A_389)
      | ~ v2_lattice3(A_389)
      | ~ v1_lattice3(A_389)
      | ~ v4_orders_2(A_389)
      | ~ v3_orders_2(A_389)
      | ~ v8_pre_topc(A_389)
      | ~ v2_pre_topc(A_389)
      | r1_yellow_0(A_389,k2_relset_1(u1_struct_0(B_390),u1_struct_0(A_389),u1_waybel_0(A_389,B_390)))
      | ~ r2_lattice3(A_389,k2_relset_1(u1_struct_0(B_390),u1_struct_0(A_389),u1_waybel_0(A_389,B_390)),B_392)
      | ~ m1_subset_1(B_392,u1_struct_0(A_389))
      | ~ l1_orders_2(A_389)
      | ~ v5_orders_2(A_389) ) ),
    inference(resolution,[status(thm)],[c_14,c_300])).

tff(c_1198,plain,(
    ! [A_479,B_480,D_481,B_482] :
      ( m1_subset_1('#skF_3'(A_479,B_480,D_481,D_481),u1_struct_0(A_479))
      | r3_orders_2(A_479,D_481,'#skF_1'(A_479,B_482,k2_relset_1(u1_struct_0(B_480),u1_struct_0(A_479),u1_waybel_0(A_479,B_480))))
      | ~ r3_waybel_9(A_479,B_480,D_481)
      | ~ m1_subset_1(D_481,u1_struct_0(A_479))
      | ~ l1_waybel_0(B_480,A_479)
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480)
      | ~ l1_waybel_9(A_479)
      | ~ v1_compts_1(A_479)
      | ~ v2_lattice3(A_479)
      | ~ v1_lattice3(A_479)
      | ~ v4_orders_2(A_479)
      | ~ v3_orders_2(A_479)
      | ~ v8_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | r1_yellow_0(A_479,k2_relset_1(u1_struct_0(B_480),u1_struct_0(A_479),u1_waybel_0(A_479,B_480)))
      | ~ r2_lattice3(A_479,k2_relset_1(u1_struct_0(B_480),u1_struct_0(A_479),u1_waybel_0(A_479,B_480)),B_482)
      | ~ m1_subset_1(B_482,u1_struct_0(A_479))
      | ~ l1_orders_2(A_479)
      | ~ v5_orders_2(A_479) ) ),
    inference(resolution,[status(thm)],[c_16,c_835])).

tff(c_375,plain,(
    ! [A_276,B_277,D_278,E_279] :
      ( ~ v5_pre_topc(k4_waybel_1(A_276,'#skF_3'(A_276,B_277,D_278,D_278)),A_276,A_276)
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
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_378,plain,(
    ! [D_278,E_279,B_277] :
      ( r3_orders_2('#skF_8',D_278,E_279)
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_277),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_277)),E_279)
      | ~ m1_subset_1(E_279,u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8',B_277,D_278)
      | ~ m1_subset_1(D_278,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_277,'#skF_8')
      | ~ v7_waybel_0(B_277)
      | ~ v4_orders_2(B_277)
      | v2_struct_0(B_277)
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_3'('#skF_8',B_277,D_278,D_278),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_375])).

tff(c_382,plain,(
    ! [D_280,E_281,B_282] :
      ( r3_orders_2('#skF_8',D_280,E_281)
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_282)),E_281)
      | ~ m1_subset_1(E_281,u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8',B_282,D_280)
      | ~ m1_subset_1(D_280,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_282,'#skF_8')
      | ~ v7_waybel_0(B_282)
      | ~ v4_orders_2(B_282)
      | v2_struct_0(B_282)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_282,D_280,D_280),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_378])).

tff(c_393,plain,(
    ! [D_280,B_17,B_282] :
      ( r3_orders_2('#skF_8',D_280,'#skF_1'('#skF_8',B_17,k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_282))))
      | ~ m1_subset_1('#skF_1'('#skF_8',B_17,k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_282))),u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8',B_282,D_280)
      | ~ m1_subset_1(D_280,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_282,'#skF_8')
      | ~ v7_waybel_0(B_282)
      | ~ v4_orders_2(B_282)
      | v2_struct_0(B_282)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_282,D_280,D_280),u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_282)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_282),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_282)),B_17)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14,c_382])).

tff(c_498,plain,(
    ! [D_311,B_312,B_313] :
      ( r3_orders_2('#skF_8',D_311,'#skF_1'('#skF_8',B_312,k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313))))
      | ~ m1_subset_1('#skF_1'('#skF_8',B_312,k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313))),u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8',B_313,D_311)
      | ~ m1_subset_1(D_311,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_313,'#skF_8')
      | ~ v7_waybel_0(B_313)
      | ~ v4_orders_2(B_313)
      | v2_struct_0(B_313)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_313,D_311,D_311),u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313)),B_312)
      | ~ m1_subset_1(B_312,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_98,c_393])).

tff(c_504,plain,(
    ! [D_311,B_17,B_313] :
      ( r3_orders_2('#skF_8',D_311,'#skF_1'('#skF_8',B_17,k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313))))
      | ~ r3_waybel_9('#skF_8',B_313,D_311)
      | ~ m1_subset_1(D_311,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_313,'#skF_8')
      | ~ v7_waybel_0(B_313)
      | ~ v4_orders_2(B_313)
      | v2_struct_0(B_313)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_313,D_311,D_311),u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313)),B_17)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_16,c_498])).

tff(c_510,plain,(
    ! [D_311,B_17,B_313] :
      ( r3_orders_2('#skF_8',D_311,'#skF_1'('#skF_8',B_17,k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313))))
      | ~ r3_waybel_9('#skF_8',B_313,D_311)
      | ~ m1_subset_1(D_311,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_313,'#skF_8')
      | ~ v7_waybel_0(B_313)
      | ~ v4_orders_2(B_313)
      | v2_struct_0(B_313)
      | ~ m1_subset_1('#skF_3'('#skF_8',B_313,D_311,D_311),u1_struct_0('#skF_8'))
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_313),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_313)),B_17)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_98,c_504])).

tff(c_1204,plain,(
    ! [D_481,B_17,B_480,B_482] :
      ( r3_orders_2('#skF_8',D_481,'#skF_1'('#skF_8',B_17,k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480))))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480)),B_17)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_8'))
      | r3_orders_2('#skF_8',D_481,'#skF_1'('#skF_8',B_482,k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480))))
      | ~ r3_waybel_9('#skF_8',B_480,D_481)
      | ~ m1_subset_1(D_481,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_480,'#skF_8')
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480)
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480)),B_482)
      | ~ m1_subset_1(B_482,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1198,c_510])).

tff(c_1217,plain,(
    ! [D_481,B_17,B_480,B_482] :
      ( r3_orders_2('#skF_8',D_481,'#skF_1'('#skF_8',B_17,k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480))))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480)),B_17)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_8'))
      | r3_orders_2('#skF_8',D_481,'#skF_1'('#skF_8',B_482,k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480))))
      | ~ r3_waybel_9('#skF_8',B_480,D_481)
      | ~ m1_subset_1(D_481,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_480,'#skF_8')
      | ~ v7_waybel_0(B_480)
      | ~ v4_orders_2(B_480)
      | v2_struct_0(B_480)
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_480),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_480)),B_482)
      | ~ m1_subset_1(B_482,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_98,c_88,c_86,c_84,c_82,c_78,c_76,c_74,c_72,c_1204])).

tff(c_1322,plain,(
    ! [B_499,D_500,B_501] :
      ( ~ r3_waybel_9('#skF_8',B_499,D_500)
      | ~ m1_subset_1(D_500,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_499,'#skF_8')
      | ~ v7_waybel_0(B_499)
      | ~ v4_orders_2(B_499)
      | v2_struct_0(B_499)
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499)),B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_8'))
      | r3_orders_2('#skF_8',D_500,'#skF_1'('#skF_8',B_501,k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499)))) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_1217])).

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

tff(c_1324,plain,(
    ! [D_500,B_501,B_499] :
      ( r1_orders_2('#skF_8',D_500,'#skF_1'('#skF_8',B_501,k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499))))
      | ~ m1_subset_1('#skF_1'('#skF_8',B_501,k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499))),u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8',B_499,D_500)
      | ~ m1_subset_1(D_500,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_499,'#skF_8')
      | ~ v7_waybel_0(B_499)
      | ~ v4_orders_2(B_499)
      | v2_struct_0(B_499)
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499)),B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1322,c_4])).

tff(c_1327,plain,(
    ! [D_500,B_501,B_499] :
      ( r1_orders_2('#skF_8',D_500,'#skF_1'('#skF_8',B_501,k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499))))
      | ~ m1_subset_1('#skF_1'('#skF_8',B_501,k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499))),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8',B_499,D_500)
      | ~ m1_subset_1(D_500,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_499,'#skF_8')
      | ~ v7_waybel_0(B_499)
      | ~ v4_orders_2(B_499)
      | v2_struct_0(B_499)
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_499),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_499)),B_501)
      | ~ m1_subset_1(B_501,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_98,c_1324])).

tff(c_1329,plain,(
    ! [D_502,B_503,B_504] :
      ( r1_orders_2('#skF_8',D_502,'#skF_1'('#skF_8',B_503,k2_relset_1(u1_struct_0(B_504),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_504))))
      | ~ m1_subset_1('#skF_1'('#skF_8',B_503,k2_relset_1(u1_struct_0(B_504),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_504))),u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8',B_504,D_502)
      | ~ m1_subset_1(D_502,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_504,'#skF_8')
      | ~ v7_waybel_0(B_504)
      | ~ v4_orders_2(B_504)
      | v2_struct_0(B_504)
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_504),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_504)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_504),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_504)),B_503)
      | ~ m1_subset_1(B_503,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_1327])).

tff(c_1335,plain,(
    ! [D_502,B_17,B_504] :
      ( r1_orders_2('#skF_8',D_502,'#skF_1'('#skF_8',B_17,k2_relset_1(u1_struct_0(B_504),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_504))))
      | ~ r3_waybel_9('#skF_8',B_504,D_502)
      | ~ m1_subset_1(D_502,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_504,'#skF_8')
      | ~ v7_waybel_0(B_504)
      | ~ v4_orders_2(B_504)
      | v2_struct_0(B_504)
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_504),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_504)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_504),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_504)),B_17)
      | ~ m1_subset_1(B_17,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_16,c_1329])).

tff(c_1342,plain,(
    ! [D_505,B_506,B_507] :
      ( r1_orders_2('#skF_8',D_505,'#skF_1'('#skF_8',B_506,k2_relset_1(u1_struct_0(B_507),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_507))))
      | ~ r3_waybel_9('#skF_8',B_507,D_505)
      | ~ m1_subset_1(D_505,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_507,'#skF_8')
      | ~ v7_waybel_0(B_507)
      | ~ v4_orders_2(B_507)
      | v2_struct_0(B_507)
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_507),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_507)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_507),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_507)),B_506)
      | ~ m1_subset_1(B_506,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_98,c_1335])).

tff(c_12,plain,(
    ! [A_5,B_17,C_23] :
      ( ~ r1_orders_2(A_5,B_17,'#skF_1'(A_5,B_17,C_23))
      | r1_yellow_0(A_5,C_23)
      | ~ r2_lattice3(A_5,C_23,B_17)
      | ~ m1_subset_1(B_17,u1_struct_0(A_5))
      | ~ l1_orders_2(A_5)
      | ~ v5_orders_2(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1350,plain,(
    ! [B_507,B_506] :
      ( ~ l1_orders_2('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ r3_waybel_9('#skF_8',B_507,B_506)
      | ~ l1_waybel_0(B_507,'#skF_8')
      | ~ v7_waybel_0(B_507)
      | ~ v4_orders_2(B_507)
      | v2_struct_0(B_507)
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_507),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_507)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_507),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_507)),B_506)
      | ~ m1_subset_1(B_506,u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_1342,c_12])).

tff(c_1357,plain,(
    ! [B_508,B_509] :
      ( ~ r3_waybel_9('#skF_8',B_508,B_509)
      | ~ l1_waybel_0(B_508,'#skF_8')
      | ~ v7_waybel_0(B_508)
      | ~ v4_orders_2(B_508)
      | v2_struct_0(B_508)
      | r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_508),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_508)))
      | ~ r2_lattice3('#skF_8',k2_relset_1(u1_struct_0(B_508),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_508)),B_509)
      | ~ m1_subset_1(B_509,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_98,c_1350])).

tff(c_1410,plain,(
    ! [B_514,D_515] :
      ( r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_514),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_514)))
      | ~ r3_waybel_9('#skF_8',B_514,D_515)
      | ~ v10_waybel_0(B_514,'#skF_8')
      | ~ m1_subset_1(D_515,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_514,'#skF_8')
      | ~ v7_waybel_0(B_514)
      | ~ v4_orders_2(B_514)
      | v2_struct_0(B_514) ) ),
    inference(resolution,[status(thm)],[c_294,c_1357])).

tff(c_1419,plain,(
    ! [B_111] :
      ( r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_111),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_111)))
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_111),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_1410])).

tff(c_1430,plain,(
    ! [B_111] :
      ( r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_111),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_111)))
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_111),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_1419])).

tff(c_1432,plain,(
    ! [B_516] :
      ( r1_yellow_0('#skF_8',k2_relset_1(u1_struct_0(B_516),u1_struct_0('#skF_8'),u1_waybel_0('#skF_8',B_516)))
      | ~ v10_waybel_0(B_516,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_516),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_516,'#skF_8')
      | ~ v7_waybel_0(B_516)
      | ~ v4_orders_2(B_516)
      | v2_struct_0(B_516) ) ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_1430])).

tff(c_24,plain,(
    ! [A_27,B_29] :
      ( r1_waybel_9(A_27,B_29)
      | ~ r1_yellow_0(A_27,k2_relset_1(u1_struct_0(B_29),u1_struct_0(A_27),u1_waybel_0(A_27,B_29)))
      | ~ l1_waybel_0(B_29,A_27)
      | ~ l1_orders_2(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1435,plain,(
    ! [B_516] :
      ( r1_waybel_9('#skF_8',B_516)
      | ~ l1_orders_2('#skF_8')
      | ~ v10_waybel_0(B_516,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_516),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_516,'#skF_8')
      | ~ v7_waybel_0(B_516)
      | ~ v4_orders_2(B_516)
      | v2_struct_0(B_516) ) ),
    inference(resolution,[status(thm)],[c_1432,c_24])).

tff(c_1439,plain,(
    ! [B_517] :
      ( r1_waybel_9('#skF_8',B_517)
      | ~ v10_waybel_0(B_517,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_517),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_517,'#skF_8')
      | ~ v7_waybel_0(B_517)
      | ~ v4_orders_2(B_517)
      | v2_struct_0(B_517) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1435])).

tff(c_1443,plain,(
    ! [B_111] :
      ( r1_waybel_9('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_1439])).

tff(c_1446,plain,(
    ! [B_111] :
      ( r1_waybel_9('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_1443])).

tff(c_1470,plain,(
    ! [B_522] :
      ( r1_waybel_9('#skF_8',B_522)
      | ~ v10_waybel_0(B_522,'#skF_8')
      | ~ l1_waybel_0(B_522,'#skF_8')
      | ~ v7_waybel_0(B_522)
      | ~ v4_orders_2(B_522)
      | v2_struct_0(B_522) ) ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_1446])).

tff(c_1473,plain,
    ( r1_waybel_9('#skF_8','#skF_9')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_1470])).

tff(c_1476,plain,
    ( r1_waybel_9('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1473])).

tff(c_1478,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_101,c_1476])).

tff(c_1479,plain,(
    ~ r2_hidden(k1_waybel_2('#skF_8','#skF_9'),k10_yellow_6('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1515,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_2('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1512,c_1479])).

tff(c_1518,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_2('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_66,c_64,c_62,c_1515])).

tff(c_1519,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_2('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1518])).

tff(c_1520,plain,(
    ~ m1_subset_1(k1_waybel_2('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_1519])).

tff(c_1637,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1636,c_1520])).

tff(c_1645,plain,
    ( ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_42,c_1637])).

tff(c_1648,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_66,c_64,c_62,c_1645])).

tff(c_1650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1615,c_68,c_1648])).

tff(c_1652,plain,(
    m1_subset_1(k1_waybel_2('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
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

tff(c_1654,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_8',B_2,k1_waybel_2('#skF_8','#skF_9'))
      | ~ r1_orders_2('#skF_8',B_2,k1_waybel_2('#skF_8','#skF_9'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_8'))
      | ~ l1_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1652,c_2])).

tff(c_1657,plain,(
    ! [B_2] :
      ( r3_orders_2('#skF_8',B_2,k1_waybel_2('#skF_8','#skF_9'))
      | ~ r1_orders_2('#skF_8',B_2,k1_waybel_2('#skF_8','#skF_9'))
      | ~ m1_subset_1(B_2,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_98,c_1654])).

tff(c_1659,plain,(
    v2_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1657])).

tff(c_1662,plain,
    ( ~ v1_lattice3('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_1659,c_6])).

tff(c_1666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_78,c_1662])).

tff(c_1668,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1657])).

tff(c_1726,plain,(
    ! [A_624,B_625,C_626] :
      ( ~ v5_pre_topc(k4_waybel_1(A_624,'#skF_7'(A_624,B_625,C_626)),A_624,A_624)
      | k1_waybel_2(A_624,C_626) = B_625
      | ~ r3_waybel_9(A_624,C_626,B_625)
      | ~ v10_waybel_0(C_626,A_624)
      | ~ l1_waybel_0(C_626,A_624)
      | ~ v7_waybel_0(C_626)
      | ~ v4_orders_2(C_626)
      | v2_struct_0(C_626)
      | ~ m1_subset_1(B_625,u1_struct_0(A_624))
      | ~ l1_waybel_9(A_624)
      | ~ v1_compts_1(A_624)
      | ~ v2_lattice3(A_624)
      | ~ v1_lattice3(A_624)
      | ~ v5_orders_2(A_624)
      | ~ v4_orders_2(A_624)
      | ~ v3_orders_2(A_624)
      | ~ v8_pre_topc(A_624)
      | ~ v2_pre_topc(A_624) ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_1730,plain,(
    ! [C_626,B_625] :
      ( k1_waybel_2('#skF_8',C_626) = B_625
      | ~ r3_waybel_9('#skF_8',C_626,B_625)
      | ~ v10_waybel_0(C_626,'#skF_8')
      | ~ l1_waybel_0(C_626,'#skF_8')
      | ~ v7_waybel_0(C_626)
      | ~ v4_orders_2(C_626)
      | v2_struct_0(C_626)
      | ~ m1_subset_1(B_625,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_7'('#skF_8',B_625,C_626),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_1726])).

tff(c_1734,plain,(
    ! [C_627,B_628] :
      ( k1_waybel_2('#skF_8',C_627) = B_628
      | ~ r3_waybel_9('#skF_8',C_627,B_628)
      | ~ v10_waybel_0(C_627,'#skF_8')
      | ~ l1_waybel_0(C_627,'#skF_8')
      | ~ v7_waybel_0(C_627)
      | ~ v4_orders_2(C_627)
      | v2_struct_0(C_627)
      | ~ m1_subset_1(B_628,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_7'('#skF_8',B_628,C_627),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_1730])).

tff(c_1738,plain,(
    ! [C_142,B_138] :
      ( k1_waybel_2('#skF_8',C_142) = B_138
      | ~ r3_waybel_9('#skF_8',C_142,B_138)
      | ~ v10_waybel_0(C_142,'#skF_8')
      | ~ l1_waybel_0(C_142,'#skF_8')
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_1734])).

tff(c_1746,plain,(
    ! [C_632,B_633] :
      ( k1_waybel_2('#skF_8',C_632) = B_633
      | ~ r3_waybel_9('#skF_8',C_632,B_633)
      | ~ v10_waybel_0(C_632,'#skF_8')
      | ~ l1_waybel_0(C_632,'#skF_8')
      | ~ v7_waybel_0(C_632)
      | ~ v4_orders_2(C_632)
      | v2_struct_0(C_632)
      | ~ m1_subset_1(B_633,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_1738])).

tff(c_1755,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_111),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_40,c_1746])).

tff(c_1766,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_111),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_1755])).

tff(c_1768,plain,(
    ! [B_634] :
      ( k1_waybel_2('#skF_8',B_634) = '#skF_4'('#skF_8',B_634)
      | ~ v10_waybel_0(B_634,'#skF_8')
      | ~ m1_subset_1('#skF_4'('#skF_8',B_634),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0(B_634,'#skF_8')
      | ~ v7_waybel_0(B_634)
      | ~ v4_orders_2(B_634)
      | v2_struct_0(B_634) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1668,c_1766])).

tff(c_1772,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_1768])).

tff(c_1775,plain,(
    ! [B_111] :
      ( k1_waybel_2('#skF_8',B_111) = '#skF_4'('#skF_8',B_111)
      | ~ v10_waybel_0(B_111,'#skF_8')
      | ~ l1_waybel_0(B_111,'#skF_8')
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_1772])).

tff(c_1777,plain,(
    ! [B_635] :
      ( k1_waybel_2('#skF_8',B_635) = '#skF_4'('#skF_8',B_635)
      | ~ v10_waybel_0(B_635,'#skF_8')
      | ~ l1_waybel_0(B_635,'#skF_8')
      | ~ v7_waybel_0(B_635)
      | ~ v4_orders_2(B_635)
      | v2_struct_0(B_635) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1668,c_1775])).

tff(c_1780,plain,
    ( k1_waybel_2('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_1777])).

tff(c_1783,plain,
    ( k1_waybel_2('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1780])).

tff(c_1784,plain,(
    k1_waybel_2('#skF_8','#skF_9') = '#skF_4'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1783])).

tff(c_1651,plain,
    ( ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8')
    | r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1519])).

tff(c_1658,plain,(
    ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_1651])).

tff(c_1786,plain,(
    ~ r3_waybel_9('#skF_8','#skF_9','#skF_4'('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1784,c_1658])).

tff(c_1801,plain,
    ( ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_40,c_1786])).

tff(c_1804,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_66,c_64,c_62,c_1801])).

tff(c_1806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1668,c_68,c_1804])).

tff(c_1807,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9'))
    | v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1651])).

tff(c_1809,plain,(
    v2_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1807])).

tff(c_1812,plain,
    ( ~ v1_lattice3('#skF_8')
    | ~ l1_orders_2('#skF_8') ),
    inference(resolution,[status(thm)],[c_1809,c_6])).

tff(c_1816,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_78,c_1812])).

tff(c_1818,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1807])).

tff(c_1808,plain,(
    r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1651])).

tff(c_1852,plain,(
    ! [A_641,B_642,C_643] :
      ( '#skF_6'(A_641,B_642) != '#skF_5'(A_641,B_642)
      | r2_hidden(C_643,k10_yellow_6(A_641,B_642))
      | ~ r3_waybel_9(A_641,B_642,C_643)
      | ~ m1_subset_1(C_643,u1_struct_0(A_641))
      | ~ l1_waybel_0(B_642,A_641)
      | ~ v7_waybel_0(B_642)
      | ~ v4_orders_2(B_642)
      | v2_struct_0(B_642)
      | ~ l1_pre_topc(A_641)
      | ~ v1_compts_1(A_641)
      | ~ v8_pre_topc(A_641)
      | ~ v2_pre_topc(A_641)
      | v2_struct_0(A_641) ) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_1855,plain,
    ( '#skF_6'('#skF_8','#skF_9') != '#skF_5'('#skF_8','#skF_9')
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_2('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1852,c_1479])).

tff(c_1858,plain,
    ( '#skF_6'('#skF_8','#skF_9') != '#skF_5'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_66,c_64,c_62,c_1652,c_1808,c_1855])).

tff(c_1859,plain,(
    '#skF_6'('#skF_8','#skF_9') != '#skF_5'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1818,c_68,c_1858])).

tff(c_1868,plain,(
    ! [A_647,B_648,C_649] :
      ( m1_subset_1('#skF_5'(A_647,B_648),u1_struct_0(A_647))
      | r2_hidden(C_649,k10_yellow_6(A_647,B_648))
      | ~ r3_waybel_9(A_647,B_648,C_649)
      | ~ m1_subset_1(C_649,u1_struct_0(A_647))
      | ~ l1_waybel_0(B_648,A_647)
      | ~ v7_waybel_0(B_648)
      | ~ v4_orders_2(B_648)
      | v2_struct_0(B_648)
      | ~ l1_pre_topc(A_647)
      | ~ v1_compts_1(A_647)
      | ~ v8_pre_topc(A_647)
      | ~ v2_pre_topc(A_647)
      | v2_struct_0(A_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_1873,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_2('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1868,c_1479])).

tff(c_1877,plain,
    ( m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_66,c_64,c_62,c_1652,c_1808,c_1873])).

tff(c_1878,plain,(
    m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1818,c_68,c_1877])).

tff(c_1860,plain,(
    ! [A_644,B_645,C_646] :
      ( r3_waybel_9(A_644,B_645,'#skF_5'(A_644,B_645))
      | r2_hidden(C_646,k10_yellow_6(A_644,B_645))
      | ~ r3_waybel_9(A_644,B_645,C_646)
      | ~ m1_subset_1(C_646,u1_struct_0(A_644))
      | ~ l1_waybel_0(B_645,A_644)
      | ~ v7_waybel_0(B_645)
      | ~ v4_orders_2(B_645)
      | v2_struct_0(B_645)
      | ~ l1_pre_topc(A_644)
      | ~ v1_compts_1(A_644)
      | ~ v8_pre_topc(A_644)
      | ~ v2_pre_topc(A_644)
      | v2_struct_0(A_644) ) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_1863,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_2('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1860,c_1479])).

tff(c_1866,plain,
    ( r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9'))
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_66,c_64,c_62,c_1652,c_1808,c_1863])).

tff(c_1867,plain,(
    r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_1818,c_68,c_1866])).

tff(c_1904,plain,(
    ! [A_661,B_662,C_663] :
      ( ~ v5_pre_topc(k4_waybel_1(A_661,'#skF_7'(A_661,B_662,C_663)),A_661,A_661)
      | k1_waybel_2(A_661,C_663) = B_662
      | ~ r3_waybel_9(A_661,C_663,B_662)
      | ~ v10_waybel_0(C_663,A_661)
      | ~ l1_waybel_0(C_663,A_661)
      | ~ v7_waybel_0(C_663)
      | ~ v4_orders_2(C_663)
      | v2_struct_0(C_663)
      | ~ m1_subset_1(B_662,u1_struct_0(A_661))
      | ~ l1_waybel_9(A_661)
      | ~ v1_compts_1(A_661)
      | ~ v2_lattice3(A_661)
      | ~ v1_lattice3(A_661)
      | ~ v5_orders_2(A_661)
      | ~ v4_orders_2(A_661)
      | ~ v3_orders_2(A_661)
      | ~ v8_pre_topc(A_661)
      | ~ v2_pre_topc(A_661) ) ),
    inference(cnfTransformation,[status(thm)],[f_301])).

tff(c_1908,plain,(
    ! [C_663,B_662] :
      ( k1_waybel_2('#skF_8',C_663) = B_662
      | ~ r3_waybel_9('#skF_8',C_663,B_662)
      | ~ v10_waybel_0(C_663,'#skF_8')
      | ~ l1_waybel_0(C_663,'#skF_8')
      | ~ v7_waybel_0(C_663)
      | ~ v4_orders_2(C_663)
      | v2_struct_0(C_663)
      | ~ m1_subset_1(B_662,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | ~ m1_subset_1('#skF_7'('#skF_8',B_662,C_663),u1_struct_0('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_70,c_1904])).

tff(c_1912,plain,(
    ! [C_664,B_665] :
      ( k1_waybel_2('#skF_8',C_664) = B_665
      | ~ r3_waybel_9('#skF_8',C_664,B_665)
      | ~ v10_waybel_0(C_664,'#skF_8')
      | ~ l1_waybel_0(C_664,'#skF_8')
      | ~ v7_waybel_0(C_664)
      | ~ v4_orders_2(C_664)
      | v2_struct_0(C_664)
      | ~ m1_subset_1(B_665,u1_struct_0('#skF_8'))
      | ~ m1_subset_1('#skF_7'('#skF_8',B_665,C_664),u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_1908])).

tff(c_1916,plain,(
    ! [C_142,B_138] :
      ( k1_waybel_2('#skF_8',C_142) = B_138
      | ~ r3_waybel_9('#skF_8',C_142,B_138)
      | ~ v10_waybel_0(C_142,'#skF_8')
      | ~ l1_waybel_0(C_142,'#skF_8')
      | ~ v7_waybel_0(C_142)
      | ~ v4_orders_2(C_142)
      | v2_struct_0(C_142)
      | ~ m1_subset_1(B_138,u1_struct_0('#skF_8'))
      | ~ l1_waybel_9('#skF_8')
      | ~ v1_compts_1('#skF_8')
      | ~ v2_lattice3('#skF_8')
      | ~ v1_lattice3('#skF_8')
      | ~ v5_orders_2('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | ~ v3_orders_2('#skF_8')
      | ~ v8_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_1912])).

tff(c_1920,plain,(
    ! [C_666,B_667] :
      ( k1_waybel_2('#skF_8',C_666) = B_667
      | ~ r3_waybel_9('#skF_8',C_666,B_667)
      | ~ v10_waybel_0(C_666,'#skF_8')
      | ~ l1_waybel_0(C_666,'#skF_8')
      | ~ v7_waybel_0(C_666)
      | ~ v4_orders_2(C_666)
      | v2_struct_0(C_666)
      | ~ m1_subset_1(B_667,u1_struct_0('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_82,c_80,c_78,c_76,c_74,c_72,c_1916])).

tff(c_1922,plain,
    ( k1_waybel_2('#skF_8','#skF_9') = '#skF_5'('#skF_8','#skF_9')
    | ~ v10_waybel_0('#skF_9','#skF_8')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ m1_subset_1('#skF_5'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1867,c_1920])).

tff(c_1938,plain,
    ( k1_waybel_2('#skF_8','#skF_9') = '#skF_5'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1878,c_66,c_64,c_62,c_60,c_1922])).

tff(c_1939,plain,(
    k1_waybel_2('#skF_8','#skF_9') = '#skF_5'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1938])).

tff(c_1819,plain,(
    ! [A_636,B_637,C_638] :
      ( m1_subset_1('#skF_6'(A_636,B_637),u1_struct_0(A_636))
      | r2_hidden(C_638,k10_yellow_6(A_636,B_637))
      | ~ r3_waybel_9(A_636,B_637,C_638)
      | ~ m1_subset_1(C_638,u1_struct_0(A_636))
      | ~ l1_waybel_0(B_637,A_636)
      | ~ v7_waybel_0(B_637)
      | ~ v4_orders_2(B_637)
      | v2_struct_0(B_637)
      | ~ l1_pre_topc(A_636)
      | ~ v1_compts_1(A_636)
      | ~ v8_pre_topc(A_636)
      | ~ v2_pre_topc(A_636)
      | v2_struct_0(A_636) ) ),
    inference(cnfTransformation,[status(thm)],[f_259])).

tff(c_1824,plain,
    ( m1_subset_1('#skF_6'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ r3_waybel_9('#skF_8','#skF_9',k1_waybel_2('#skF_8','#skF_9'))
    | ~ m1_subset_1(k1_waybel_2('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ l1_pre_topc('#skF_8')
    | ~ v1_compts_1('#skF_8')
    | ~ v8_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1819,c_1479])).

tff(c_1828,plain,
    ( m1_subset_1('#skF_6'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_74,c_93,c_66,c_64,c_62,c_1652,c_1808,c_1824])).

tff(c_1829,plain,
    ( m1_subset_1('#skF_6'('#skF_8','#skF_9'),u1_struct_0('#skF_8'))
    | v2_struct_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1828])).

tff(c_1830,plain,(
    m1_subset_1('#skF_6'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_1818,c_1829])).

tff(c_1817,plain,(
    r3_waybel_9('#skF_8','#skF_9','#skF_6'('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_1807])).

tff(c_1927,plain,
    ( k1_waybel_2('#skF_8','#skF_9') = '#skF_6'('#skF_8','#skF_9')
    | ~ v10_waybel_0('#skF_9','#skF_8')
    | ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ m1_subset_1('#skF_6'('#skF_8','#skF_9'),u1_struct_0('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1817,c_1920])).

tff(c_1946,plain,
    ( k1_waybel_2('#skF_8','#skF_9') = '#skF_6'('#skF_8','#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1830,c_66,c_64,c_62,c_60,c_1927])).

tff(c_1947,plain,(
    k1_waybel_2('#skF_8','#skF_9') = '#skF_6'('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1946])).

tff(c_1975,plain,(
    '#skF_6'('#skF_8','#skF_9') = '#skF_5'('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1939,c_1947])).

tff(c_1976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1859,c_1975])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.11  
% 5.92/2.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.92/2.12  %$ v5_pre_topc > r3_waybel_9 > r3_orders_2 > r2_lattice3 > r1_orders_2 > v10_waybel_0 > r2_hidden > r1_yellow_0 > r1_waybel_9 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_compts_1 > l1_waybel_9 > l1_pre_topc > l1_orders_2 > k2_relset_1 > u1_waybel_0 > k4_waybel_1 > k1_yellow_0 > k1_waybel_2 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_6 > #skF_1 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 5.92/2.12  
% 5.92/2.12  %Foreground sorts:
% 5.92/2.12  
% 5.92/2.12  
% 5.92/2.12  %Background operators:
% 5.92/2.12  
% 5.92/2.12  
% 5.92/2.12  %Foreground operators:
% 5.92/2.12  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.92/2.12  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.92/2.12  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 5.92/2.12  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 5.92/2.12  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 5.92/2.12  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.92/2.12  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.92/2.12  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.92/2.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.92/2.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.92/2.12  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.92/2.12  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 5.92/2.12  tff(v10_waybel_0, type, v10_waybel_0: ($i * $i) > $o).
% 5.92/2.12  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.92/2.12  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.92/2.12  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 5.92/2.12  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 5.92/2.12  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 5.92/2.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.92/2.12  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.92/2.12  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 5.92/2.12  tff('#skF_9', type, '#skF_9': $i).
% 5.92/2.12  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.92/2.12  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 5.92/2.12  tff(r1_waybel_9, type, r1_waybel_9: ($i * $i) > $o).
% 5.92/2.12  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.92/2.12  tff(k4_waybel_1, type, k4_waybel_1: ($i * $i) > $i).
% 5.92/2.12  tff(u1_waybel_0, type, u1_waybel_0: ($i * $i) > $i).
% 5.92/2.12  tff('#skF_8', type, '#skF_8': $i).
% 5.92/2.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.92/2.12  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.92/2.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.92/2.12  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 5.92/2.12  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.92/2.12  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 5.92/2.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.92/2.12  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.92/2.12  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 5.92/2.12  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.92/2.12  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.92/2.12  tff(k1_waybel_2, type, k1_waybel_2: ($i * $i) > $i).
% 5.92/2.12  tff(l1_waybel_9, type, l1_waybel_9: $i > $o).
% 5.92/2.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.92/2.12  
% 6.16/2.15  tff(f_341, negated_conjecture, ~(![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => ((![B]: (m1_subset_1(B, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, B), A, A))) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v10_waybel_0(B, A) => (r1_waybel_9(A, B) & r2_hidden(k1_waybel_2(A, B), k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_waybel_9)).
% 6.16/2.15  tff(f_96, axiom, (![A]: (l1_waybel_9(A) => (l1_pre_topc(A) & l1_orders_2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_waybel_9)).
% 6.16/2.15  tff(f_219, axiom, (![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_waybel_9)).
% 6.16/2.15  tff(f_301, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)) => ((((![D]: (m1_subset_1(D, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, D), A, A))) & v10_waybel_0(C, A)) & r3_waybel_9(A, C, B)) => (B = k1_waybel_2(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_waybel_9)).
% 6.16/2.15  tff(f_47, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 6.16/2.15  tff(f_259, axiom, (![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r3_waybel_9(A, B, C) & r3_waybel_9(A, B, D)) => (C = D)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) => r2_hidden(C, k10_yellow_6(A, B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_waybel_9)).
% 6.16/2.15  tff(f_143, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & v10_waybel_0(B, A)) & r3_waybel_9(A, B, C)) => r2_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l48_waybel_9)).
% 6.16/2.15  tff(f_81, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 6.16/2.15  tff(f_193, axiom, (![A]: (((((((((v2_pre_topc(A) & v8_pre_topc(A)) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & v1_lattice3(A)) & v2_lattice3(A)) & v1_compts_1(A)) & l1_waybel_9(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((((C = D) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => v5_pre_topc(k4_waybel_1(A, E), A, A)))) & r3_waybel_9(A, B, C)) => (![E]: (m1_subset_1(E, u1_struct_0(A)) => (r2_lattice3(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)), E) => r3_orders_2(A, D, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_waybel_9)).
% 6.16/2.15  tff(f_40, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 6.16/2.15  tff(f_90, axiom, (![A]: (l1_orders_2(A) => (![B]: (l1_waybel_0(B, A) => (r1_waybel_9(A, B) <=> r1_yellow_0(A, k2_relset_1(u1_struct_0(B), u1_struct_0(A), u1_waybel_0(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_waybel_9)).
% 6.16/2.15  tff(c_72, plain, (l1_waybel_9('#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_94, plain, (![A_148]: (l1_orders_2(A_148) | ~l1_waybel_9(A_148))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.16/2.15  tff(c_98, plain, (l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_72, c_94])).
% 6.16/2.15  tff(c_78, plain, (v1_lattice3('#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_84, plain, (v3_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_88, plain, (v2_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_86, plain, (v8_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_74, plain, (v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_89, plain, (![A_147]: (l1_pre_topc(A_147) | ~l1_waybel_9(A_147))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.16/2.15  tff(c_93, plain, (l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_72, c_89])).
% 6.16/2.15  tff(c_40, plain, (![A_107, B_111]: (r3_waybel_9(A_107, B_111, '#skF_4'(A_107, B_111)) | ~l1_waybel_0(B_111, A_107) | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_107) | ~v1_compts_1(A_107) | ~v8_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_219])).
% 6.16/2.15  tff(c_82, plain, (v4_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_80, plain, (v5_orders_2('#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_76, plain, (v2_lattice3('#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_56, plain, (![A_130, B_138, C_142]: (m1_subset_1('#skF_7'(A_130, B_138, C_142), u1_struct_0(A_130)) | k1_waybel_2(A_130, C_142)=B_138 | ~r3_waybel_9(A_130, C_142, B_138) | ~v10_waybel_0(C_142, A_130) | ~l1_waybel_0(C_142, A_130) | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0(A_130)) | ~l1_waybel_9(A_130) | ~v1_compts_1(A_130) | ~v2_lattice3(A_130) | ~v1_lattice3(A_130) | ~v5_orders_2(A_130) | ~v4_orders_2(A_130) | ~v3_orders_2(A_130) | ~v8_pre_topc(A_130) | ~v2_pre_topc(A_130))), inference(cnfTransformation, [status(thm)], [f_301])).
% 6.16/2.15  tff(c_70, plain, (![B_146]: (v5_pre_topc(k4_waybel_1('#skF_8', B_146), '#skF_8', '#skF_8') | ~m1_subset_1(B_146, u1_struct_0('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_1571, plain, (![A_589, B_590, C_591]: (~v5_pre_topc(k4_waybel_1(A_589, '#skF_7'(A_589, B_590, C_591)), A_589, A_589) | k1_waybel_2(A_589, C_591)=B_590 | ~r3_waybel_9(A_589, C_591, B_590) | ~v10_waybel_0(C_591, A_589) | ~l1_waybel_0(C_591, A_589) | ~v7_waybel_0(C_591) | ~v4_orders_2(C_591) | v2_struct_0(C_591) | ~m1_subset_1(B_590, u1_struct_0(A_589)) | ~l1_waybel_9(A_589) | ~v1_compts_1(A_589) | ~v2_lattice3(A_589) | ~v1_lattice3(A_589) | ~v5_orders_2(A_589) | ~v4_orders_2(A_589) | ~v3_orders_2(A_589) | ~v8_pre_topc(A_589) | ~v2_pre_topc(A_589))), inference(cnfTransformation, [status(thm)], [f_301])).
% 6.16/2.15  tff(c_1575, plain, (![C_591, B_590]: (k1_waybel_2('#skF_8', C_591)=B_590 | ~r3_waybel_9('#skF_8', C_591, B_590) | ~v10_waybel_0(C_591, '#skF_8') | ~l1_waybel_0(C_591, '#skF_8') | ~v7_waybel_0(C_591) | ~v4_orders_2(C_591) | v2_struct_0(C_591) | ~m1_subset_1(B_590, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_7'('#skF_8', B_590, C_591), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_1571])).
% 6.16/2.15  tff(c_1579, plain, (![C_592, B_593]: (k1_waybel_2('#skF_8', C_592)=B_593 | ~r3_waybel_9('#skF_8', C_592, B_593) | ~v10_waybel_0(C_592, '#skF_8') | ~l1_waybel_0(C_592, '#skF_8') | ~v7_waybel_0(C_592) | ~v4_orders_2(C_592) | v2_struct_0(C_592) | ~m1_subset_1(B_593, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_7'('#skF_8', B_593, C_592), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_1575])).
% 6.16/2.15  tff(c_1583, plain, (![C_142, B_138]: (k1_waybel_2('#skF_8', C_142)=B_138 | ~r3_waybel_9('#skF_8', C_142, B_138) | ~v10_waybel_0(C_142, '#skF_8') | ~l1_waybel_0(C_142, '#skF_8') | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_1579])).
% 6.16/2.15  tff(c_1587, plain, (![C_594, B_595]: (k1_waybel_2('#skF_8', C_594)=B_595 | ~r3_waybel_9('#skF_8', C_594, B_595) | ~v10_waybel_0(C_594, '#skF_8') | ~l1_waybel_0(C_594, '#skF_8') | ~v7_waybel_0(C_594) | ~v4_orders_2(C_594) | v2_struct_0(C_594) | ~m1_subset_1(B_595, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_1583])).
% 6.16/2.15  tff(c_1596, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_111), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_40, c_1587])).
% 6.16/2.15  tff(c_1605, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_111), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_1596])).
% 6.16/2.15  tff(c_1606, plain, (v2_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1605])).
% 6.16/2.15  tff(c_6, plain, (![A_4]: (~v2_struct_0(A_4) | ~v1_lattice3(A_4) | ~l1_orders_2(A_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.16/2.15  tff(c_1609, plain, (~v1_lattice3('#skF_8') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_1606, c_6])).
% 6.16/2.15  tff(c_1613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_78, c_1609])).
% 6.16/2.15  tff(c_1615, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1605])).
% 6.16/2.15  tff(c_68, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_66, plain, (v4_orders_2('#skF_9')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_64, plain, (v7_waybel_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_62, plain, (l1_waybel_0('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_42, plain, (![A_107, B_111]: (m1_subset_1('#skF_4'(A_107, B_111), u1_struct_0(A_107)) | ~l1_waybel_0(B_111, A_107) | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_107) | ~v1_compts_1(A_107) | ~v8_pre_topc(A_107) | ~v2_pre_topc(A_107) | v2_struct_0(A_107))), inference(cnfTransformation, [status(thm)], [f_219])).
% 6.16/2.15  tff(c_60, plain, (v10_waybel_0('#skF_9', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_1616, plain, (![B_596]: (k1_waybel_2('#skF_8', B_596)='#skF_4'('#skF_8', B_596) | ~v10_waybel_0(B_596, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_596), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_596, '#skF_8') | ~v7_waybel_0(B_596) | ~v4_orders_2(B_596) | v2_struct_0(B_596))), inference(splitRight, [status(thm)], [c_1605])).
% 6.16/2.15  tff(c_1620, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_1616])).
% 6.16/2.15  tff(c_1623, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_1620])).
% 6.16/2.15  tff(c_1629, plain, (![B_600]: (k1_waybel_2('#skF_8', B_600)='#skF_4'('#skF_8', B_600) | ~v10_waybel_0(B_600, '#skF_8') | ~l1_waybel_0(B_600, '#skF_8') | ~v7_waybel_0(B_600) | ~v4_orders_2(B_600) | v2_struct_0(B_600))), inference(negUnitSimplification, [status(thm)], [c_1615, c_1623])).
% 6.16/2.15  tff(c_1632, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_60, c_1629])).
% 6.16/2.15  tff(c_1635, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1632])).
% 6.16/2.15  tff(c_1636, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_68, c_1635])).
% 6.16/2.15  tff(c_1512, plain, (![A_564, B_565, C_566]: (r3_waybel_9(A_564, B_565, '#skF_6'(A_564, B_565)) | r2_hidden(C_566, k10_yellow_6(A_564, B_565)) | ~r3_waybel_9(A_564, B_565, C_566) | ~m1_subset_1(C_566, u1_struct_0(A_564)) | ~l1_waybel_0(B_565, A_564) | ~v7_waybel_0(B_565) | ~v4_orders_2(B_565) | v2_struct_0(B_565) | ~l1_pre_topc(A_564) | ~v1_compts_1(A_564) | ~v8_pre_topc(A_564) | ~v2_pre_topc(A_564) | v2_struct_0(A_564))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.16/2.15  tff(c_58, plain, (~r2_hidden(k1_waybel_2('#skF_8', '#skF_9'), k10_yellow_6('#skF_8', '#skF_9')) | ~r1_waybel_9('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_341])).
% 6.16/2.15  tff(c_101, plain, (~r1_waybel_9('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_58])).
% 6.16/2.15  tff(c_156, plain, (![A_217, B_218, C_219]: (~v5_pre_topc(k4_waybel_1(A_217, '#skF_7'(A_217, B_218, C_219)), A_217, A_217) | k1_waybel_2(A_217, C_219)=B_218 | ~r3_waybel_9(A_217, C_219, B_218) | ~v10_waybel_0(C_219, A_217) | ~l1_waybel_0(C_219, A_217) | ~v7_waybel_0(C_219) | ~v4_orders_2(C_219) | v2_struct_0(C_219) | ~m1_subset_1(B_218, u1_struct_0(A_217)) | ~l1_waybel_9(A_217) | ~v1_compts_1(A_217) | ~v2_lattice3(A_217) | ~v1_lattice3(A_217) | ~v5_orders_2(A_217) | ~v4_orders_2(A_217) | ~v3_orders_2(A_217) | ~v8_pre_topc(A_217) | ~v2_pre_topc(A_217))), inference(cnfTransformation, [status(thm)], [f_301])).
% 6.16/2.15  tff(c_160, plain, (![C_219, B_218]: (k1_waybel_2('#skF_8', C_219)=B_218 | ~r3_waybel_9('#skF_8', C_219, B_218) | ~v10_waybel_0(C_219, '#skF_8') | ~l1_waybel_0(C_219, '#skF_8') | ~v7_waybel_0(C_219) | ~v4_orders_2(C_219) | v2_struct_0(C_219) | ~m1_subset_1(B_218, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_7'('#skF_8', B_218, C_219), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_156])).
% 6.16/2.15  tff(c_164, plain, (![C_220, B_221]: (k1_waybel_2('#skF_8', C_220)=B_221 | ~r3_waybel_9('#skF_8', C_220, B_221) | ~v10_waybel_0(C_220, '#skF_8') | ~l1_waybel_0(C_220, '#skF_8') | ~v7_waybel_0(C_220) | ~v4_orders_2(C_220) | v2_struct_0(C_220) | ~m1_subset_1(B_221, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_7'('#skF_8', B_221, C_220), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_160])).
% 6.16/2.15  tff(c_168, plain, (![C_142, B_138]: (k1_waybel_2('#skF_8', C_142)=B_138 | ~r3_waybel_9('#skF_8', C_142, B_138) | ~v10_waybel_0(C_142, '#skF_8') | ~l1_waybel_0(C_142, '#skF_8') | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_164])).
% 6.16/2.15  tff(c_172, plain, (![C_222, B_223]: (k1_waybel_2('#skF_8', C_222)=B_223 | ~r3_waybel_9('#skF_8', C_222, B_223) | ~v10_waybel_0(C_222, '#skF_8') | ~l1_waybel_0(C_222, '#skF_8') | ~v7_waybel_0(C_222) | ~v4_orders_2(C_222) | v2_struct_0(C_222) | ~m1_subset_1(B_223, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_168])).
% 6.16/2.15  tff(c_181, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_111), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_40, c_172])).
% 6.16/2.15  tff(c_190, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_111), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_181])).
% 6.16/2.15  tff(c_191, plain, (v2_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_190])).
% 6.16/2.15  tff(c_195, plain, (~v1_lattice3('#skF_8') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_191, c_6])).
% 6.16/2.15  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_78, c_195])).
% 6.16/2.15  tff(c_201, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_190])).
% 6.16/2.15  tff(c_34, plain, (![A_31, B_47, D_59]: (m1_subset_1('#skF_2'(A_31, B_47, D_59, D_59), u1_struct_0(A_31)) | r2_lattice3(A_31, k2_relset_1(u1_struct_0(B_47), u1_struct_0(A_31), u1_waybel_0(A_31, B_47)), D_59) | ~r3_waybel_9(A_31, B_47, D_59) | ~v10_waybel_0(B_47, A_31) | ~m1_subset_1(D_59, u1_struct_0(A_31)) | ~l1_waybel_0(B_47, A_31) | ~v7_waybel_0(B_47) | ~v4_orders_2(B_47) | v2_struct_0(B_47) | ~l1_waybel_9(A_31) | ~v1_compts_1(A_31) | ~v2_lattice3(A_31) | ~v1_lattice3(A_31) | ~v5_orders_2(A_31) | ~v4_orders_2(A_31) | ~v3_orders_2(A_31) | ~v8_pre_topc(A_31) | ~v2_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.16/2.15  tff(c_281, plain, (![A_247, B_248, D_249]: (~v5_pre_topc(k4_waybel_1(A_247, '#skF_2'(A_247, B_248, D_249, D_249)), A_247, A_247) | r2_lattice3(A_247, k2_relset_1(u1_struct_0(B_248), u1_struct_0(A_247), u1_waybel_0(A_247, B_248)), D_249) | ~r3_waybel_9(A_247, B_248, D_249) | ~v10_waybel_0(B_248, A_247) | ~m1_subset_1(D_249, u1_struct_0(A_247)) | ~l1_waybel_0(B_248, A_247) | ~v7_waybel_0(B_248) | ~v4_orders_2(B_248) | v2_struct_0(B_248) | ~l1_waybel_9(A_247) | ~v1_compts_1(A_247) | ~v2_lattice3(A_247) | ~v1_lattice3(A_247) | ~v5_orders_2(A_247) | ~v4_orders_2(A_247) | ~v3_orders_2(A_247) | ~v8_pre_topc(A_247) | ~v2_pre_topc(A_247))), inference(cnfTransformation, [status(thm)], [f_143])).
% 6.16/2.15  tff(c_284, plain, (![B_248, D_249]: (r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_248), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_248)), D_249) | ~r3_waybel_9('#skF_8', B_248, D_249) | ~v10_waybel_0(B_248, '#skF_8') | ~m1_subset_1(D_249, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_248, '#skF_8') | ~v7_waybel_0(B_248) | ~v4_orders_2(B_248) | v2_struct_0(B_248) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_2'('#skF_8', B_248, D_249, D_249), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_281])).
% 6.16/2.15  tff(c_288, plain, (![B_250, D_251]: (r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_250), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_250)), D_251) | ~r3_waybel_9('#skF_8', B_250, D_251) | ~v10_waybel_0(B_250, '#skF_8') | ~m1_subset_1(D_251, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_250, '#skF_8') | ~v7_waybel_0(B_250) | ~v4_orders_2(B_250) | v2_struct_0(B_250) | ~m1_subset_1('#skF_2'('#skF_8', B_250, D_251, D_251), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_284])).
% 6.16/2.15  tff(c_291, plain, (![B_47, D_59]: (r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_47), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_47)), D_59) | ~r3_waybel_9('#skF_8', B_47, D_59) | ~v10_waybel_0(B_47, '#skF_8') | ~m1_subset_1(D_59, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_47, '#skF_8') | ~v7_waybel_0(B_47) | ~v4_orders_2(B_47) | v2_struct_0(B_47) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_34, c_288])).
% 6.16/2.15  tff(c_294, plain, (![B_47, D_59]: (r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_47), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_47)), D_59) | ~r3_waybel_9('#skF_8', B_47, D_59) | ~v10_waybel_0(B_47, '#skF_8') | ~m1_subset_1(D_59, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_47, '#skF_8') | ~v7_waybel_0(B_47) | ~v4_orders_2(B_47) | v2_struct_0(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_291])).
% 6.16/2.15  tff(c_16, plain, (![A_5, B_17, C_23]: (m1_subset_1('#skF_1'(A_5, B_17, C_23), u1_struct_0(A_5)) | r1_yellow_0(A_5, C_23) | ~r2_lattice3(A_5, C_23, B_17) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.16/2.15  tff(c_14, plain, (![A_5, C_23, B_17]: (r2_lattice3(A_5, C_23, '#skF_1'(A_5, B_17, C_23)) | r1_yellow_0(A_5, C_23) | ~r2_lattice3(A_5, C_23, B_17) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.16/2.15  tff(c_300, plain, (![A_258, B_259, D_260, E_261]: (m1_subset_1('#skF_3'(A_258, B_259, D_260, D_260), u1_struct_0(A_258)) | r3_orders_2(A_258, D_260, E_261) | ~r2_lattice3(A_258, k2_relset_1(u1_struct_0(B_259), u1_struct_0(A_258), u1_waybel_0(A_258, B_259)), E_261) | ~m1_subset_1(E_261, u1_struct_0(A_258)) | ~r3_waybel_9(A_258, B_259, D_260) | ~m1_subset_1(D_260, u1_struct_0(A_258)) | ~l1_waybel_0(B_259, A_258) | ~v7_waybel_0(B_259) | ~v4_orders_2(B_259) | v2_struct_0(B_259) | ~l1_waybel_9(A_258) | ~v1_compts_1(A_258) | ~v2_lattice3(A_258) | ~v1_lattice3(A_258) | ~v5_orders_2(A_258) | ~v4_orders_2(A_258) | ~v3_orders_2(A_258) | ~v8_pre_topc(A_258) | ~v2_pre_topc(A_258))), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.16/2.15  tff(c_835, plain, (![A_389, B_390, D_391, B_392]: (m1_subset_1('#skF_3'(A_389, B_390, D_391, D_391), u1_struct_0(A_389)) | r3_orders_2(A_389, D_391, '#skF_1'(A_389, B_392, k2_relset_1(u1_struct_0(B_390), u1_struct_0(A_389), u1_waybel_0(A_389, B_390)))) | ~m1_subset_1('#skF_1'(A_389, B_392, k2_relset_1(u1_struct_0(B_390), u1_struct_0(A_389), u1_waybel_0(A_389, B_390))), u1_struct_0(A_389)) | ~r3_waybel_9(A_389, B_390, D_391) | ~m1_subset_1(D_391, u1_struct_0(A_389)) | ~l1_waybel_0(B_390, A_389) | ~v7_waybel_0(B_390) | ~v4_orders_2(B_390) | v2_struct_0(B_390) | ~l1_waybel_9(A_389) | ~v1_compts_1(A_389) | ~v2_lattice3(A_389) | ~v1_lattice3(A_389) | ~v4_orders_2(A_389) | ~v3_orders_2(A_389) | ~v8_pre_topc(A_389) | ~v2_pre_topc(A_389) | r1_yellow_0(A_389, k2_relset_1(u1_struct_0(B_390), u1_struct_0(A_389), u1_waybel_0(A_389, B_390))) | ~r2_lattice3(A_389, k2_relset_1(u1_struct_0(B_390), u1_struct_0(A_389), u1_waybel_0(A_389, B_390)), B_392) | ~m1_subset_1(B_392, u1_struct_0(A_389)) | ~l1_orders_2(A_389) | ~v5_orders_2(A_389))), inference(resolution, [status(thm)], [c_14, c_300])).
% 6.16/2.15  tff(c_1198, plain, (![A_479, B_480, D_481, B_482]: (m1_subset_1('#skF_3'(A_479, B_480, D_481, D_481), u1_struct_0(A_479)) | r3_orders_2(A_479, D_481, '#skF_1'(A_479, B_482, k2_relset_1(u1_struct_0(B_480), u1_struct_0(A_479), u1_waybel_0(A_479, B_480)))) | ~r3_waybel_9(A_479, B_480, D_481) | ~m1_subset_1(D_481, u1_struct_0(A_479)) | ~l1_waybel_0(B_480, A_479) | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480) | ~l1_waybel_9(A_479) | ~v1_compts_1(A_479) | ~v2_lattice3(A_479) | ~v1_lattice3(A_479) | ~v4_orders_2(A_479) | ~v3_orders_2(A_479) | ~v8_pre_topc(A_479) | ~v2_pre_topc(A_479) | r1_yellow_0(A_479, k2_relset_1(u1_struct_0(B_480), u1_struct_0(A_479), u1_waybel_0(A_479, B_480))) | ~r2_lattice3(A_479, k2_relset_1(u1_struct_0(B_480), u1_struct_0(A_479), u1_waybel_0(A_479, B_480)), B_482) | ~m1_subset_1(B_482, u1_struct_0(A_479)) | ~l1_orders_2(A_479) | ~v5_orders_2(A_479))), inference(resolution, [status(thm)], [c_16, c_835])).
% 6.16/2.15  tff(c_375, plain, (![A_276, B_277, D_278, E_279]: (~v5_pre_topc(k4_waybel_1(A_276, '#skF_3'(A_276, B_277, D_278, D_278)), A_276, A_276) | r3_orders_2(A_276, D_278, E_279) | ~r2_lattice3(A_276, k2_relset_1(u1_struct_0(B_277), u1_struct_0(A_276), u1_waybel_0(A_276, B_277)), E_279) | ~m1_subset_1(E_279, u1_struct_0(A_276)) | ~r3_waybel_9(A_276, B_277, D_278) | ~m1_subset_1(D_278, u1_struct_0(A_276)) | ~l1_waybel_0(B_277, A_276) | ~v7_waybel_0(B_277) | ~v4_orders_2(B_277) | v2_struct_0(B_277) | ~l1_waybel_9(A_276) | ~v1_compts_1(A_276) | ~v2_lattice3(A_276) | ~v1_lattice3(A_276) | ~v5_orders_2(A_276) | ~v4_orders_2(A_276) | ~v3_orders_2(A_276) | ~v8_pre_topc(A_276) | ~v2_pre_topc(A_276))), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.16/2.15  tff(c_378, plain, (![D_278, E_279, B_277]: (r3_orders_2('#skF_8', D_278, E_279) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_277), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_277)), E_279) | ~m1_subset_1(E_279, u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', B_277, D_278) | ~m1_subset_1(D_278, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_277, '#skF_8') | ~v7_waybel_0(B_277) | ~v4_orders_2(B_277) | v2_struct_0(B_277) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_3'('#skF_8', B_277, D_278, D_278), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_375])).
% 6.16/2.15  tff(c_382, plain, (![D_280, E_281, B_282]: (r3_orders_2('#skF_8', D_280, E_281) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_282)), E_281) | ~m1_subset_1(E_281, u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', B_282, D_280) | ~m1_subset_1(D_280, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_282, '#skF_8') | ~v7_waybel_0(B_282) | ~v4_orders_2(B_282) | v2_struct_0(B_282) | ~m1_subset_1('#skF_3'('#skF_8', B_282, D_280, D_280), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_378])).
% 6.16/2.15  tff(c_393, plain, (![D_280, B_17, B_282]: (r3_orders_2('#skF_8', D_280, '#skF_1'('#skF_8', B_17, k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_282)))) | ~m1_subset_1('#skF_1'('#skF_8', B_17, k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_282))), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', B_282, D_280) | ~m1_subset_1(D_280, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_282, '#skF_8') | ~v7_waybel_0(B_282) | ~v4_orders_2(B_282) | v2_struct_0(B_282) | ~m1_subset_1('#skF_3'('#skF_8', B_282, D_280, D_280), u1_struct_0('#skF_8')) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_282))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_282), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_282)), B_17) | ~m1_subset_1(B_17, u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v5_orders_2('#skF_8'))), inference(resolution, [status(thm)], [c_14, c_382])).
% 6.16/2.15  tff(c_498, plain, (![D_311, B_312, B_313]: (r3_orders_2('#skF_8', D_311, '#skF_1'('#skF_8', B_312, k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313)))) | ~m1_subset_1('#skF_1'('#skF_8', B_312, k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313))), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', B_313, D_311) | ~m1_subset_1(D_311, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_313, '#skF_8') | ~v7_waybel_0(B_313) | ~v4_orders_2(B_313) | v2_struct_0(B_313) | ~m1_subset_1('#skF_3'('#skF_8', B_313, D_311, D_311), u1_struct_0('#skF_8')) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313)), B_312) | ~m1_subset_1(B_312, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_98, c_393])).
% 6.16/2.15  tff(c_504, plain, (![D_311, B_17, B_313]: (r3_orders_2('#skF_8', D_311, '#skF_1'('#skF_8', B_17, k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313)))) | ~r3_waybel_9('#skF_8', B_313, D_311) | ~m1_subset_1(D_311, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_313, '#skF_8') | ~v7_waybel_0(B_313) | ~v4_orders_2(B_313) | v2_struct_0(B_313) | ~m1_subset_1('#skF_3'('#skF_8', B_313, D_311, D_311), u1_struct_0('#skF_8')) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313)), B_17) | ~m1_subset_1(B_17, u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v5_orders_2('#skF_8'))), inference(resolution, [status(thm)], [c_16, c_498])).
% 6.16/2.15  tff(c_510, plain, (![D_311, B_17, B_313]: (r3_orders_2('#skF_8', D_311, '#skF_1'('#skF_8', B_17, k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313)))) | ~r3_waybel_9('#skF_8', B_313, D_311) | ~m1_subset_1(D_311, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_313, '#skF_8') | ~v7_waybel_0(B_313) | ~v4_orders_2(B_313) | v2_struct_0(B_313) | ~m1_subset_1('#skF_3'('#skF_8', B_313, D_311, D_311), u1_struct_0('#skF_8')) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_313), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_313)), B_17) | ~m1_subset_1(B_17, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_98, c_504])).
% 6.16/2.15  tff(c_1204, plain, (![D_481, B_17, B_480, B_482]: (r3_orders_2('#skF_8', D_481, '#skF_1'('#skF_8', B_17, k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480)))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480)), B_17) | ~m1_subset_1(B_17, u1_struct_0('#skF_8')) | r3_orders_2('#skF_8', D_481, '#skF_1'('#skF_8', B_482, k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480)))) | ~r3_waybel_9('#skF_8', B_480, D_481) | ~m1_subset_1(D_481, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_480, '#skF_8') | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480)), B_482) | ~m1_subset_1(B_482, u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v5_orders_2('#skF_8'))), inference(resolution, [status(thm)], [c_1198, c_510])).
% 6.16/2.15  tff(c_1217, plain, (![D_481, B_17, B_480, B_482]: (r3_orders_2('#skF_8', D_481, '#skF_1'('#skF_8', B_17, k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480)))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480)), B_17) | ~m1_subset_1(B_17, u1_struct_0('#skF_8')) | r3_orders_2('#skF_8', D_481, '#skF_1'('#skF_8', B_482, k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480)))) | ~r3_waybel_9('#skF_8', B_480, D_481) | ~m1_subset_1(D_481, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_480, '#skF_8') | ~v7_waybel_0(B_480) | ~v4_orders_2(B_480) | v2_struct_0(B_480) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_480), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_480)), B_482) | ~m1_subset_1(B_482, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_98, c_88, c_86, c_84, c_82, c_78, c_76, c_74, c_72, c_1204])).
% 6.16/2.15  tff(c_1322, plain, (![B_499, D_500, B_501]: (~r3_waybel_9('#skF_8', B_499, D_500) | ~m1_subset_1(D_500, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_499, '#skF_8') | ~v7_waybel_0(B_499) | ~v4_orders_2(B_499) | v2_struct_0(B_499) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499)), B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_8')) | r3_orders_2('#skF_8', D_500, '#skF_1'('#skF_8', B_501, k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499)))))), inference(factorization, [status(thm), theory('equality')], [c_1217])).
% 6.16/2.15  tff(c_4, plain, (![A_1, B_2, C_3]: (r1_orders_2(A_1, B_2, C_3) | ~r3_orders_2(A_1, B_2, C_3) | ~m1_subset_1(C_3, u1_struct_0(A_1)) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.16/2.15  tff(c_1324, plain, (![D_500, B_501, B_499]: (r1_orders_2('#skF_8', D_500, '#skF_1'('#skF_8', B_501, k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499)))) | ~m1_subset_1('#skF_1'('#skF_8', B_501, k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499))), u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', B_499, D_500) | ~m1_subset_1(D_500, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_499, '#skF_8') | ~v7_waybel_0(B_499) | ~v4_orders_2(B_499) | v2_struct_0(B_499) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499)), B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_1322, c_4])).
% 6.16/2.15  tff(c_1327, plain, (![D_500, B_501, B_499]: (r1_orders_2('#skF_8', D_500, '#skF_1'('#skF_8', B_501, k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499)))) | ~m1_subset_1('#skF_1'('#skF_8', B_501, k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499))), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', B_499, D_500) | ~m1_subset_1(D_500, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_499, '#skF_8') | ~v7_waybel_0(B_499) | ~v4_orders_2(B_499) | v2_struct_0(B_499) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_499), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_499)), B_501) | ~m1_subset_1(B_501, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_98, c_1324])).
% 6.16/2.15  tff(c_1329, plain, (![D_502, B_503, B_504]: (r1_orders_2('#skF_8', D_502, '#skF_1'('#skF_8', B_503, k2_relset_1(u1_struct_0(B_504), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_504)))) | ~m1_subset_1('#skF_1'('#skF_8', B_503, k2_relset_1(u1_struct_0(B_504), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_504))), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', B_504, D_502) | ~m1_subset_1(D_502, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_504, '#skF_8') | ~v7_waybel_0(B_504) | ~v4_orders_2(B_504) | v2_struct_0(B_504) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_504), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_504))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_504), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_504)), B_503) | ~m1_subset_1(B_503, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_201, c_1327])).
% 6.16/2.15  tff(c_1335, plain, (![D_502, B_17, B_504]: (r1_orders_2('#skF_8', D_502, '#skF_1'('#skF_8', B_17, k2_relset_1(u1_struct_0(B_504), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_504)))) | ~r3_waybel_9('#skF_8', B_504, D_502) | ~m1_subset_1(D_502, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_504, '#skF_8') | ~v7_waybel_0(B_504) | ~v4_orders_2(B_504) | v2_struct_0(B_504) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_504), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_504))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_504), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_504)), B_17) | ~m1_subset_1(B_17, u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v5_orders_2('#skF_8'))), inference(resolution, [status(thm)], [c_16, c_1329])).
% 6.16/2.15  tff(c_1342, plain, (![D_505, B_506, B_507]: (r1_orders_2('#skF_8', D_505, '#skF_1'('#skF_8', B_506, k2_relset_1(u1_struct_0(B_507), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_507)))) | ~r3_waybel_9('#skF_8', B_507, D_505) | ~m1_subset_1(D_505, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_507, '#skF_8') | ~v7_waybel_0(B_507) | ~v4_orders_2(B_507) | v2_struct_0(B_507) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_507), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_507))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_507), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_507)), B_506) | ~m1_subset_1(B_506, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_98, c_1335])).
% 6.16/2.15  tff(c_12, plain, (![A_5, B_17, C_23]: (~r1_orders_2(A_5, B_17, '#skF_1'(A_5, B_17, C_23)) | r1_yellow_0(A_5, C_23) | ~r2_lattice3(A_5, C_23, B_17) | ~m1_subset_1(B_17, u1_struct_0(A_5)) | ~l1_orders_2(A_5) | ~v5_orders_2(A_5))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.16/2.15  tff(c_1350, plain, (![B_507, B_506]: (~l1_orders_2('#skF_8') | ~v5_orders_2('#skF_8') | ~r3_waybel_9('#skF_8', B_507, B_506) | ~l1_waybel_0(B_507, '#skF_8') | ~v7_waybel_0(B_507) | ~v4_orders_2(B_507) | v2_struct_0(B_507) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_507), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_507))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_507), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_507)), B_506) | ~m1_subset_1(B_506, u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_1342, c_12])).
% 6.16/2.15  tff(c_1357, plain, (![B_508, B_509]: (~r3_waybel_9('#skF_8', B_508, B_509) | ~l1_waybel_0(B_508, '#skF_8') | ~v7_waybel_0(B_508) | ~v4_orders_2(B_508) | v2_struct_0(B_508) | r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_508), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_508))) | ~r2_lattice3('#skF_8', k2_relset_1(u1_struct_0(B_508), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_508)), B_509) | ~m1_subset_1(B_509, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_98, c_1350])).
% 6.16/2.15  tff(c_1410, plain, (![B_514, D_515]: (r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_514), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_514))) | ~r3_waybel_9('#skF_8', B_514, D_515) | ~v10_waybel_0(B_514, '#skF_8') | ~m1_subset_1(D_515, u1_struct_0('#skF_8')) | ~l1_waybel_0(B_514, '#skF_8') | ~v7_waybel_0(B_514) | ~v4_orders_2(B_514) | v2_struct_0(B_514))), inference(resolution, [status(thm)], [c_294, c_1357])).
% 6.16/2.15  tff(c_1419, plain, (![B_111]: (r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_111), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_111))) | ~v10_waybel_0(B_111, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_111), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_40, c_1410])).
% 6.16/2.15  tff(c_1430, plain, (![B_111]: (r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_111), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_111))) | ~v10_waybel_0(B_111, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_111), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_1419])).
% 6.16/2.15  tff(c_1432, plain, (![B_516]: (r1_yellow_0('#skF_8', k2_relset_1(u1_struct_0(B_516), u1_struct_0('#skF_8'), u1_waybel_0('#skF_8', B_516))) | ~v10_waybel_0(B_516, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_516), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_516, '#skF_8') | ~v7_waybel_0(B_516) | ~v4_orders_2(B_516) | v2_struct_0(B_516))), inference(negUnitSimplification, [status(thm)], [c_201, c_1430])).
% 6.16/2.15  tff(c_24, plain, (![A_27, B_29]: (r1_waybel_9(A_27, B_29) | ~r1_yellow_0(A_27, k2_relset_1(u1_struct_0(B_29), u1_struct_0(A_27), u1_waybel_0(A_27, B_29))) | ~l1_waybel_0(B_29, A_27) | ~l1_orders_2(A_27))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.16/2.15  tff(c_1435, plain, (![B_516]: (r1_waybel_9('#skF_8', B_516) | ~l1_orders_2('#skF_8') | ~v10_waybel_0(B_516, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_516), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_516, '#skF_8') | ~v7_waybel_0(B_516) | ~v4_orders_2(B_516) | v2_struct_0(B_516))), inference(resolution, [status(thm)], [c_1432, c_24])).
% 6.16/2.15  tff(c_1439, plain, (![B_517]: (r1_waybel_9('#skF_8', B_517) | ~v10_waybel_0(B_517, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_517), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_517, '#skF_8') | ~v7_waybel_0(B_517) | ~v4_orders_2(B_517) | v2_struct_0(B_517))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1435])).
% 6.16/2.15  tff(c_1443, plain, (![B_111]: (r1_waybel_9('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_1439])).
% 6.16/2.15  tff(c_1446, plain, (![B_111]: (r1_waybel_9('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_1443])).
% 6.16/2.15  tff(c_1470, plain, (![B_522]: (r1_waybel_9('#skF_8', B_522) | ~v10_waybel_0(B_522, '#skF_8') | ~l1_waybel_0(B_522, '#skF_8') | ~v7_waybel_0(B_522) | ~v4_orders_2(B_522) | v2_struct_0(B_522))), inference(negUnitSimplification, [status(thm)], [c_201, c_1446])).
% 6.16/2.15  tff(c_1473, plain, (r1_waybel_9('#skF_8', '#skF_9') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_60, c_1470])).
% 6.16/2.15  tff(c_1476, plain, (r1_waybel_9('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1473])).
% 6.16/2.15  tff(c_1478, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_101, c_1476])).
% 6.16/2.15  tff(c_1479, plain, (~r2_hidden(k1_waybel_2('#skF_8', '#skF_9'), k10_yellow_6('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_58])).
% 6.16/2.15  tff(c_1515, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_2('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1512, c_1479])).
% 6.16/2.15  tff(c_1518, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_2('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_66, c_64, c_62, c_1515])).
% 6.16/2.15  tff(c_1519, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_2('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_68, c_1518])).
% 6.16/2.15  tff(c_1520, plain, (~m1_subset_1(k1_waybel_2('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(splitLeft, [status(thm)], [c_1519])).
% 6.16/2.15  tff(c_1637, plain, (~m1_subset_1('#skF_4'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1636, c_1520])).
% 6.16/2.15  tff(c_1645, plain, (~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_42, c_1637])).
% 6.16/2.15  tff(c_1648, plain, (v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_66, c_64, c_62, c_1645])).
% 6.16/2.15  tff(c_1650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1615, c_68, c_1648])).
% 6.16/2.15  tff(c_1652, plain, (m1_subset_1(k1_waybel_2('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(splitRight, [status(thm)], [c_1519])).
% 6.16/2.15  tff(c_2, plain, (![A_1, B_2, C_3]: (r3_orders_2(A_1, B_2, C_3) | ~r1_orders_2(A_1, B_2, C_3) | ~m1_subset_1(C_3, u1_struct_0(A_1)) | ~m1_subset_1(B_2, u1_struct_0(A_1)) | ~l1_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.16/2.15  tff(c_1654, plain, (![B_2]: (r3_orders_2('#skF_8', B_2, k1_waybel_2('#skF_8', '#skF_9')) | ~r1_orders_2('#skF_8', B_2, k1_waybel_2('#skF_8', '#skF_9')) | ~m1_subset_1(B_2, u1_struct_0('#skF_8')) | ~l1_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1652, c_2])).
% 6.16/2.15  tff(c_1657, plain, (![B_2]: (r3_orders_2('#skF_8', B_2, k1_waybel_2('#skF_8', '#skF_9')) | ~r1_orders_2('#skF_8', B_2, k1_waybel_2('#skF_8', '#skF_9')) | ~m1_subset_1(B_2, u1_struct_0('#skF_8')) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_98, c_1654])).
% 6.16/2.15  tff(c_1659, plain, (v2_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1657])).
% 6.16/2.15  tff(c_1662, plain, (~v1_lattice3('#skF_8') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_1659, c_6])).
% 6.16/2.15  tff(c_1666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_78, c_1662])).
% 6.16/2.15  tff(c_1668, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1657])).
% 6.16/2.15  tff(c_1726, plain, (![A_624, B_625, C_626]: (~v5_pre_topc(k4_waybel_1(A_624, '#skF_7'(A_624, B_625, C_626)), A_624, A_624) | k1_waybel_2(A_624, C_626)=B_625 | ~r3_waybel_9(A_624, C_626, B_625) | ~v10_waybel_0(C_626, A_624) | ~l1_waybel_0(C_626, A_624) | ~v7_waybel_0(C_626) | ~v4_orders_2(C_626) | v2_struct_0(C_626) | ~m1_subset_1(B_625, u1_struct_0(A_624)) | ~l1_waybel_9(A_624) | ~v1_compts_1(A_624) | ~v2_lattice3(A_624) | ~v1_lattice3(A_624) | ~v5_orders_2(A_624) | ~v4_orders_2(A_624) | ~v3_orders_2(A_624) | ~v8_pre_topc(A_624) | ~v2_pre_topc(A_624))), inference(cnfTransformation, [status(thm)], [f_301])).
% 6.16/2.15  tff(c_1730, plain, (![C_626, B_625]: (k1_waybel_2('#skF_8', C_626)=B_625 | ~r3_waybel_9('#skF_8', C_626, B_625) | ~v10_waybel_0(C_626, '#skF_8') | ~l1_waybel_0(C_626, '#skF_8') | ~v7_waybel_0(C_626) | ~v4_orders_2(C_626) | v2_struct_0(C_626) | ~m1_subset_1(B_625, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_7'('#skF_8', B_625, C_626), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_1726])).
% 6.16/2.15  tff(c_1734, plain, (![C_627, B_628]: (k1_waybel_2('#skF_8', C_627)=B_628 | ~r3_waybel_9('#skF_8', C_627, B_628) | ~v10_waybel_0(C_627, '#skF_8') | ~l1_waybel_0(C_627, '#skF_8') | ~v7_waybel_0(C_627) | ~v4_orders_2(C_627) | v2_struct_0(C_627) | ~m1_subset_1(B_628, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_7'('#skF_8', B_628, C_627), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_1730])).
% 6.16/2.15  tff(c_1738, plain, (![C_142, B_138]: (k1_waybel_2('#skF_8', C_142)=B_138 | ~r3_waybel_9('#skF_8', C_142, B_138) | ~v10_waybel_0(C_142, '#skF_8') | ~l1_waybel_0(C_142, '#skF_8') | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_1734])).
% 6.16/2.15  tff(c_1746, plain, (![C_632, B_633]: (k1_waybel_2('#skF_8', C_632)=B_633 | ~r3_waybel_9('#skF_8', C_632, B_633) | ~v10_waybel_0(C_632, '#skF_8') | ~l1_waybel_0(C_632, '#skF_8') | ~v7_waybel_0(C_632) | ~v4_orders_2(C_632) | v2_struct_0(C_632) | ~m1_subset_1(B_633, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_1738])).
% 6.16/2.15  tff(c_1755, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_111), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_40, c_1746])).
% 6.16/2.15  tff(c_1766, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_111), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_1755])).
% 6.16/2.15  tff(c_1768, plain, (![B_634]: (k1_waybel_2('#skF_8', B_634)='#skF_4'('#skF_8', B_634) | ~v10_waybel_0(B_634, '#skF_8') | ~m1_subset_1('#skF_4'('#skF_8', B_634), u1_struct_0('#skF_8')) | ~l1_waybel_0(B_634, '#skF_8') | ~v7_waybel_0(B_634) | ~v4_orders_2(B_634) | v2_struct_0(B_634))), inference(negUnitSimplification, [status(thm)], [c_1668, c_1766])).
% 6.16/2.15  tff(c_1772, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_1768])).
% 6.16/2.15  tff(c_1775, plain, (![B_111]: (k1_waybel_2('#skF_8', B_111)='#skF_4'('#skF_8', B_111) | ~v10_waybel_0(B_111, '#skF_8') | ~l1_waybel_0(B_111, '#skF_8') | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_1772])).
% 6.16/2.15  tff(c_1777, plain, (![B_635]: (k1_waybel_2('#skF_8', B_635)='#skF_4'('#skF_8', B_635) | ~v10_waybel_0(B_635, '#skF_8') | ~l1_waybel_0(B_635, '#skF_8') | ~v7_waybel_0(B_635) | ~v4_orders_2(B_635) | v2_struct_0(B_635))), inference(negUnitSimplification, [status(thm)], [c_1668, c_1775])).
% 6.16/2.15  tff(c_1780, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_60, c_1777])).
% 6.16/2.15  tff(c_1783, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1780])).
% 6.16/2.15  tff(c_1784, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_4'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_68, c_1783])).
% 6.16/2.15  tff(c_1651, plain, (~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9')) | v2_struct_0('#skF_8') | r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_1519])).
% 6.16/2.15  tff(c_1658, plain, (~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_1651])).
% 6.16/2.15  tff(c_1786, plain, (~r3_waybel_9('#skF_8', '#skF_9', '#skF_4'('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1784, c_1658])).
% 6.16/2.15  tff(c_1801, plain, (~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_40, c_1786])).
% 6.16/2.15  tff(c_1804, plain, (v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_66, c_64, c_62, c_1801])).
% 6.16/2.15  tff(c_1806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1668, c_68, c_1804])).
% 6.16/2.15  tff(c_1807, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9')) | v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1651])).
% 6.16/2.15  tff(c_1809, plain, (v2_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1807])).
% 6.16/2.15  tff(c_1812, plain, (~v1_lattice3('#skF_8') | ~l1_orders_2('#skF_8')), inference(resolution, [status(thm)], [c_1809, c_6])).
% 6.16/2.15  tff(c_1816, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_78, c_1812])).
% 6.16/2.15  tff(c_1818, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1807])).
% 6.16/2.15  tff(c_1808, plain, (r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_1651])).
% 6.16/2.15  tff(c_1852, plain, (![A_641, B_642, C_643]: ('#skF_6'(A_641, B_642)!='#skF_5'(A_641, B_642) | r2_hidden(C_643, k10_yellow_6(A_641, B_642)) | ~r3_waybel_9(A_641, B_642, C_643) | ~m1_subset_1(C_643, u1_struct_0(A_641)) | ~l1_waybel_0(B_642, A_641) | ~v7_waybel_0(B_642) | ~v4_orders_2(B_642) | v2_struct_0(B_642) | ~l1_pre_topc(A_641) | ~v1_compts_1(A_641) | ~v8_pre_topc(A_641) | ~v2_pre_topc(A_641) | v2_struct_0(A_641))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.16/2.15  tff(c_1855, plain, ('#skF_6'('#skF_8', '#skF_9')!='#skF_5'('#skF_8', '#skF_9') | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_2('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1852, c_1479])).
% 6.16/2.15  tff(c_1858, plain, ('#skF_6'('#skF_8', '#skF_9')!='#skF_5'('#skF_8', '#skF_9') | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_66, c_64, c_62, c_1652, c_1808, c_1855])).
% 6.16/2.15  tff(c_1859, plain, ('#skF_6'('#skF_8', '#skF_9')!='#skF_5'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_1818, c_68, c_1858])).
% 6.16/2.15  tff(c_1868, plain, (![A_647, B_648, C_649]: (m1_subset_1('#skF_5'(A_647, B_648), u1_struct_0(A_647)) | r2_hidden(C_649, k10_yellow_6(A_647, B_648)) | ~r3_waybel_9(A_647, B_648, C_649) | ~m1_subset_1(C_649, u1_struct_0(A_647)) | ~l1_waybel_0(B_648, A_647) | ~v7_waybel_0(B_648) | ~v4_orders_2(B_648) | v2_struct_0(B_648) | ~l1_pre_topc(A_647) | ~v1_compts_1(A_647) | ~v8_pre_topc(A_647) | ~v2_pre_topc(A_647) | v2_struct_0(A_647))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.16/2.15  tff(c_1873, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_2('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1868, c_1479])).
% 6.16/2.15  tff(c_1877, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_66, c_64, c_62, c_1652, c_1808, c_1873])).
% 6.16/2.15  tff(c_1878, plain, (m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1818, c_68, c_1877])).
% 6.16/2.15  tff(c_1860, plain, (![A_644, B_645, C_646]: (r3_waybel_9(A_644, B_645, '#skF_5'(A_644, B_645)) | r2_hidden(C_646, k10_yellow_6(A_644, B_645)) | ~r3_waybel_9(A_644, B_645, C_646) | ~m1_subset_1(C_646, u1_struct_0(A_644)) | ~l1_waybel_0(B_645, A_644) | ~v7_waybel_0(B_645) | ~v4_orders_2(B_645) | v2_struct_0(B_645) | ~l1_pre_topc(A_644) | ~v1_compts_1(A_644) | ~v8_pre_topc(A_644) | ~v2_pre_topc(A_644) | v2_struct_0(A_644))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.16/2.15  tff(c_1863, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', '#skF_9')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_2('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1860, c_1479])).
% 6.16/2.15  tff(c_1866, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', '#skF_9')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_66, c_64, c_62, c_1652, c_1808, c_1863])).
% 6.16/2.15  tff(c_1867, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_1818, c_68, c_1866])).
% 6.16/2.15  tff(c_1904, plain, (![A_661, B_662, C_663]: (~v5_pre_topc(k4_waybel_1(A_661, '#skF_7'(A_661, B_662, C_663)), A_661, A_661) | k1_waybel_2(A_661, C_663)=B_662 | ~r3_waybel_9(A_661, C_663, B_662) | ~v10_waybel_0(C_663, A_661) | ~l1_waybel_0(C_663, A_661) | ~v7_waybel_0(C_663) | ~v4_orders_2(C_663) | v2_struct_0(C_663) | ~m1_subset_1(B_662, u1_struct_0(A_661)) | ~l1_waybel_9(A_661) | ~v1_compts_1(A_661) | ~v2_lattice3(A_661) | ~v1_lattice3(A_661) | ~v5_orders_2(A_661) | ~v4_orders_2(A_661) | ~v3_orders_2(A_661) | ~v8_pre_topc(A_661) | ~v2_pre_topc(A_661))), inference(cnfTransformation, [status(thm)], [f_301])).
% 6.16/2.15  tff(c_1908, plain, (![C_663, B_662]: (k1_waybel_2('#skF_8', C_663)=B_662 | ~r3_waybel_9('#skF_8', C_663, B_662) | ~v10_waybel_0(C_663, '#skF_8') | ~l1_waybel_0(C_663, '#skF_8') | ~v7_waybel_0(C_663) | ~v4_orders_2(C_663) | v2_struct_0(C_663) | ~m1_subset_1(B_662, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | ~m1_subset_1('#skF_7'('#skF_8', B_662, C_663), u1_struct_0('#skF_8')))), inference(resolution, [status(thm)], [c_70, c_1904])).
% 6.16/2.15  tff(c_1912, plain, (![C_664, B_665]: (k1_waybel_2('#skF_8', C_664)=B_665 | ~r3_waybel_9('#skF_8', C_664, B_665) | ~v10_waybel_0(C_664, '#skF_8') | ~l1_waybel_0(C_664, '#skF_8') | ~v7_waybel_0(C_664) | ~v4_orders_2(C_664) | v2_struct_0(C_664) | ~m1_subset_1(B_665, u1_struct_0('#skF_8')) | ~m1_subset_1('#skF_7'('#skF_8', B_665, C_664), u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_1908])).
% 6.16/2.15  tff(c_1916, plain, (![C_142, B_138]: (k1_waybel_2('#skF_8', C_142)=B_138 | ~r3_waybel_9('#skF_8', C_142, B_138) | ~v10_waybel_0(C_142, '#skF_8') | ~l1_waybel_0(C_142, '#skF_8') | ~v7_waybel_0(C_142) | ~v4_orders_2(C_142) | v2_struct_0(C_142) | ~m1_subset_1(B_138, u1_struct_0('#skF_8')) | ~l1_waybel_9('#skF_8') | ~v1_compts_1('#skF_8') | ~v2_lattice3('#skF_8') | ~v1_lattice3('#skF_8') | ~v5_orders_2('#skF_8') | ~v4_orders_2('#skF_8') | ~v3_orders_2('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_1912])).
% 6.16/2.15  tff(c_1920, plain, (![C_666, B_667]: (k1_waybel_2('#skF_8', C_666)=B_667 | ~r3_waybel_9('#skF_8', C_666, B_667) | ~v10_waybel_0(C_666, '#skF_8') | ~l1_waybel_0(C_666, '#skF_8') | ~v7_waybel_0(C_666) | ~v4_orders_2(C_666) | v2_struct_0(C_666) | ~m1_subset_1(B_667, u1_struct_0('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_82, c_80, c_78, c_76, c_74, c_72, c_1916])).
% 6.16/2.15  tff(c_1922, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_5'('#skF_8', '#skF_9') | ~v10_waybel_0('#skF_9', '#skF_8') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~m1_subset_1('#skF_5'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1867, c_1920])).
% 6.16/2.15  tff(c_1938, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_5'('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1878, c_66, c_64, c_62, c_60, c_1922])).
% 6.16/2.15  tff(c_1939, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_5'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_68, c_1938])).
% 6.16/2.15  tff(c_1819, plain, (![A_636, B_637, C_638]: (m1_subset_1('#skF_6'(A_636, B_637), u1_struct_0(A_636)) | r2_hidden(C_638, k10_yellow_6(A_636, B_637)) | ~r3_waybel_9(A_636, B_637, C_638) | ~m1_subset_1(C_638, u1_struct_0(A_636)) | ~l1_waybel_0(B_637, A_636) | ~v7_waybel_0(B_637) | ~v4_orders_2(B_637) | v2_struct_0(B_637) | ~l1_pre_topc(A_636) | ~v1_compts_1(A_636) | ~v8_pre_topc(A_636) | ~v2_pre_topc(A_636) | v2_struct_0(A_636))), inference(cnfTransformation, [status(thm)], [f_259])).
% 6.16/2.15  tff(c_1824, plain, (m1_subset_1('#skF_6'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', '#skF_9', k1_waybel_2('#skF_8', '#skF_9')) | ~m1_subset_1(k1_waybel_2('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v1_compts_1('#skF_8') | ~v8_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1819, c_1479])).
% 6.16/2.15  tff(c_1828, plain, (m1_subset_1('#skF_6'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_74, c_93, c_66, c_64, c_62, c_1652, c_1808, c_1824])).
% 6.16/2.15  tff(c_1829, plain, (m1_subset_1('#skF_6'('#skF_8', '#skF_9'), u1_struct_0('#skF_8')) | v2_struct_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_68, c_1828])).
% 6.16/2.15  tff(c_1830, plain, (m1_subset_1('#skF_6'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_1818, c_1829])).
% 6.16/2.15  tff(c_1817, plain, (r3_waybel_9('#skF_8', '#skF_9', '#skF_6'('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_1807])).
% 6.16/2.15  tff(c_1927, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_6'('#skF_8', '#skF_9') | ~v10_waybel_0('#skF_9', '#skF_8') | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~m1_subset_1('#skF_6'('#skF_8', '#skF_9'), u1_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1817, c_1920])).
% 6.16/2.15  tff(c_1946, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_6'('#skF_8', '#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1830, c_66, c_64, c_62, c_60, c_1927])).
% 6.16/2.15  tff(c_1947, plain, (k1_waybel_2('#skF_8', '#skF_9')='#skF_6'('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_68, c_1946])).
% 6.16/2.15  tff(c_1975, plain, ('#skF_6'('#skF_8', '#skF_9')='#skF_5'('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1939, c_1947])).
% 6.16/2.15  tff(c_1976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1859, c_1975])).
% 6.16/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.15  
% 6.16/2.15  Inference rules
% 6.16/2.15  ----------------------
% 6.16/2.15  #Ref     : 0
% 6.16/2.15  #Sup     : 258
% 6.16/2.15  #Fact    : 34
% 6.16/2.15  #Define  : 0
% 6.16/2.15  #Split   : 8
% 6.16/2.15  #Chain   : 0
% 6.16/2.15  #Close   : 0
% 6.16/2.15  
% 6.16/2.15  Ordering : KBO
% 6.16/2.15  
% 6.16/2.15  Simplification rules
% 6.16/2.15  ----------------------
% 6.16/2.15  #Subsume      : 133
% 6.16/2.15  #Demod        : 817
% 6.16/2.15  #Tautology    : 35
% 6.16/2.15  #SimpNegUnit  : 136
% 6.16/2.15  #BackRed      : 10
% 6.16/2.15  
% 6.16/2.15  #Partial instantiations: 0
% 6.16/2.15  #Strategies tried      : 1
% 6.16/2.15  
% 6.16/2.15  Timing (in seconds)
% 6.16/2.15  ----------------------
% 6.16/2.16  Preprocessing        : 0.40
% 6.16/2.16  Parsing              : 0.21
% 6.16/2.16  CNF conversion       : 0.04
% 6.16/2.16  Main loop            : 0.94
% 6.16/2.16  Inferencing          : 0.41
% 6.16/2.16  Reduction            : 0.24
% 6.16/2.16  Demodulation         : 0.17
% 6.16/2.16  BG Simplification    : 0.04
% 6.16/2.16  Subsumption          : 0.19
% 6.16/2.16  Abstraction          : 0.04
% 6.16/2.16  MUC search           : 0.00
% 6.16/2.16  Cooper               : 0.00
% 6.16/2.16  Total                : 1.40
% 6.16/2.16  Index Insertion      : 0.00
% 6.16/2.16  Index Deletion       : 0.00
% 6.16/2.16  Index Matching       : 0.00
% 6.16/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
