%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2042+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:47 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  149 (3961 expanded)
%              Number of leaves         :   32 (1715 expanded)
%              Depth                    :   16
%              Number of atoms          :  822 (27269 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_pre_topc > v10_waybel_0 > r2_hidden > r1_waybel_9 > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_waybel_2 > v2_struct_0 > v2_pre_topc > v2_lattice3 > v1_lattice3 > v1_compts_1 > l1_waybel_9 > k4_waybel_1 > k1_waybel_2 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_2 > #skF_1 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v10_waybel_0,type,(
    v10_waybel_0: ( $i * $i ) > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(r1_waybel_9,type,(
    r1_waybel_9: ( $i * $i ) > $o )).

tff(k4_waybel_1,type,(
    k4_waybel_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(v2_waybel_2,type,(
    v2_waybel_2: $i > $o )).

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

tff(f_128,negated_conjecture,(
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
         => v2_waybel_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_waybel_9)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & v8_pre_topc(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & v2_lattice3(A)
        & l1_waybel_9(A) )
     => ( ( ! [B] :
              ( ( ~ v2_struct_0(B)
                & v4_orders_2(B)
                & v7_waybel_0(B)
                & l1_waybel_0(B,A) )
             => ( v10_waybel_0(B,A)
               => ( r1_waybel_9(A,B)
                  & r2_hidden(k1_waybel_2(A,B),k10_yellow_6(A,B)) ) ) )
          & ! [B] :
              ( m1_subset_1(B,u1_struct_0(A))
             => v5_pre_topc(k4_waybel_1(A,B),A,A) ) )
       => v2_waybel_2(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_waybel_9)).

tff(f_102,axiom,(
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

tff(c_34,plain,(
    ~ v2_waybel_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_54,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_52,plain,(
    v8_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_50,plain,(
    v3_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_48,plain,(
    v4_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_46,plain,(
    v5_orders_2('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_44,plain,(
    v1_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_42,plain,(
    v2_lattice3('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    l1_waybel_9('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_24,plain,(
    ! [A_1] :
      ( ~ v2_struct_0('#skF_1'(A_1))
      | m1_subset_1('#skF_2'(A_1),u1_struct_0(A_1))
      | v2_waybel_2(A_1)
      | ~ l1_waybel_9(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | ~ v8_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36,plain,(
    ! [B_9] :
      ( v5_pre_topc(k4_waybel_1('#skF_4',B_9),'#skF_4','#skF_4')
      | ~ m1_subset_1(B_9,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_61,plain,(
    ! [A_16] :
      ( v7_waybel_0('#skF_1'(A_16))
      | ~ v5_pre_topc(k4_waybel_1(A_16,'#skF_2'(A_16)),A_16,A_16)
      | v2_waybel_2(A_16)
      | ~ l1_waybel_9(A_16)
      | ~ v2_lattice3(A_16)
      | ~ v1_lattice3(A_16)
      | ~ v5_orders_2(A_16)
      | ~ v4_orders_2(A_16)
      | ~ v3_orders_2(A_16)
      | ~ v8_pre_topc(A_16)
      | ~ v2_pre_topc(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_65,plain,
    ( v7_waybel_0('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_61])).

tff(c_68,plain,
    ( v7_waybel_0('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_65])).

tff(c_69,plain,
    ( v7_waybel_0('#skF_1'('#skF_4'))
    | ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_68])).

tff(c_70,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_82,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_70])).

tff(c_100,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_82])).

tff(c_101,plain,(
    ~ v2_struct_0('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_100])).

tff(c_22,plain,(
    ! [A_1] :
      ( v4_orders_2('#skF_1'(A_1))
      | m1_subset_1('#skF_2'(A_1),u1_struct_0(A_1))
      | v2_waybel_2(A_1)
      | ~ l1_waybel_9(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | ~ v8_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_85,plain,
    ( v4_orders_2('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_70])).

tff(c_104,plain,
    ( v4_orders_2('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_85])).

tff(c_105,plain,(
    v4_orders_2('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_104])).

tff(c_20,plain,(
    ! [A_1] :
      ( v7_waybel_0('#skF_1'(A_1))
      | m1_subset_1('#skF_2'(A_1),u1_struct_0(A_1))
      | v2_waybel_2(A_1)
      | ~ l1_waybel_9(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | ~ v8_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,
    ( v7_waybel_0('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_70])).

tff(c_96,plain,
    ( v7_waybel_0('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_79])).

tff(c_97,plain,(
    v7_waybel_0('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_96])).

tff(c_18,plain,(
    ! [A_1] :
      ( l1_waybel_0('#skF_1'(A_1),A_1)
      | m1_subset_1('#skF_2'(A_1),u1_struct_0(A_1))
      | v2_waybel_2(A_1)
      | ~ l1_waybel_9(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | ~ v8_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_73,plain,
    ( l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_70])).

tff(c_88,plain,
    ( l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | v2_waybel_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_73])).

tff(c_89,plain,(
    l1_waybel_0('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_88])).

tff(c_16,plain,(
    ! [A_1] :
      ( v10_waybel_0('#skF_1'(A_1),A_1)
      | m1_subset_1('#skF_2'(A_1),u1_struct_0(A_1))
      | v2_waybel_2(A_1)
      | ~ l1_waybel_9(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | ~ v8_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_76,plain,
    ( v10_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_70])).

tff(c_92,plain,
    ( v10_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | v2_waybel_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_76])).

tff(c_93,plain,(
    v10_waybel_0('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_92])).

tff(c_40,plain,(
    v1_compts_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_144,plain,(
    ! [A_23,B_24] :
      ( m1_subset_1('#skF_3'(A_23),u1_struct_0(A_23))
      | r1_waybel_9(A_23,B_24)
      | ~ v10_waybel_0(B_24,A_23)
      | ~ l1_waybel_0(B_24,A_23)
      | ~ v7_waybel_0(B_24)
      | ~ v4_orders_2(B_24)
      | v2_struct_0(B_24)
      | ~ l1_waybel_9(A_23)
      | ~ v1_compts_1(A_23)
      | ~ v2_lattice3(A_23)
      | ~ v1_lattice3(A_23)
      | ~ v5_orders_2(A_23)
      | ~ v4_orders_2(A_23)
      | ~ v3_orders_2(A_23)
      | ~ v8_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_146,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | ~ l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4'))
    | ~ l1_waybel_9('#skF_4')
    | ~ v1_compts_1('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_93,c_144])).

tff(c_149,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_105,c_97,c_89,c_146])).

tff(c_150,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | r1_waybel_9('#skF_4','#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_149])).

tff(c_151,plain,(
    r1_waybel_9('#skF_4','#skF_1'('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_152,plain,(
    ! [A_25,B_26] :
      ( ~ v5_pre_topc(k4_waybel_1(A_25,'#skF_3'(A_25)),A_25,A_25)
      | r1_waybel_9(A_25,B_26)
      | ~ v10_waybel_0(B_26,A_25)
      | ~ l1_waybel_0(B_26,A_25)
      | ~ v7_waybel_0(B_26)
      | ~ v4_orders_2(B_26)
      | v2_struct_0(B_26)
      | ~ l1_waybel_9(A_25)
      | ~ v1_compts_1(A_25)
      | ~ v2_lattice3(A_25)
      | ~ v1_lattice3(A_25)
      | ~ v5_orders_2(A_25)
      | ~ v4_orders_2(A_25)
      | ~ v3_orders_2(A_25)
      | ~ v8_pre_topc(A_25)
      | ~ v2_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_155,plain,(
    ! [B_26] :
      ( r1_waybel_9('#skF_4',B_26)
      | ~ v10_waybel_0(B_26,'#skF_4')
      | ~ l1_waybel_0(B_26,'#skF_4')
      | ~ v7_waybel_0(B_26)
      | ~ v4_orders_2(B_26)
      | v2_struct_0(B_26)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_152])).

tff(c_158,plain,(
    ! [B_26] :
      ( r1_waybel_9('#skF_4',B_26)
      | ~ v10_waybel_0(B_26,'#skF_4')
      | ~ l1_waybel_0(B_26,'#skF_4')
      | ~ v7_waybel_0(B_26)
      | ~ v4_orders_2(B_26)
      | v2_struct_0(B_26)
      | ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_155])).

tff(c_159,plain,(
    ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_160,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1('#skF_3'(A_27),u1_struct_0(A_27))
      | r2_hidden(k1_waybel_2(A_27,B_28),k10_yellow_6(A_27,B_28))
      | ~ v10_waybel_0(B_28,A_27)
      | ~ l1_waybel_0(B_28,A_27)
      | ~ v7_waybel_0(B_28)
      | ~ v4_orders_2(B_28)
      | v2_struct_0(B_28)
      | ~ l1_waybel_9(A_27)
      | ~ v1_compts_1(A_27)
      | ~ v2_lattice3(A_27)
      | ~ v1_lattice3(A_27)
      | ~ v5_orders_2(A_27)
      | ~ v4_orders_2(A_27)
      | ~ v3_orders_2(A_27)
      | ~ v8_pre_topc(A_27)
      | ~ v2_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_14,plain,(
    ! [A_1] :
      ( ~ r2_hidden(k1_waybel_2(A_1,'#skF_1'(A_1)),k10_yellow_6(A_1,'#skF_1'(A_1)))
      | ~ r1_waybel_9(A_1,'#skF_1'(A_1))
      | m1_subset_1('#skF_2'(A_1),u1_struct_0(A_1))
      | v2_waybel_2(A_1)
      | ~ l1_waybel_9(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | ~ v8_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_178,plain,(
    ! [A_31] :
      ( ~ r1_waybel_9(A_31,'#skF_1'(A_31))
      | m1_subset_1('#skF_2'(A_31),u1_struct_0(A_31))
      | v2_waybel_2(A_31)
      | m1_subset_1('#skF_3'(A_31),u1_struct_0(A_31))
      | ~ v10_waybel_0('#skF_1'(A_31),A_31)
      | ~ l1_waybel_0('#skF_1'(A_31),A_31)
      | ~ v7_waybel_0('#skF_1'(A_31))
      | ~ v4_orders_2('#skF_1'(A_31))
      | v2_struct_0('#skF_1'(A_31))
      | ~ l1_waybel_9(A_31)
      | ~ v1_compts_1(A_31)
      | ~ v2_lattice3(A_31)
      | ~ v1_lattice3(A_31)
      | ~ v5_orders_2(A_31)
      | ~ v4_orders_2(A_31)
      | ~ v3_orders_2(A_31)
      | ~ v8_pre_topc(A_31)
      | ~ v2_pre_topc(A_31) ) ),
    inference(resolution,[status(thm)],[c_160,c_14])).

tff(c_181,plain,
    ( ~ r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4')
    | m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v10_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4'))
    | ~ l1_waybel_9('#skF_4')
    | ~ v1_compts_1('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_178,c_70])).

tff(c_184,plain,
    ( v2_waybel_2('#skF_4')
    | m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_105,c_97,c_89,c_93,c_151,c_181])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_159,c_34,c_184])).

tff(c_188,plain,(
    m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_208,plain,(
    ! [A_35,B_36] :
      ( ~ v5_pre_topc(k4_waybel_1(A_35,'#skF_3'(A_35)),A_35,A_35)
      | r2_hidden(k1_waybel_2(A_35,B_36),k10_yellow_6(A_35,B_36))
      | ~ v10_waybel_0(B_36,A_35)
      | ~ l1_waybel_0(B_36,A_35)
      | ~ v7_waybel_0(B_36)
      | ~ v4_orders_2(B_36)
      | v2_struct_0(B_36)
      | ~ l1_waybel_9(A_35)
      | ~ v1_compts_1(A_35)
      | ~ v2_lattice3(A_35)
      | ~ v1_lattice3(A_35)
      | ~ v5_orders_2(A_35)
      | ~ v4_orders_2(A_35)
      | ~ v3_orders_2(A_35)
      | ~ v8_pre_topc(A_35)
      | ~ v2_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_211,plain,(
    ! [B_36] :
      ( r2_hidden(k1_waybel_2('#skF_4',B_36),k10_yellow_6('#skF_4',B_36))
      | ~ v10_waybel_0(B_36,'#skF_4')
      | ~ l1_waybel_0(B_36,'#skF_4')
      | ~ v7_waybel_0(B_36)
      | ~ v4_orders_2(B_36)
      | v2_struct_0(B_36)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_208])).

tff(c_215,plain,(
    ! [B_37] :
      ( r2_hidden(k1_waybel_2('#skF_4',B_37),k10_yellow_6('#skF_4',B_37))
      | ~ v10_waybel_0(B_37,'#skF_4')
      | ~ l1_waybel_0(B_37,'#skF_4')
      | ~ v7_waybel_0(B_37)
      | ~ v4_orders_2(B_37)
      | v2_struct_0(B_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_211])).

tff(c_223,plain,
    ( ~ r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4'))
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ v10_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_215,c_14])).

tff(c_230,plain,
    ( m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4'))
    | v2_waybel_2('#skF_4')
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_97,c_89,c_93,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_151,c_223])).

tff(c_232,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_34,c_70,c_230])).

tff(c_234,plain,(
    ~ r1_waybel_9('#skF_4','#skF_1'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_233,plain,(
    m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_235,plain,(
    ! [A_38,B_39] :
      ( ~ v5_pre_topc(k4_waybel_1(A_38,'#skF_3'(A_38)),A_38,A_38)
      | r1_waybel_9(A_38,B_39)
      | ~ v10_waybel_0(B_39,A_38)
      | ~ l1_waybel_0(B_39,A_38)
      | ~ v7_waybel_0(B_39)
      | ~ v4_orders_2(B_39)
      | v2_struct_0(B_39)
      | ~ l1_waybel_9(A_38)
      | ~ v1_compts_1(A_38)
      | ~ v2_lattice3(A_38)
      | ~ v1_lattice3(A_38)
      | ~ v5_orders_2(A_38)
      | ~ v4_orders_2(A_38)
      | ~ v3_orders_2(A_38)
      | ~ v8_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_238,plain,(
    ! [B_39] :
      ( r1_waybel_9('#skF_4',B_39)
      | ~ v10_waybel_0(B_39,'#skF_4')
      | ~ l1_waybel_0(B_39,'#skF_4')
      | ~ v7_waybel_0(B_39)
      | ~ v4_orders_2(B_39)
      | v2_struct_0(B_39)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_235])).

tff(c_241,plain,(
    ! [B_39] :
      ( r1_waybel_9('#skF_4',B_39)
      | ~ v10_waybel_0(B_39,'#skF_4')
      | ~ l1_waybel_0(B_39,'#skF_4')
      | ~ v7_waybel_0(B_39)
      | ~ v4_orders_2(B_39)
      | v2_struct_0(B_39)
      | ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_238])).

tff(c_244,plain,(
    ! [B_40] :
      ( r1_waybel_9('#skF_4',B_40)
      | ~ v10_waybel_0(B_40,'#skF_4')
      | ~ l1_waybel_0(B_40,'#skF_4')
      | ~ v7_waybel_0(B_40)
      | ~ v4_orders_2(B_40)
      | v2_struct_0(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_241])).

tff(c_247,plain,
    ( r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | ~ l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_93,c_244])).

tff(c_250,plain,
    ( r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_97,c_89,c_247])).

tff(c_252,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_234,c_250])).

tff(c_254,plain,(
    m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_264,plain,(
    ! [A_42] :
      ( ~ v2_struct_0('#skF_1'(A_42))
      | ~ v5_pre_topc(k4_waybel_1(A_42,'#skF_2'(A_42)),A_42,A_42)
      | v2_waybel_2(A_42)
      | ~ l1_waybel_9(A_42)
      | ~ v2_lattice3(A_42)
      | ~ v1_lattice3(A_42)
      | ~ v5_orders_2(A_42)
      | ~ v4_orders_2(A_42)
      | ~ v3_orders_2(A_42)
      | ~ v8_pre_topc(A_42)
      | ~ v2_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_268,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_264])).

tff(c_271,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_268])).

tff(c_272,plain,(
    ~ v2_struct_0('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_271])).

tff(c_255,plain,(
    ! [A_41] :
      ( v4_orders_2('#skF_1'(A_41))
      | ~ v5_pre_topc(k4_waybel_1(A_41,'#skF_2'(A_41)),A_41,A_41)
      | v2_waybel_2(A_41)
      | ~ l1_waybel_9(A_41)
      | ~ v2_lattice3(A_41)
      | ~ v1_lattice3(A_41)
      | ~ v5_orders_2(A_41)
      | ~ v4_orders_2(A_41)
      | ~ v3_orders_2(A_41)
      | ~ v8_pre_topc(A_41)
      | ~ v2_pre_topc(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_259,plain,
    ( v4_orders_2('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_255])).

tff(c_262,plain,
    ( v4_orders_2('#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_259])).

tff(c_263,plain,(
    v4_orders_2('#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_262])).

tff(c_253,plain,(
    v7_waybel_0('#skF_1'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_282,plain,(
    ! [A_44] :
      ( l1_waybel_0('#skF_1'(A_44),A_44)
      | ~ v5_pre_topc(k4_waybel_1(A_44,'#skF_2'(A_44)),A_44,A_44)
      | v2_waybel_2(A_44)
      | ~ l1_waybel_9(A_44)
      | ~ v2_lattice3(A_44)
      | ~ v1_lattice3(A_44)
      | ~ v5_orders_2(A_44)
      | ~ v4_orders_2(A_44)
      | ~ v3_orders_2(A_44)
      | ~ v8_pre_topc(A_44)
      | ~ v2_pre_topc(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_286,plain,
    ( l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_282])).

tff(c_289,plain,
    ( l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | v2_waybel_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_286])).

tff(c_290,plain,(
    l1_waybel_0('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_289])).

tff(c_273,plain,(
    ! [A_43] :
      ( v10_waybel_0('#skF_1'(A_43),A_43)
      | ~ v5_pre_topc(k4_waybel_1(A_43,'#skF_2'(A_43)),A_43,A_43)
      | v2_waybel_2(A_43)
      | ~ l1_waybel_9(A_43)
      | ~ v2_lattice3(A_43)
      | ~ v1_lattice3(A_43)
      | ~ v5_orders_2(A_43)
      | ~ v4_orders_2(A_43)
      | ~ v3_orders_2(A_43)
      | ~ v8_pre_topc(A_43)
      | ~ v2_pre_topc(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_277,plain,
    ( v10_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_273])).

tff(c_280,plain,
    ( v10_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | v2_waybel_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_277])).

tff(c_281,plain,(
    v10_waybel_0('#skF_1'('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_280])).

tff(c_293,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1('#skF_3'(A_47),u1_struct_0(A_47))
      | r1_waybel_9(A_47,B_48)
      | ~ v10_waybel_0(B_48,A_47)
      | ~ l1_waybel_0(B_48,A_47)
      | ~ v7_waybel_0(B_48)
      | ~ v4_orders_2(B_48)
      | v2_struct_0(B_48)
      | ~ l1_waybel_9(A_47)
      | ~ v1_compts_1(A_47)
      | ~ v2_lattice3(A_47)
      | ~ v1_lattice3(A_47)
      | ~ v5_orders_2(A_47)
      | ~ v4_orders_2(A_47)
      | ~ v3_orders_2(A_47)
      | ~ v8_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_295,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | ~ l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4'))
    | ~ l1_waybel_9('#skF_4')
    | ~ v1_compts_1('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_281,c_293])).

tff(c_298,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_263,c_253,c_290,c_295])).

tff(c_299,plain,
    ( m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | r1_waybel_9('#skF_4','#skF_1'('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_298])).

tff(c_300,plain,(
    r1_waybel_9('#skF_4','#skF_1'('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_301,plain,(
    ! [A_49,B_50] :
      ( ~ v5_pre_topc(k4_waybel_1(A_49,'#skF_3'(A_49)),A_49,A_49)
      | r1_waybel_9(A_49,B_50)
      | ~ v10_waybel_0(B_50,A_49)
      | ~ l1_waybel_0(B_50,A_49)
      | ~ v7_waybel_0(B_50)
      | ~ v4_orders_2(B_50)
      | v2_struct_0(B_50)
      | ~ l1_waybel_9(A_49)
      | ~ v1_compts_1(A_49)
      | ~ v2_lattice3(A_49)
      | ~ v1_lattice3(A_49)
      | ~ v5_orders_2(A_49)
      | ~ v4_orders_2(A_49)
      | ~ v3_orders_2(A_49)
      | ~ v8_pre_topc(A_49)
      | ~ v2_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_304,plain,(
    ! [B_50] :
      ( r1_waybel_9('#skF_4',B_50)
      | ~ v10_waybel_0(B_50,'#skF_4')
      | ~ l1_waybel_0(B_50,'#skF_4')
      | ~ v7_waybel_0(B_50)
      | ~ v4_orders_2(B_50)
      | v2_struct_0(B_50)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_301])).

tff(c_307,plain,(
    ! [B_50] :
      ( r1_waybel_9('#skF_4',B_50)
      | ~ v10_waybel_0(B_50,'#skF_4')
      | ~ l1_waybel_0(B_50,'#skF_4')
      | ~ v7_waybel_0(B_50)
      | ~ v4_orders_2(B_50)
      | v2_struct_0(B_50)
      | ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_304])).

tff(c_308,plain,(
    ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_307])).

tff(c_309,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1('#skF_3'(A_51),u1_struct_0(A_51))
      | r2_hidden(k1_waybel_2(A_51,B_52),k10_yellow_6(A_51,B_52))
      | ~ v10_waybel_0(B_52,A_51)
      | ~ l1_waybel_0(B_52,A_51)
      | ~ v7_waybel_0(B_52)
      | ~ v4_orders_2(B_52)
      | v2_struct_0(B_52)
      | ~ l1_waybel_9(A_51)
      | ~ v1_compts_1(A_51)
      | ~ v2_lattice3(A_51)
      | ~ v1_lattice3(A_51)
      | ~ v5_orders_2(A_51)
      | ~ v4_orders_2(A_51)
      | ~ v3_orders_2(A_51)
      | ~ v8_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ r2_hidden(k1_waybel_2(A_1,'#skF_1'(A_1)),k10_yellow_6(A_1,'#skF_1'(A_1)))
      | ~ r1_waybel_9(A_1,'#skF_1'(A_1))
      | ~ v5_pre_topc(k4_waybel_1(A_1,'#skF_2'(A_1)),A_1,A_1)
      | v2_waybel_2(A_1)
      | ~ l1_waybel_9(A_1)
      | ~ v2_lattice3(A_1)
      | ~ v1_lattice3(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | ~ v8_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_328,plain,(
    ! [A_56] :
      ( ~ r1_waybel_9(A_56,'#skF_1'(A_56))
      | ~ v5_pre_topc(k4_waybel_1(A_56,'#skF_2'(A_56)),A_56,A_56)
      | v2_waybel_2(A_56)
      | m1_subset_1('#skF_3'(A_56),u1_struct_0(A_56))
      | ~ v10_waybel_0('#skF_1'(A_56),A_56)
      | ~ l1_waybel_0('#skF_1'(A_56),A_56)
      | ~ v7_waybel_0('#skF_1'(A_56))
      | ~ v4_orders_2('#skF_1'(A_56))
      | v2_struct_0('#skF_1'(A_56))
      | ~ l1_waybel_9(A_56)
      | ~ v1_compts_1(A_56)
      | ~ v2_lattice3(A_56)
      | ~ v1_lattice3(A_56)
      | ~ v5_orders_2(A_56)
      | ~ v4_orders_2(A_56)
      | ~ v3_orders_2(A_56)
      | ~ v8_pre_topc(A_56)
      | ~ v2_pre_topc(A_56) ) ),
    inference(resolution,[status(thm)],[c_309,c_2])).

tff(c_332,plain,
    ( ~ r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | v2_waybel_2('#skF_4')
    | m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | ~ v10_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4'))
    | ~ l1_waybel_9('#skF_4')
    | ~ v1_compts_1('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_328])).

tff(c_335,plain,
    ( v2_waybel_2('#skF_4')
    | m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_263,c_253,c_290,c_281,c_300,c_332])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_308,c_34,c_335])).

tff(c_339,plain,(
    m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_307])).

tff(c_359,plain,(
    ! [A_60,B_61] :
      ( ~ v5_pre_topc(k4_waybel_1(A_60,'#skF_3'(A_60)),A_60,A_60)
      | r2_hidden(k1_waybel_2(A_60,B_61),k10_yellow_6(A_60,B_61))
      | ~ v10_waybel_0(B_61,A_60)
      | ~ l1_waybel_0(B_61,A_60)
      | ~ v7_waybel_0(B_61)
      | ~ v4_orders_2(B_61)
      | v2_struct_0(B_61)
      | ~ l1_waybel_9(A_60)
      | ~ v1_compts_1(A_60)
      | ~ v2_lattice3(A_60)
      | ~ v1_lattice3(A_60)
      | ~ v5_orders_2(A_60)
      | ~ v4_orders_2(A_60)
      | ~ v3_orders_2(A_60)
      | ~ v8_pre_topc(A_60)
      | ~ v2_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_362,plain,(
    ! [B_61] :
      ( r2_hidden(k1_waybel_2('#skF_4',B_61),k10_yellow_6('#skF_4',B_61))
      | ~ v10_waybel_0(B_61,'#skF_4')
      | ~ l1_waybel_0(B_61,'#skF_4')
      | ~ v7_waybel_0(B_61)
      | ~ v4_orders_2(B_61)
      | v2_struct_0(B_61)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_359])).

tff(c_366,plain,(
    ! [B_62] :
      ( r2_hidden(k1_waybel_2('#skF_4',B_62),k10_yellow_6('#skF_4',B_62))
      | ~ v10_waybel_0(B_62,'#skF_4')
      | ~ l1_waybel_0(B_62,'#skF_4')
      | ~ v7_waybel_0(B_62)
      | ~ v4_orders_2(B_62)
      | v2_struct_0(B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_362])).

tff(c_370,plain,
    ( ~ r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | ~ v5_pre_topc(k4_waybel_1('#skF_4','#skF_2'('#skF_4')),'#skF_4','#skF_4')
    | v2_waybel_2('#skF_4')
    | ~ l1_waybel_9('#skF_4')
    | ~ v2_lattice3('#skF_4')
    | ~ v1_lattice3('#skF_4')
    | ~ v5_orders_2('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | ~ v3_orders_2('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ v10_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_366,c_2])).

tff(c_377,plain,
    ( ~ v5_pre_topc(k4_waybel_1('#skF_4','#skF_2'('#skF_4')),'#skF_4','#skF_4')
    | v2_waybel_2('#skF_4')
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_253,c_290,c_281,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_38,c_300,c_370])).

tff(c_378,plain,(
    ~ v5_pre_topc(k4_waybel_1('#skF_4','#skF_2'('#skF_4')),'#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_34,c_377])).

tff(c_386,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_36,c_378])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_386])).

tff(c_392,plain,(
    ~ r1_waybel_9('#skF_4','#skF_1'('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_391,plain,(
    m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_393,plain,(
    ! [A_64,B_65] :
      ( ~ v5_pre_topc(k4_waybel_1(A_64,'#skF_3'(A_64)),A_64,A_64)
      | r1_waybel_9(A_64,B_65)
      | ~ v10_waybel_0(B_65,A_64)
      | ~ l1_waybel_0(B_65,A_64)
      | ~ v7_waybel_0(B_65)
      | ~ v4_orders_2(B_65)
      | v2_struct_0(B_65)
      | ~ l1_waybel_9(A_64)
      | ~ v1_compts_1(A_64)
      | ~ v2_lattice3(A_64)
      | ~ v1_lattice3(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | ~ v8_pre_topc(A_64)
      | ~ v2_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_396,plain,(
    ! [B_65] :
      ( r1_waybel_9('#skF_4',B_65)
      | ~ v10_waybel_0(B_65,'#skF_4')
      | ~ l1_waybel_0(B_65,'#skF_4')
      | ~ v7_waybel_0(B_65)
      | ~ v4_orders_2(B_65)
      | v2_struct_0(B_65)
      | ~ l1_waybel_9('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v2_lattice3('#skF_4')
      | ~ v1_lattice3('#skF_4')
      | ~ v5_orders_2('#skF_4')
      | ~ v4_orders_2('#skF_4')
      | ~ v3_orders_2('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ m1_subset_1('#skF_3'('#skF_4'),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_36,c_393])).

tff(c_400,plain,(
    ! [B_66] :
      ( r1_waybel_9('#skF_4',B_66)
      | ~ v10_waybel_0(B_66,'#skF_4')
      | ~ l1_waybel_0(B_66,'#skF_4')
      | ~ v7_waybel_0(B_66)
      | ~ v4_orders_2(B_66)
      | v2_struct_0(B_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_54,c_52,c_50,c_48,c_46,c_44,c_42,c_40,c_38,c_396])).

tff(c_403,plain,
    ( r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | ~ l1_waybel_0('#skF_1'('#skF_4'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4'))
    | ~ v4_orders_2('#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(resolution,[status(thm)],[c_281,c_400])).

tff(c_406,plain,
    ( r1_waybel_9('#skF_4','#skF_1'('#skF_4'))
    | v2_struct_0('#skF_1'('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_253,c_290,c_403])).

tff(c_408,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_272,c_392,c_406])).

%------------------------------------------------------------------------------
