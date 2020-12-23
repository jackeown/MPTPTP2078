%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:55 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 101 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  287 ( 527 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > o_2_6_yellow_6 > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff(k4_yellow_6,type,(
    k4_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v3_yellow_6,type,(
    v3_yellow_6: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(o_2_6_yellow_6,type,(
    o_2_6_yellow_6: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v1_yellow_6,type,(
    v1_yellow_6: ( $i * $i ) > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k11_yellow_6,type,(
    k11_yellow_6: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_186,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v8_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & v1_yellow_6(B,A)
              & l1_waybel_0(B,A) )
           => k11_yellow_6(A,B) = k4_yellow_6(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_yellow_6)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_waybel_0(B,A)
         => ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & v1_yellow_6(B,A) )
           => ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & v3_yellow_6(B,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_yellow_6)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & v1_yellow_6(B,A)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_6_yellow_6(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_2_6_yellow_6)).

tff(f_141,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & v1_yellow_6(B,A)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(B))
             => k2_waybel_0(A,B,C) = k4_yellow_6(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_6)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_162,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & v1_yellow_6(B,A)
            & l1_waybel_0(B,A) )
         => r2_hidden(k4_yellow_6(A,B),k10_yellow_6(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_6)).

tff(f_99,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v8_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & v3_yellow_6(B,A)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( C = k11_yellow_6(A,B)
              <=> r2_hidden(C,k10_yellow_6(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_yellow_6)).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_24,plain,(
    k4_yellow_6('#skF_1','#skF_2') != k11_yellow_6('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_26,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_38,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_28,plain,(
    v1_yellow_6('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_32,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_30,plain,(
    v7_waybel_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_186])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v3_yellow_6(B_7,A_5)
      | ~ v1_yellow_6(B_7,A_5)
      | ~ v7_waybel_0(B_7)
      | ~ v4_orders_2(B_7)
      | v2_struct_0(B_7)
      | ~ l1_waybel_0(B_7,A_5)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(o_2_6_yellow_6(A_15,B_16),u1_struct_0(B_16))
      | ~ l1_waybel_0(B_16,A_15)
      | ~ v1_yellow_6(B_16,A_15)
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_48,plain,(
    ! [A_38,B_39,C_40] :
      ( k2_waybel_0(A_38,B_39,C_40) = k4_yellow_6(A_38,B_39)
      | ~ m1_subset_1(C_40,u1_struct_0(B_39))
      | ~ l1_waybel_0(B_39,A_38)
      | ~ v1_yellow_6(B_39,A_38)
      | ~ v7_waybel_0(B_39)
      | ~ v4_orders_2(B_39)
      | v2_struct_0(B_39)
      | ~ l1_struct_0(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_67,plain,(
    ! [A_48,B_49,A_50] :
      ( k2_waybel_0(A_48,B_49,o_2_6_yellow_6(A_50,B_49)) = k4_yellow_6(A_48,B_49)
      | ~ l1_waybel_0(B_49,A_48)
      | ~ v1_yellow_6(B_49,A_48)
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48)
      | ~ l1_waybel_0(B_49,A_50)
      | ~ v1_yellow_6(B_49,A_50)
      | ~ v7_waybel_0(B_49)
      | ~ v4_orders_2(B_49)
      | v2_struct_0(B_49)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50)
      | v2_struct_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_4,plain,(
    ! [A_2,B_3,C_4] :
      ( m1_subset_1(k2_waybel_0(A_2,B_3,C_4),u1_struct_0(A_2))
      | ~ m1_subset_1(C_4,u1_struct_0(B_3))
      | ~ l1_waybel_0(B_3,A_2)
      | v2_struct_0(B_3)
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [A_60,B_61,A_62] :
      ( m1_subset_1(k4_yellow_6(A_60,B_61),u1_struct_0(A_60))
      | ~ m1_subset_1(o_2_6_yellow_6(A_62,B_61),u1_struct_0(B_61))
      | ~ l1_waybel_0(B_61,A_60)
      | v2_struct_0(B_61)
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60)
      | ~ l1_waybel_0(B_61,A_60)
      | ~ v1_yellow_6(B_61,A_60)
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60)
      | ~ l1_waybel_0(B_61,A_62)
      | ~ v1_yellow_6(B_61,A_62)
      | ~ v7_waybel_0(B_61)
      | ~ v4_orders_2(B_61)
      | v2_struct_0(B_61)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_4])).

tff(c_117,plain,(
    ! [A_63,B_64,A_65] :
      ( m1_subset_1(k4_yellow_6(A_63,B_64),u1_struct_0(A_63))
      | ~ l1_waybel_0(B_64,A_63)
      | ~ v1_yellow_6(B_64,A_63)
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63)
      | ~ l1_waybel_0(B_64,A_65)
      | ~ v1_yellow_6(B_64,A_65)
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_18,c_113])).

tff(c_119,plain,(
    ! [A_63] :
      ( m1_subset_1(k4_yellow_6(A_63,'#skF_2'),u1_struct_0(A_63))
      | ~ l1_waybel_0('#skF_2',A_63)
      | ~ v1_yellow_6('#skF_2',A_63)
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63)
      | ~ l1_waybel_0('#skF_2','#skF_1')
      | ~ v7_waybel_0('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_117])).

tff(c_122,plain,(
    ! [A_63] :
      ( m1_subset_1(k4_yellow_6(A_63,'#skF_2'),u1_struct_0(A_63))
      | ~ l1_waybel_0('#skF_2',A_63)
      | ~ v1_yellow_6('#skF_2',A_63)
      | ~ l1_struct_0(A_63)
      | v2_struct_0(A_63)
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_32,c_30,c_26,c_119])).

tff(c_124,plain,(
    ! [A_66] :
      ( m1_subset_1(k4_yellow_6(A_66,'#skF_2'),u1_struct_0(A_66))
      | ~ l1_waybel_0('#skF_2',A_66)
      | ~ v1_yellow_6('#skF_2',A_66)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34,c_122])).

tff(c_22,plain,(
    ! [A_24,B_26] :
      ( r2_hidden(k4_yellow_6(A_24,B_26),k10_yellow_6(A_24,B_26))
      | ~ l1_waybel_0(B_26,A_24)
      | ~ v1_yellow_6(B_26,A_24)
      | ~ v7_waybel_0(B_26)
      | ~ v4_orders_2(B_26)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    ! [A_43,B_44,C_45] :
      ( k11_yellow_6(A_43,B_44) = C_45
      | ~ r2_hidden(C_45,k10_yellow_6(A_43,B_44))
      | ~ m1_subset_1(C_45,u1_struct_0(A_43))
      | ~ l1_waybel_0(B_44,A_43)
      | ~ v3_yellow_6(B_44,A_43)
      | ~ v7_waybel_0(B_44)
      | ~ v4_orders_2(B_44)
      | v2_struct_0(B_44)
      | ~ l1_pre_topc(A_43)
      | ~ v8_pre_topc(A_43)
      | ~ v2_pre_topc(A_43)
      | v2_struct_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_65,plain,(
    ! [A_24,B_26] :
      ( k4_yellow_6(A_24,B_26) = k11_yellow_6(A_24,B_26)
      | ~ m1_subset_1(k4_yellow_6(A_24,B_26),u1_struct_0(A_24))
      | ~ v3_yellow_6(B_26,A_24)
      | ~ v8_pre_topc(A_24)
      | ~ l1_waybel_0(B_26,A_24)
      | ~ v1_yellow_6(B_26,A_24)
      | ~ v7_waybel_0(B_26)
      | ~ v4_orders_2(B_26)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_129,plain,(
    ! [A_66] :
      ( k4_yellow_6(A_66,'#skF_2') = k11_yellow_6(A_66,'#skF_2')
      | ~ v3_yellow_6('#skF_2',A_66)
      | ~ v8_pre_topc(A_66)
      | ~ v7_waybel_0('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | ~ l1_waybel_0('#skF_2',A_66)
      | ~ v1_yellow_6('#skF_2',A_66)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_124,c_65])).

tff(c_135,plain,(
    ! [A_66] :
      ( k4_yellow_6(A_66,'#skF_2') = k11_yellow_6(A_66,'#skF_2')
      | ~ v3_yellow_6('#skF_2',A_66)
      | ~ v8_pre_topc(A_66)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | ~ l1_waybel_0('#skF_2',A_66)
      | ~ v1_yellow_6('#skF_2',A_66)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_129])).

tff(c_159,plain,(
    ! [A_71] :
      ( k4_yellow_6(A_71,'#skF_2') = k11_yellow_6(A_71,'#skF_2')
      | ~ v3_yellow_6('#skF_2',A_71)
      | ~ v8_pre_topc(A_71)
      | ~ l1_pre_topc(A_71)
      | ~ v2_pre_topc(A_71)
      | ~ l1_waybel_0('#skF_2',A_71)
      | ~ v1_yellow_6('#skF_2',A_71)
      | ~ l1_struct_0(A_71)
      | v2_struct_0(A_71) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_135])).

tff(c_163,plain,(
    ! [A_5] :
      ( k4_yellow_6(A_5,'#skF_2') = k11_yellow_6(A_5,'#skF_2')
      | ~ v8_pre_topc(A_5)
      | ~ l1_struct_0(A_5)
      | ~ v1_yellow_6('#skF_2',A_5)
      | ~ v7_waybel_0('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_waybel_0('#skF_2',A_5)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_159])).

tff(c_166,plain,(
    ! [A_5] :
      ( k4_yellow_6(A_5,'#skF_2') = k11_yellow_6(A_5,'#skF_2')
      | ~ v8_pre_topc(A_5)
      | ~ l1_struct_0(A_5)
      | ~ v1_yellow_6('#skF_2',A_5)
      | v2_struct_0('#skF_2')
      | ~ l1_waybel_0('#skF_2',A_5)
      | ~ l1_pre_topc(A_5)
      | ~ v2_pre_topc(A_5)
      | v2_struct_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_163])).

tff(c_168,plain,(
    ! [A_72] :
      ( k4_yellow_6(A_72,'#skF_2') = k11_yellow_6(A_72,'#skF_2')
      | ~ v8_pre_topc(A_72)
      | ~ l1_struct_0(A_72)
      | ~ v1_yellow_6('#skF_2',A_72)
      | ~ l1_waybel_0('#skF_2',A_72)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_166])).

tff(c_171,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_168])).

tff(c_174,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_26,c_38,c_171])).

tff(c_175,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_24,c_174])).

tff(c_178,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_175])).

tff(c_182,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.43  
% 2.55/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.43  %$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > o_2_6_yellow_6 > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 2.55/1.43  
% 2.55/1.43  %Foreground sorts:
% 2.55/1.43  
% 2.55/1.43  
% 2.55/1.43  %Background operators:
% 2.55/1.43  
% 2.55/1.43  
% 2.55/1.43  %Foreground operators:
% 2.55/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.55/1.43  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.55/1.43  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.43  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.55/1.43  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 2.55/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.55/1.43  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.55/1.43  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.55/1.43  tff(o_2_6_yellow_6, type, o_2_6_yellow_6: ($i * $i) > $i).
% 2.55/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.43  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.55/1.43  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 2.55/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.43  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.55/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.55/1.43  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 2.55/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.55/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.43  
% 2.55/1.45  tff(f_186, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (k11_yellow_6(A, B) = k4_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_6)).
% 2.55/1.45  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.55/1.45  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (l1_waybel_0(B, A) => ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) => (((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_6)).
% 2.55/1.45  tff(f_119, axiom, (![A, B]: ((((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_6_yellow_6(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_2_6_yellow_6)).
% 2.55/1.45  tff(f_141, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k4_yellow_6(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_6)).
% 2.55/1.45  tff(f_43, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.55/1.45  tff(f_162, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 2.55/1.45  tff(f_99, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k11_yellow_6(A, B)) <=> r2_hidden(C, k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_yellow_6)).
% 2.55/1.45  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.45  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_24, plain, (k4_yellow_6('#skF_1', '#skF_2')!=k11_yellow_6('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_26, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_38, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_28, plain, (v1_yellow_6('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_32, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_30, plain, (v7_waybel_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_186])).
% 2.55/1.45  tff(c_6, plain, (![B_7, A_5]: (v3_yellow_6(B_7, A_5) | ~v1_yellow_6(B_7, A_5) | ~v7_waybel_0(B_7) | ~v4_orders_2(B_7) | v2_struct_0(B_7) | ~l1_waybel_0(B_7, A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.55/1.45  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(o_2_6_yellow_6(A_15, B_16), u1_struct_0(B_16)) | ~l1_waybel_0(B_16, A_15) | ~v1_yellow_6(B_16, A_15) | ~v7_waybel_0(B_16) | ~v4_orders_2(B_16) | v2_struct_0(B_16) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.55/1.45  tff(c_48, plain, (![A_38, B_39, C_40]: (k2_waybel_0(A_38, B_39, C_40)=k4_yellow_6(A_38, B_39) | ~m1_subset_1(C_40, u1_struct_0(B_39)) | ~l1_waybel_0(B_39, A_38) | ~v1_yellow_6(B_39, A_38) | ~v7_waybel_0(B_39) | ~v4_orders_2(B_39) | v2_struct_0(B_39) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_141])).
% 2.55/1.45  tff(c_67, plain, (![A_48, B_49, A_50]: (k2_waybel_0(A_48, B_49, o_2_6_yellow_6(A_50, B_49))=k4_yellow_6(A_48, B_49) | ~l1_waybel_0(B_49, A_48) | ~v1_yellow_6(B_49, A_48) | ~l1_struct_0(A_48) | v2_struct_0(A_48) | ~l1_waybel_0(B_49, A_50) | ~v1_yellow_6(B_49, A_50) | ~v7_waybel_0(B_49) | ~v4_orders_2(B_49) | v2_struct_0(B_49) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50) | v2_struct_0(A_50))), inference(resolution, [status(thm)], [c_18, c_48])).
% 2.55/1.45  tff(c_4, plain, (![A_2, B_3, C_4]: (m1_subset_1(k2_waybel_0(A_2, B_3, C_4), u1_struct_0(A_2)) | ~m1_subset_1(C_4, u1_struct_0(B_3)) | ~l1_waybel_0(B_3, A_2) | v2_struct_0(B_3) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.55/1.45  tff(c_113, plain, (![A_60, B_61, A_62]: (m1_subset_1(k4_yellow_6(A_60, B_61), u1_struct_0(A_60)) | ~m1_subset_1(o_2_6_yellow_6(A_62, B_61), u1_struct_0(B_61)) | ~l1_waybel_0(B_61, A_60) | v2_struct_0(B_61) | ~l1_struct_0(A_60) | v2_struct_0(A_60) | ~l1_waybel_0(B_61, A_60) | ~v1_yellow_6(B_61, A_60) | ~l1_struct_0(A_60) | v2_struct_0(A_60) | ~l1_waybel_0(B_61, A_62) | ~v1_yellow_6(B_61, A_62) | ~v7_waybel_0(B_61) | ~v4_orders_2(B_61) | v2_struct_0(B_61) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_67, c_4])).
% 2.55/1.45  tff(c_117, plain, (![A_63, B_64, A_65]: (m1_subset_1(k4_yellow_6(A_63, B_64), u1_struct_0(A_63)) | ~l1_waybel_0(B_64, A_63) | ~v1_yellow_6(B_64, A_63) | ~l1_struct_0(A_63) | v2_struct_0(A_63) | ~l1_waybel_0(B_64, A_65) | ~v1_yellow_6(B_64, A_65) | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_18, c_113])).
% 2.55/1.45  tff(c_119, plain, (![A_63]: (m1_subset_1(k4_yellow_6(A_63, '#skF_2'), u1_struct_0(A_63)) | ~l1_waybel_0('#skF_2', A_63) | ~v1_yellow_6('#skF_2', A_63) | ~l1_struct_0(A_63) | v2_struct_0(A_63) | ~l1_waybel_0('#skF_2', '#skF_1') | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_117])).
% 2.55/1.45  tff(c_122, plain, (![A_63]: (m1_subset_1(k4_yellow_6(A_63, '#skF_2'), u1_struct_0(A_63)) | ~l1_waybel_0('#skF_2', A_63) | ~v1_yellow_6('#skF_2', A_63) | ~l1_struct_0(A_63) | v2_struct_0(A_63) | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_32, c_30, c_26, c_119])).
% 2.55/1.45  tff(c_124, plain, (![A_66]: (m1_subset_1(k4_yellow_6(A_66, '#skF_2'), u1_struct_0(A_66)) | ~l1_waybel_0('#skF_2', A_66) | ~v1_yellow_6('#skF_2', A_66) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(negUnitSimplification, [status(thm)], [c_42, c_34, c_122])).
% 2.55/1.45  tff(c_22, plain, (![A_24, B_26]: (r2_hidden(k4_yellow_6(A_24, B_26), k10_yellow_6(A_24, B_26)) | ~l1_waybel_0(B_26, A_24) | ~v1_yellow_6(B_26, A_24) | ~v7_waybel_0(B_26) | ~v4_orders_2(B_26) | v2_struct_0(B_26) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_162])).
% 2.55/1.45  tff(c_56, plain, (![A_43, B_44, C_45]: (k11_yellow_6(A_43, B_44)=C_45 | ~r2_hidden(C_45, k10_yellow_6(A_43, B_44)) | ~m1_subset_1(C_45, u1_struct_0(A_43)) | ~l1_waybel_0(B_44, A_43) | ~v3_yellow_6(B_44, A_43) | ~v7_waybel_0(B_44) | ~v4_orders_2(B_44) | v2_struct_0(B_44) | ~l1_pre_topc(A_43) | ~v8_pre_topc(A_43) | ~v2_pre_topc(A_43) | v2_struct_0(A_43))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.55/1.45  tff(c_65, plain, (![A_24, B_26]: (k4_yellow_6(A_24, B_26)=k11_yellow_6(A_24, B_26) | ~m1_subset_1(k4_yellow_6(A_24, B_26), u1_struct_0(A_24)) | ~v3_yellow_6(B_26, A_24) | ~v8_pre_topc(A_24) | ~l1_waybel_0(B_26, A_24) | ~v1_yellow_6(B_26, A_24) | ~v7_waybel_0(B_26) | ~v4_orders_2(B_26) | v2_struct_0(B_26) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(resolution, [status(thm)], [c_22, c_56])).
% 2.55/1.45  tff(c_129, plain, (![A_66]: (k4_yellow_6(A_66, '#skF_2')=k11_yellow_6(A_66, '#skF_2') | ~v3_yellow_6('#skF_2', A_66) | ~v8_pre_topc(A_66) | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | ~l1_waybel_0('#skF_2', A_66) | ~v1_yellow_6('#skF_2', A_66) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(resolution, [status(thm)], [c_124, c_65])).
% 2.55/1.45  tff(c_135, plain, (![A_66]: (k4_yellow_6(A_66, '#skF_2')=k11_yellow_6(A_66, '#skF_2') | ~v3_yellow_6('#skF_2', A_66) | ~v8_pre_topc(A_66) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | ~l1_waybel_0('#skF_2', A_66) | ~v1_yellow_6('#skF_2', A_66) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_129])).
% 2.55/1.45  tff(c_159, plain, (![A_71]: (k4_yellow_6(A_71, '#skF_2')=k11_yellow_6(A_71, '#skF_2') | ~v3_yellow_6('#skF_2', A_71) | ~v8_pre_topc(A_71) | ~l1_pre_topc(A_71) | ~v2_pre_topc(A_71) | ~l1_waybel_0('#skF_2', A_71) | ~v1_yellow_6('#skF_2', A_71) | ~l1_struct_0(A_71) | v2_struct_0(A_71))), inference(negUnitSimplification, [status(thm)], [c_34, c_135])).
% 2.55/1.45  tff(c_163, plain, (![A_5]: (k4_yellow_6(A_5, '#skF_2')=k11_yellow_6(A_5, '#skF_2') | ~v8_pre_topc(A_5) | ~l1_struct_0(A_5) | ~v1_yellow_6('#skF_2', A_5) | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_waybel_0('#skF_2', A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(resolution, [status(thm)], [c_6, c_159])).
% 2.55/1.45  tff(c_166, plain, (![A_5]: (k4_yellow_6(A_5, '#skF_2')=k11_yellow_6(A_5, '#skF_2') | ~v8_pre_topc(A_5) | ~l1_struct_0(A_5) | ~v1_yellow_6('#skF_2', A_5) | v2_struct_0('#skF_2') | ~l1_waybel_0('#skF_2', A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_163])).
% 2.55/1.45  tff(c_168, plain, (![A_72]: (k4_yellow_6(A_72, '#skF_2')=k11_yellow_6(A_72, '#skF_2') | ~v8_pre_topc(A_72) | ~l1_struct_0(A_72) | ~v1_yellow_6('#skF_2', A_72) | ~l1_waybel_0('#skF_2', A_72) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(negUnitSimplification, [status(thm)], [c_34, c_166])).
% 2.55/1.45  tff(c_171, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | ~v8_pre_topc('#skF_1') | ~l1_struct_0('#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_168])).
% 2.55/1.45  tff(c_174, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_26, c_38, c_171])).
% 2.55/1.45  tff(c_175, plain, (~l1_struct_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_42, c_24, c_174])).
% 2.55/1.45  tff(c_178, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_175])).
% 2.55/1.45  tff(c_182, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_178])).
% 2.55/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/1.45  
% 2.55/1.45  Inference rules
% 2.55/1.45  ----------------------
% 2.55/1.45  #Ref     : 0
% 2.55/1.45  #Sup     : 31
% 2.55/1.45  #Fact    : 0
% 2.55/1.45  #Define  : 0
% 2.55/1.45  #Split   : 0
% 2.55/1.45  #Chain   : 0
% 2.55/1.45  #Close   : 0
% 2.55/1.45  
% 2.55/1.45  Ordering : KBO
% 2.55/1.45  
% 2.55/1.45  Simplification rules
% 2.55/1.45  ----------------------
% 2.55/1.45  #Subsume      : 2
% 2.55/1.45  #Demod        : 14
% 2.55/1.45  #Tautology    : 10
% 2.55/1.45  #SimpNegUnit  : 4
% 2.55/1.45  #BackRed      : 0
% 2.55/1.45  
% 2.55/1.45  #Partial instantiations: 0
% 2.55/1.45  #Strategies tried      : 1
% 2.55/1.45  
% 2.55/1.45  Timing (in seconds)
% 2.55/1.45  ----------------------
% 2.55/1.45  Preprocessing        : 0.36
% 2.55/1.45  Parsing              : 0.16
% 2.55/1.45  CNF conversion       : 0.03
% 2.55/1.45  Main loop            : 0.25
% 2.55/1.45  Inferencing          : 0.10
% 2.55/1.45  Reduction            : 0.06
% 2.55/1.45  Demodulation         : 0.04
% 2.55/1.45  BG Simplification    : 0.03
% 2.55/1.45  Subsumption          : 0.05
% 2.55/1.45  Abstraction          : 0.02
% 2.55/1.45  MUC search           : 0.00
% 2.55/1.45  Cooper               : 0.00
% 2.55/1.45  Total                : 0.65
% 2.55/1.45  Index Insertion      : 0.00
% 2.55/1.45  Index Deletion       : 0.00
% 2.55/1.45  Index Matching       : 0.00
% 2.55/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
