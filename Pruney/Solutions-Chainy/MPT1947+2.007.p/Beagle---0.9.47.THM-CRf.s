%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:55 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 146 expanded)
%              Number of leaves         :   31 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  283 ( 836 expanded)
%              Number of equality atoms :   16 (  50 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > o_2_2_yellow_6 > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(o_2_2_yellow_6,type,(
    o_2_2_yellow_6: ( $i * $i ) > $i )).

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

tff(f_182,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_yellow_6)).

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(o_2_2_yellow_6(A,B),u1_struct_0(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_2_2_yellow_6)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_6)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_waybel_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_yellow_6)).

tff(f_158,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_6)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_yellow_6)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_24,plain,(
    k4_yellow_6('#skF_1','#skF_2') != k11_yellow_6('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_40,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_26,plain,(
    l1_waybel_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_32,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_30,plain,(
    v7_waybel_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(o_2_2_yellow_6(A_15,B_16),u1_struct_0(B_16))
      | ~ l1_waybel_0(B_16,A_15)
      | ~ v7_waybel_0(B_16)
      | ~ v4_orders_2(B_16)
      | v2_struct_0(B_16)
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

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
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_55,plain,(
    ! [A_41,B_42,A_43] :
      ( k2_waybel_0(A_41,B_42,o_2_2_yellow_6(A_43,B_42)) = k4_yellow_6(A_41,B_42)
      | ~ l1_waybel_0(B_42,A_41)
      | ~ v1_yellow_6(B_42,A_41)
      | ~ l1_struct_0(A_41)
      | v2_struct_0(A_41)
      | ~ l1_waybel_0(B_42,A_43)
      | ~ v7_waybel_0(B_42)
      | ~ v4_orders_2(B_42)
      | v2_struct_0(B_42)
      | ~ l1_struct_0(A_43)
      | v2_struct_0(A_43) ) ),
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

tff(c_86,plain,(
    ! [A_55,B_56,A_57] :
      ( m1_subset_1(k4_yellow_6(A_55,B_56),u1_struct_0(A_55))
      | ~ m1_subset_1(o_2_2_yellow_6(A_57,B_56),u1_struct_0(B_56))
      | ~ l1_waybel_0(B_56,A_55)
      | v2_struct_0(B_56)
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55)
      | ~ l1_waybel_0(B_56,A_55)
      | ~ v1_yellow_6(B_56,A_55)
      | ~ l1_struct_0(A_55)
      | v2_struct_0(A_55)
      | ~ l1_waybel_0(B_56,A_57)
      | ~ v7_waybel_0(B_56)
      | ~ v4_orders_2(B_56)
      | v2_struct_0(B_56)
      | ~ l1_struct_0(A_57)
      | v2_struct_0(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_4])).

tff(c_90,plain,(
    ! [A_58,B_59,A_60] :
      ( m1_subset_1(k4_yellow_6(A_58,B_59),u1_struct_0(A_58))
      | ~ l1_waybel_0(B_59,A_58)
      | ~ v1_yellow_6(B_59,A_58)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58)
      | ~ l1_waybel_0(B_59,A_60)
      | ~ v7_waybel_0(B_59)
      | ~ v4_orders_2(B_59)
      | v2_struct_0(B_59)
      | ~ l1_struct_0(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_18,c_86])).

tff(c_92,plain,(
    ! [A_58] :
      ( m1_subset_1(k4_yellow_6(A_58,'#skF_2'),u1_struct_0(A_58))
      | ~ l1_waybel_0('#skF_2',A_58)
      | ~ v1_yellow_6('#skF_2',A_58)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58)
      | ~ v7_waybel_0('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_90])).

tff(c_95,plain,(
    ! [A_58] :
      ( m1_subset_1(k4_yellow_6(A_58,'#skF_2'),u1_struct_0(A_58))
      | ~ l1_waybel_0('#skF_2',A_58)
      | ~ v1_yellow_6('#skF_2',A_58)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58)
      | v2_struct_0('#skF_2')
      | ~ l1_struct_0('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_92])).

tff(c_96,plain,(
    ! [A_58] :
      ( m1_subset_1(k4_yellow_6(A_58,'#skF_2'),u1_struct_0(A_58))
      | ~ l1_waybel_0('#skF_2',A_58)
      | ~ v1_yellow_6('#skF_2',A_58)
      | ~ l1_struct_0(A_58)
      | v2_struct_0(A_58)
      | ~ l1_struct_0('#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_34,c_95])).

tff(c_97,plain,(
    ~ l1_struct_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_100,plain,(
    ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_2,c_97])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_100])).

tff(c_106,plain,(
    l1_struct_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_38,plain,(
    v8_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_28,plain,(
    v1_yellow_6('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

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

tff(c_122,plain,(
    ! [A_65] :
      ( m1_subset_1(k4_yellow_6(A_65,'#skF_2'),u1_struct_0(A_65))
      | ~ l1_waybel_0('#skF_2',A_65)
      | ~ v1_yellow_6('#skF_2',A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(splitRight,[status(thm)],[c_96])).

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
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_68,plain,(
    ! [A_46,B_47,C_48] :
      ( k11_yellow_6(A_46,B_47) = C_48
      | ~ r2_hidden(C_48,k10_yellow_6(A_46,B_47))
      | ~ m1_subset_1(C_48,u1_struct_0(A_46))
      | ~ l1_waybel_0(B_47,A_46)
      | ~ v3_yellow_6(B_47,A_46)
      | ~ v7_waybel_0(B_47)
      | ~ v4_orders_2(B_47)
      | v2_struct_0(B_47)
      | ~ l1_pre_topc(A_46)
      | ~ v8_pre_topc(A_46)
      | ~ v2_pre_topc(A_46)
      | v2_struct_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_77,plain,(
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
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_127,plain,(
    ! [A_65] :
      ( k4_yellow_6(A_65,'#skF_2') = k11_yellow_6(A_65,'#skF_2')
      | ~ v3_yellow_6('#skF_2',A_65)
      | ~ v8_pre_topc(A_65)
      | ~ v7_waybel_0('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | ~ l1_waybel_0('#skF_2',A_65)
      | ~ v1_yellow_6('#skF_2',A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_122,c_77])).

tff(c_133,plain,(
    ! [A_65] :
      ( k4_yellow_6(A_65,'#skF_2') = k11_yellow_6(A_65,'#skF_2')
      | ~ v3_yellow_6('#skF_2',A_65)
      | ~ v8_pre_topc(A_65)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_65)
      | ~ v2_pre_topc(A_65)
      | ~ l1_waybel_0('#skF_2',A_65)
      | ~ v1_yellow_6('#skF_2',A_65)
      | ~ l1_struct_0(A_65)
      | v2_struct_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_127])).

tff(c_136,plain,(
    ! [A_66] :
      ( k4_yellow_6(A_66,'#skF_2') = k11_yellow_6(A_66,'#skF_2')
      | ~ v3_yellow_6('#skF_2',A_66)
      | ~ v8_pre_topc(A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | ~ l1_waybel_0('#skF_2',A_66)
      | ~ v1_yellow_6('#skF_2',A_66)
      | ~ l1_struct_0(A_66)
      | v2_struct_0(A_66) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_133])).

tff(c_140,plain,(
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
    inference(resolution,[status(thm)],[c_6,c_136])).

tff(c_143,plain,(
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
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_140])).

tff(c_145,plain,(
    ! [A_67] :
      ( k4_yellow_6(A_67,'#skF_2') = k11_yellow_6(A_67,'#skF_2')
      | ~ v8_pre_topc(A_67)
      | ~ l1_struct_0(A_67)
      | ~ v1_yellow_6('#skF_2',A_67)
      | ~ l1_waybel_0('#skF_2',A_67)
      | ~ l1_pre_topc(A_67)
      | ~ v2_pre_topc(A_67)
      | v2_struct_0(A_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_143])).

tff(c_148,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | ~ v8_pre_topc('#skF_1')
    | ~ l1_struct_0('#skF_1')
    | ~ l1_waybel_0('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_145])).

tff(c_151,plain,
    ( k4_yellow_6('#skF_1','#skF_2') = k11_yellow_6('#skF_1','#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_26,c_106,c_38,c_148])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_24,c_151])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:35:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.21  
% 2.16/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.21  %$ v3_yellow_6 > v1_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k2_waybel_0 > o_2_2_yellow_6 > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_2 > #skF_1
% 2.29/1.21  
% 2.29/1.21  %Foreground sorts:
% 2.29/1.21  
% 2.29/1.21  
% 2.29/1.21  %Background operators:
% 2.29/1.21  
% 2.29/1.21  
% 2.29/1.21  %Foreground operators:
% 2.29/1.21  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.29/1.21  tff(o_2_2_yellow_6, type, o_2_2_yellow_6: ($i * $i) > $i).
% 2.29/1.21  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 2.29/1.21  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 2.29/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.21  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.29/1.21  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 2.29/1.21  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.29/1.21  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 2.29/1.21  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.29/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.21  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.29/1.21  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 2.29/1.21  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.29/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.21  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.29/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.21  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.29/1.21  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 2.29/1.21  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.29/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.21  
% 2.29/1.23  tff(f_182, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (k11_yellow_6(A, B) = k4_yellow_6(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_yellow_6)).
% 2.29/1.23  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.29/1.23  tff(f_115, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(o_2_2_yellow_6(A, B), u1_struct_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_o_2_2_yellow_6)).
% 2.29/1.23  tff(f_137, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k4_yellow_6(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_yellow_6)).
% 2.29/1.23  tff(f_43, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 2.29/1.23  tff(f_71, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (l1_waybel_0(B, A) => ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) => (((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_yellow_6)).
% 2.29/1.23  tff(f_158, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_6)).
% 2.29/1.23  tff(f_99, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k11_yellow_6(A, B)) <=> r2_hidden(C, k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_yellow_6)).
% 2.29/1.23  tff(c_42, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_24, plain, (k4_yellow_6('#skF_1', '#skF_2')!=k11_yellow_6('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_40, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_26, plain, (l1_waybel_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.29/1.23  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_32, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_30, plain, (v7_waybel_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(o_2_2_yellow_6(A_15, B_16), u1_struct_0(B_16)) | ~l1_waybel_0(B_16, A_15) | ~v7_waybel_0(B_16) | ~v4_orders_2(B_16) | v2_struct_0(B_16) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.29/1.23  tff(c_48, plain, (![A_38, B_39, C_40]: (k2_waybel_0(A_38, B_39, C_40)=k4_yellow_6(A_38, B_39) | ~m1_subset_1(C_40, u1_struct_0(B_39)) | ~l1_waybel_0(B_39, A_38) | ~v1_yellow_6(B_39, A_38) | ~v7_waybel_0(B_39) | ~v4_orders_2(B_39) | v2_struct_0(B_39) | ~l1_struct_0(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.29/1.23  tff(c_55, plain, (![A_41, B_42, A_43]: (k2_waybel_0(A_41, B_42, o_2_2_yellow_6(A_43, B_42))=k4_yellow_6(A_41, B_42) | ~l1_waybel_0(B_42, A_41) | ~v1_yellow_6(B_42, A_41) | ~l1_struct_0(A_41) | v2_struct_0(A_41) | ~l1_waybel_0(B_42, A_43) | ~v7_waybel_0(B_42) | ~v4_orders_2(B_42) | v2_struct_0(B_42) | ~l1_struct_0(A_43) | v2_struct_0(A_43))), inference(resolution, [status(thm)], [c_18, c_48])).
% 2.29/1.23  tff(c_4, plain, (![A_2, B_3, C_4]: (m1_subset_1(k2_waybel_0(A_2, B_3, C_4), u1_struct_0(A_2)) | ~m1_subset_1(C_4, u1_struct_0(B_3)) | ~l1_waybel_0(B_3, A_2) | v2_struct_0(B_3) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.29/1.23  tff(c_86, plain, (![A_55, B_56, A_57]: (m1_subset_1(k4_yellow_6(A_55, B_56), u1_struct_0(A_55)) | ~m1_subset_1(o_2_2_yellow_6(A_57, B_56), u1_struct_0(B_56)) | ~l1_waybel_0(B_56, A_55) | v2_struct_0(B_56) | ~l1_struct_0(A_55) | v2_struct_0(A_55) | ~l1_waybel_0(B_56, A_55) | ~v1_yellow_6(B_56, A_55) | ~l1_struct_0(A_55) | v2_struct_0(A_55) | ~l1_waybel_0(B_56, A_57) | ~v7_waybel_0(B_56) | ~v4_orders_2(B_56) | v2_struct_0(B_56) | ~l1_struct_0(A_57) | v2_struct_0(A_57))), inference(superposition, [status(thm), theory('equality')], [c_55, c_4])).
% 2.29/1.23  tff(c_90, plain, (![A_58, B_59, A_60]: (m1_subset_1(k4_yellow_6(A_58, B_59), u1_struct_0(A_58)) | ~l1_waybel_0(B_59, A_58) | ~v1_yellow_6(B_59, A_58) | ~l1_struct_0(A_58) | v2_struct_0(A_58) | ~l1_waybel_0(B_59, A_60) | ~v7_waybel_0(B_59) | ~v4_orders_2(B_59) | v2_struct_0(B_59) | ~l1_struct_0(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_18, c_86])).
% 2.29/1.23  tff(c_92, plain, (![A_58]: (m1_subset_1(k4_yellow_6(A_58, '#skF_2'), u1_struct_0(A_58)) | ~l1_waybel_0('#skF_2', A_58) | ~v1_yellow_6('#skF_2', A_58) | ~l1_struct_0(A_58) | v2_struct_0(A_58) | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_90])).
% 2.29/1.23  tff(c_95, plain, (![A_58]: (m1_subset_1(k4_yellow_6(A_58, '#skF_2'), u1_struct_0(A_58)) | ~l1_waybel_0('#skF_2', A_58) | ~v1_yellow_6('#skF_2', A_58) | ~l1_struct_0(A_58) | v2_struct_0(A_58) | v2_struct_0('#skF_2') | ~l1_struct_0('#skF_1') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_92])).
% 2.29/1.23  tff(c_96, plain, (![A_58]: (m1_subset_1(k4_yellow_6(A_58, '#skF_2'), u1_struct_0(A_58)) | ~l1_waybel_0('#skF_2', A_58) | ~v1_yellow_6('#skF_2', A_58) | ~l1_struct_0(A_58) | v2_struct_0(A_58) | ~l1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_34, c_95])).
% 2.29/1.23  tff(c_97, plain, (~l1_struct_0('#skF_1')), inference(splitLeft, [status(thm)], [c_96])).
% 2.29/1.23  tff(c_100, plain, (~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_2, c_97])).
% 2.29/1.23  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_100])).
% 2.29/1.23  tff(c_106, plain, (l1_struct_0('#skF_1')), inference(splitRight, [status(thm)], [c_96])).
% 2.29/1.23  tff(c_38, plain, (v8_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_28, plain, (v1_yellow_6('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.29/1.23  tff(c_6, plain, (![B_7, A_5]: (v3_yellow_6(B_7, A_5) | ~v1_yellow_6(B_7, A_5) | ~v7_waybel_0(B_7) | ~v4_orders_2(B_7) | v2_struct_0(B_7) | ~l1_waybel_0(B_7, A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.29/1.23  tff(c_122, plain, (![A_65]: (m1_subset_1(k4_yellow_6(A_65, '#skF_2'), u1_struct_0(A_65)) | ~l1_waybel_0('#skF_2', A_65) | ~v1_yellow_6('#skF_2', A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(splitRight, [status(thm)], [c_96])).
% 2.29/1.23  tff(c_22, plain, (![A_24, B_26]: (r2_hidden(k4_yellow_6(A_24, B_26), k10_yellow_6(A_24, B_26)) | ~l1_waybel_0(B_26, A_24) | ~v1_yellow_6(B_26, A_24) | ~v7_waybel_0(B_26) | ~v4_orders_2(B_26) | v2_struct_0(B_26) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.29/1.23  tff(c_68, plain, (![A_46, B_47, C_48]: (k11_yellow_6(A_46, B_47)=C_48 | ~r2_hidden(C_48, k10_yellow_6(A_46, B_47)) | ~m1_subset_1(C_48, u1_struct_0(A_46)) | ~l1_waybel_0(B_47, A_46) | ~v3_yellow_6(B_47, A_46) | ~v7_waybel_0(B_47) | ~v4_orders_2(B_47) | v2_struct_0(B_47) | ~l1_pre_topc(A_46) | ~v8_pre_topc(A_46) | ~v2_pre_topc(A_46) | v2_struct_0(A_46))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.29/1.23  tff(c_77, plain, (![A_24, B_26]: (k4_yellow_6(A_24, B_26)=k11_yellow_6(A_24, B_26) | ~m1_subset_1(k4_yellow_6(A_24, B_26), u1_struct_0(A_24)) | ~v3_yellow_6(B_26, A_24) | ~v8_pre_topc(A_24) | ~l1_waybel_0(B_26, A_24) | ~v1_yellow_6(B_26, A_24) | ~v7_waybel_0(B_26) | ~v4_orders_2(B_26) | v2_struct_0(B_26) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(resolution, [status(thm)], [c_22, c_68])).
% 2.29/1.23  tff(c_127, plain, (![A_65]: (k4_yellow_6(A_65, '#skF_2')=k11_yellow_6(A_65, '#skF_2') | ~v3_yellow_6('#skF_2', A_65) | ~v8_pre_topc(A_65) | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | ~l1_waybel_0('#skF_2', A_65) | ~v1_yellow_6('#skF_2', A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(resolution, [status(thm)], [c_122, c_77])).
% 2.29/1.23  tff(c_133, plain, (![A_65]: (k4_yellow_6(A_65, '#skF_2')=k11_yellow_6(A_65, '#skF_2') | ~v3_yellow_6('#skF_2', A_65) | ~v8_pre_topc(A_65) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_65) | ~v2_pre_topc(A_65) | ~l1_waybel_0('#skF_2', A_65) | ~v1_yellow_6('#skF_2', A_65) | ~l1_struct_0(A_65) | v2_struct_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_127])).
% 2.29/1.23  tff(c_136, plain, (![A_66]: (k4_yellow_6(A_66, '#skF_2')=k11_yellow_6(A_66, '#skF_2') | ~v3_yellow_6('#skF_2', A_66) | ~v8_pre_topc(A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | ~l1_waybel_0('#skF_2', A_66) | ~v1_yellow_6('#skF_2', A_66) | ~l1_struct_0(A_66) | v2_struct_0(A_66))), inference(negUnitSimplification, [status(thm)], [c_34, c_133])).
% 2.29/1.23  tff(c_140, plain, (![A_5]: (k4_yellow_6(A_5, '#skF_2')=k11_yellow_6(A_5, '#skF_2') | ~v8_pre_topc(A_5) | ~l1_struct_0(A_5) | ~v1_yellow_6('#skF_2', A_5) | ~v7_waybel_0('#skF_2') | ~v4_orders_2('#skF_2') | v2_struct_0('#skF_2') | ~l1_waybel_0('#skF_2', A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(resolution, [status(thm)], [c_6, c_136])).
% 2.29/1.23  tff(c_143, plain, (![A_5]: (k4_yellow_6(A_5, '#skF_2')=k11_yellow_6(A_5, '#skF_2') | ~v8_pre_topc(A_5) | ~l1_struct_0(A_5) | ~v1_yellow_6('#skF_2', A_5) | v2_struct_0('#skF_2') | ~l1_waybel_0('#skF_2', A_5) | ~l1_pre_topc(A_5) | ~v2_pre_topc(A_5) | v2_struct_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_140])).
% 2.29/1.23  tff(c_145, plain, (![A_67]: (k4_yellow_6(A_67, '#skF_2')=k11_yellow_6(A_67, '#skF_2') | ~v8_pre_topc(A_67) | ~l1_struct_0(A_67) | ~v1_yellow_6('#skF_2', A_67) | ~l1_waybel_0('#skF_2', A_67) | ~l1_pre_topc(A_67) | ~v2_pre_topc(A_67) | v2_struct_0(A_67))), inference(negUnitSimplification, [status(thm)], [c_34, c_143])).
% 2.29/1.23  tff(c_148, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | ~v8_pre_topc('#skF_1') | ~l1_struct_0('#skF_1') | ~l1_waybel_0('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_145])).
% 2.29/1.23  tff(c_151, plain, (k4_yellow_6('#skF_1', '#skF_2')=k11_yellow_6('#skF_1', '#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_26, c_106, c_38, c_148])).
% 2.29/1.23  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_24, c_151])).
% 2.29/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.29/1.23  
% 2.29/1.23  Inference rules
% 2.29/1.23  ----------------------
% 2.29/1.23  #Ref     : 0
% 2.29/1.23  #Sup     : 21
% 2.29/1.23  #Fact    : 0
% 2.29/1.23  #Define  : 0
% 2.29/1.23  #Split   : 1
% 2.29/1.23  #Chain   : 0
% 2.29/1.23  #Close   : 0
% 2.29/1.23  
% 2.29/1.23  Ordering : KBO
% 2.29/1.23  
% 2.29/1.23  Simplification rules
% 2.29/1.23  ----------------------
% 2.29/1.23  #Subsume      : 3
% 2.29/1.23  #Demod        : 12
% 2.29/1.23  #Tautology    : 8
% 2.29/1.23  #SimpNegUnit  : 4
% 2.29/1.23  #BackRed      : 0
% 2.29/1.23  
% 2.29/1.23  #Partial instantiations: 0
% 2.29/1.23  #Strategies tried      : 1
% 2.29/1.23  
% 2.29/1.23  Timing (in seconds)
% 2.29/1.23  ----------------------
% 2.29/1.23  Preprocessing        : 0.31
% 2.29/1.23  Parsing              : 0.16
% 2.29/1.23  CNF conversion       : 0.02
% 2.29/1.23  Main loop            : 0.19
% 2.29/1.23  Inferencing          : 0.08
% 2.29/1.23  Reduction            : 0.05
% 2.29/1.23  Demodulation         : 0.04
% 2.29/1.23  BG Simplification    : 0.02
% 2.29/1.23  Subsumption          : 0.04
% 2.29/1.23  Abstraction          : 0.01
% 2.29/1.23  MUC search           : 0.00
% 2.29/1.23  Cooper               : 0.00
% 2.29/1.23  Total                : 0.54
% 2.29/1.23  Index Insertion      : 0.00
% 2.29/1.23  Index Deletion       : 0.00
% 2.29/1.23  Index Matching       : 0.00
% 2.29/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
