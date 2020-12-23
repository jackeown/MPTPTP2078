%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:39 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 427 expanded)
%              Number of leaves         :   23 ( 151 expanded)
%              Depth                    :   15
%              Number of atoms          :  249 (2134 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_pre_topc > #nlpp > u1_struct_0 > k6_yellow_6 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k6_yellow_6,type,(
    k6_yellow_6: $i > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ( v1_compts_1(A)
        <=> ! [B] :
              ( ( ~ v2_struct_0(B)
                & v4_orders_2(B)
                & v7_waybel_0(B)
                & l1_waybel_0(B,A) )
             => ? [C] :
                  ( m1_subset_1(C,u1_struct_0(A))
                  & r3_waybel_9(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_yellow19)).

tff(f_77,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ~ ( r2_hidden(B,k6_yellow_6(A))
                & ! [C] :
                    ( m1_subset_1(C,u1_struct_0(A))
                   => ~ r3_waybel_9(A,B,C) ) ) )
       => v1_compts_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_yellow19)).

tff(f_49,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_compts_1(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ? [C] :
                ( m1_subset_1(C,u1_struct_0(A))
                & r3_waybel_9(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l37_yellow19)).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_32,plain,
    ( ~ v2_struct_0('#skF_4')
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_59,plain,(
    ~ v1_compts_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_20,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_waybel_0('#skF_2'(A_7),A_7)
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_12,plain,(
    ! [A_7] :
      ( v7_waybel_0('#skF_2'(A_7))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_7] :
      ( v4_orders_2('#skF_2'(A_7))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_46,plain,(
    ! [B_21] :
      ( v1_compts_1('#skF_3')
      | r3_waybel_9('#skF_3',B_21,'#skF_5'(B_21))
      | ~ l1_waybel_0(B_21,'#skF_3')
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_67,plain,(
    ! [B_21] :
      ( r3_waybel_9('#skF_3',B_21,'#skF_5'(B_21))
      | ~ l1_waybel_0(B_21,'#skF_3')
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21) ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_46])).

tff(c_71,plain,(
    ! [A_30,C_31] :
      ( ~ r3_waybel_9(A_30,'#skF_2'(A_30),C_31)
      | ~ m1_subset_1(C_31,u1_struct_0(A_30))
      | v1_compts_1(A_30)
      | ~ l1_pre_topc(A_30)
      | ~ v2_pre_topc(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_75,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3'))
    | v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ v4_orders_2('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_67,c_71])).

tff(c_78,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3'))
    | v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ v4_orders_2('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_75])).

tff(c_79,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3'))
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ v4_orders_2('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_59,c_78])).

tff(c_80,plain,(
    ~ v4_orders_2('#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_83,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_80])).

tff(c_86,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_83])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_59,c_86])).

tff(c_90,plain,(
    v4_orders_2('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_58,plain,(
    ! [B_21] :
      ( v1_compts_1('#skF_3')
      | m1_subset_1('#skF_5'(B_21),u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_21,'#skF_3')
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_69,plain,(
    ! [B_21] :
      ( m1_subset_1('#skF_5'(B_21),u1_struct_0('#skF_3'))
      | ~ l1_waybel_0(B_21,'#skF_3')
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21) ) ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_58])).

tff(c_89,plain,
    ( ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_91,plain,(
    ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_94,plain,
    ( ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ v4_orders_2('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_69,c_91])).

tff(c_97,plain,
    ( ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_94])).

tff(c_98,plain,(
    ~ v7_waybel_0('#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_97])).

tff(c_101,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_98])).

tff(c_104,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_101])).

tff(c_106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_59,c_104])).

tff(c_107,plain,
    ( ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_97])).

tff(c_109,plain,(
    ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_112,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_109])).

tff(c_115,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_59,c_115])).

tff(c_118,plain,(
    v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_16,plain,(
    ! [A_7] :
      ( ~ v2_struct_0('#skF_2'(A_7))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_122,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_16])).

tff(c_125,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_122])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_59,c_125])).

tff(c_128,plain,
    ( ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_130,plain,(
    ~ v7_waybel_0('#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_133,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_130])).

tff(c_136,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_133])).

tff(c_138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_59,c_136])).

tff(c_139,plain,
    ( ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_141,plain,(
    ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_150,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_141])).

tff(c_153,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_150])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_59,c_153])).

tff(c_156,plain,(
    v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_160,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_156,c_16])).

tff(c_163,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_160])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_59,c_163])).

tff(c_166,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_167,plain,(
    v1_compts_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_30,plain,
    ( v4_orders_2('#skF_4')
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_168,plain,(
    ~ v1_compts_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_168])).

tff(c_171,plain,(
    v4_orders_2('#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( v7_waybel_0('#skF_4')
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_175,plain,(
    v7_waybel_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_28])).

tff(c_26,plain,
    ( l1_waybel_0('#skF_4','#skF_3')
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_177,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_26])).

tff(c_205,plain,(
    ! [A_45,B_46] :
      ( r3_waybel_9(A_45,B_46,'#skF_1'(A_45,B_46))
      | ~ l1_waybel_0(B_46,A_45)
      | ~ v7_waybel_0(B_46)
      | ~ v4_orders_2(B_46)
      | v2_struct_0(B_46)
      | ~ v1_compts_1(A_45)
      | ~ l1_pre_topc(A_45)
      | ~ v2_pre_topc(A_45)
      | v2_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_195,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1('#skF_1'(A_42,B_43),u1_struct_0(A_42))
      | ~ l1_waybel_0(B_43,A_42)
      | ~ v7_waybel_0(B_43)
      | ~ v4_orders_2(B_43)
      | v2_struct_0(B_43)
      | ~ v1_compts_1(A_42)
      | ~ l1_pre_topc(A_42)
      | ~ v2_pre_topc(A_42)
      | v2_struct_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [C_20] :
      ( ~ r3_waybel_9('#skF_3','#skF_4',C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_3'))
      | ~ v1_compts_1('#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_179,plain,(
    ! [C_20] :
      ( ~ r3_waybel_9('#skF_3','#skF_4',C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_24])).

tff(c_199,plain,(
    ! [B_43] :
      ( ~ r3_waybel_9('#skF_3','#skF_4','#skF_1'('#skF_3',B_43))
      | ~ l1_waybel_0(B_43,'#skF_3')
      | ~ v7_waybel_0(B_43)
      | ~ v4_orders_2(B_43)
      | v2_struct_0(B_43)
      | ~ v1_compts_1('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_195,c_179])).

tff(c_202,plain,(
    ! [B_43] :
      ( ~ r3_waybel_9('#skF_3','#skF_4','#skF_1'('#skF_3',B_43))
      | ~ l1_waybel_0(B_43,'#skF_3')
      | ~ v7_waybel_0(B_43)
      | ~ v4_orders_2(B_43)
      | v2_struct_0(B_43)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_167,c_199])).

tff(c_203,plain,(
    ! [B_43] :
      ( ~ r3_waybel_9('#skF_3','#skF_4','#skF_1'('#skF_3',B_43))
      | ~ l1_waybel_0(B_43,'#skF_3')
      | ~ v7_waybel_0(B_43)
      | ~ v4_orders_2(B_43)
      | v2_struct_0(B_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_202])).

tff(c_209,plain,
    ( ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ v7_waybel_0('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_205,c_203])).

tff(c_216,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_167,c_171,c_175,c_177,c_209])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_166,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:37:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.32  %$ r3_waybel_9 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_pre_topc > #nlpp > u1_struct_0 > k6_yellow_6 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.34/1.32  
% 2.34/1.32  %Foreground sorts:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Background operators:
% 2.34/1.32  
% 2.34/1.32  
% 2.34/1.32  %Foreground operators:
% 2.34/1.32  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.34/1.32  tff('#skF_5', type, '#skF_5': $i > $i).
% 2.34/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.32  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.34/1.32  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.34/1.32  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 2.34/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.32  tff(k6_yellow_6, type, k6_yellow_6: $i > $i).
% 2.34/1.32  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.32  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.34/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.32  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.34/1.32  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.34/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.34/1.32  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 2.34/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.32  
% 2.34/1.34  tff(f_102, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_yellow19)).
% 2.34/1.34  tff(f_77, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => ((![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ~(r2_hidden(B, k6_yellow_6(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~r3_waybel_9(A, B, C)))))) => v1_compts_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l38_yellow19)).
% 2.34/1.34  tff(f_49, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l37_yellow19)).
% 2.34/1.34  tff(c_22, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_32, plain, (~v2_struct_0('#skF_4') | ~v1_compts_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_59, plain, (~v1_compts_1('#skF_3')), inference(splitLeft, [status(thm)], [c_32])).
% 2.34/1.34  tff(c_20, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_18, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_10, plain, (![A_7]: (l1_waybel_0('#skF_2'(A_7), A_7) | v1_compts_1(A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.34/1.34  tff(c_12, plain, (![A_7]: (v7_waybel_0('#skF_2'(A_7)) | v1_compts_1(A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.34/1.34  tff(c_14, plain, (![A_7]: (v4_orders_2('#skF_2'(A_7)) | v1_compts_1(A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.34/1.34  tff(c_46, plain, (![B_21]: (v1_compts_1('#skF_3') | r3_waybel_9('#skF_3', B_21, '#skF_5'(B_21)) | ~l1_waybel_0(B_21, '#skF_3') | ~v7_waybel_0(B_21) | ~v4_orders_2(B_21) | v2_struct_0(B_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_67, plain, (![B_21]: (r3_waybel_9('#skF_3', B_21, '#skF_5'(B_21)) | ~l1_waybel_0(B_21, '#skF_3') | ~v7_waybel_0(B_21) | ~v4_orders_2(B_21) | v2_struct_0(B_21))), inference(negUnitSimplification, [status(thm)], [c_59, c_46])).
% 2.34/1.34  tff(c_71, plain, (![A_30, C_31]: (~r3_waybel_9(A_30, '#skF_2'(A_30), C_31) | ~m1_subset_1(C_31, u1_struct_0(A_30)) | v1_compts_1(A_30) | ~l1_pre_topc(A_30) | ~v2_pre_topc(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.34/1.34  tff(c_75, plain, (~m1_subset_1('#skF_5'('#skF_2'('#skF_3')), u1_struct_0('#skF_3')) | v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3') | ~v7_waybel_0('#skF_2'('#skF_3')) | ~v4_orders_2('#skF_2'('#skF_3')) | v2_struct_0('#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_67, c_71])).
% 2.34/1.34  tff(c_78, plain, (~m1_subset_1('#skF_5'('#skF_2'('#skF_3')), u1_struct_0('#skF_3')) | v1_compts_1('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3') | ~v7_waybel_0('#skF_2'('#skF_3')) | ~v4_orders_2('#skF_2'('#skF_3')) | v2_struct_0('#skF_2'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_75])).
% 2.34/1.34  tff(c_79, plain, (~m1_subset_1('#skF_5'('#skF_2'('#skF_3')), u1_struct_0('#skF_3')) | ~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3') | ~v7_waybel_0('#skF_2'('#skF_3')) | ~v4_orders_2('#skF_2'('#skF_3')) | v2_struct_0('#skF_2'('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_22, c_59, c_78])).
% 2.34/1.34  tff(c_80, plain, (~v4_orders_2('#skF_2'('#skF_3'))), inference(splitLeft, [status(thm)], [c_79])).
% 2.34/1.34  tff(c_83, plain, (v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_14, c_80])).
% 2.34/1.34  tff(c_86, plain, (v1_compts_1('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_83])).
% 2.34/1.34  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_59, c_86])).
% 2.34/1.34  tff(c_90, plain, (v4_orders_2('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_79])).
% 2.34/1.34  tff(c_58, plain, (![B_21]: (v1_compts_1('#skF_3') | m1_subset_1('#skF_5'(B_21), u1_struct_0('#skF_3')) | ~l1_waybel_0(B_21, '#skF_3') | ~v7_waybel_0(B_21) | ~v4_orders_2(B_21) | v2_struct_0(B_21))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_69, plain, (![B_21]: (m1_subset_1('#skF_5'(B_21), u1_struct_0('#skF_3')) | ~l1_waybel_0(B_21, '#skF_3') | ~v7_waybel_0(B_21) | ~v4_orders_2(B_21) | v2_struct_0(B_21))), inference(negUnitSimplification, [status(thm)], [c_59, c_58])).
% 2.34/1.34  tff(c_89, plain, (~v7_waybel_0('#skF_2'('#skF_3')) | ~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3') | ~m1_subset_1('#skF_5'('#skF_2'('#skF_3')), u1_struct_0('#skF_3')) | v2_struct_0('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_79])).
% 2.34/1.34  tff(c_91, plain, (~m1_subset_1('#skF_5'('#skF_2'('#skF_3')), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_89])).
% 2.34/1.34  tff(c_94, plain, (~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3') | ~v7_waybel_0('#skF_2'('#skF_3')) | ~v4_orders_2('#skF_2'('#skF_3')) | v2_struct_0('#skF_2'('#skF_3'))), inference(resolution, [status(thm)], [c_69, c_91])).
% 2.34/1.34  tff(c_97, plain, (~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3') | ~v7_waybel_0('#skF_2'('#skF_3')) | v2_struct_0('#skF_2'('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_94])).
% 2.34/1.34  tff(c_98, plain, (~v7_waybel_0('#skF_2'('#skF_3'))), inference(splitLeft, [status(thm)], [c_97])).
% 2.34/1.34  tff(c_101, plain, (v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_98])).
% 2.34/1.34  tff(c_104, plain, (v1_compts_1('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_101])).
% 2.34/1.34  tff(c_106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_59, c_104])).
% 2.34/1.34  tff(c_107, plain, (~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3') | v2_struct_0('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_97])).
% 2.34/1.34  tff(c_109, plain, (~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_107])).
% 2.34/1.34  tff(c_112, plain, (v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_10, c_109])).
% 2.34/1.34  tff(c_115, plain, (v1_compts_1('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_112])).
% 2.34/1.34  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_59, c_115])).
% 2.34/1.34  tff(c_118, plain, (v2_struct_0('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_107])).
% 2.34/1.34  tff(c_16, plain, (![A_7]: (~v2_struct_0('#skF_2'(A_7)) | v1_compts_1(A_7) | ~l1_pre_topc(A_7) | ~v2_pre_topc(A_7) | v2_struct_0(A_7))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.34/1.34  tff(c_122, plain, (v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_118, c_16])).
% 2.34/1.34  tff(c_125, plain, (v1_compts_1('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_122])).
% 2.34/1.34  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_59, c_125])).
% 2.34/1.34  tff(c_128, plain, (~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3') | ~v7_waybel_0('#skF_2'('#skF_3')) | v2_struct_0('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_89])).
% 2.34/1.34  tff(c_130, plain, (~v7_waybel_0('#skF_2'('#skF_3'))), inference(splitLeft, [status(thm)], [c_128])).
% 2.34/1.34  tff(c_133, plain, (v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_12, c_130])).
% 2.34/1.34  tff(c_136, plain, (v1_compts_1('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_133])).
% 2.34/1.34  tff(c_138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_59, c_136])).
% 2.34/1.34  tff(c_139, plain, (~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3') | v2_struct_0('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_128])).
% 2.34/1.34  tff(c_141, plain, (~l1_waybel_0('#skF_2'('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_139])).
% 2.34/1.34  tff(c_150, plain, (v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_10, c_141])).
% 2.34/1.34  tff(c_153, plain, (v1_compts_1('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_150])).
% 2.34/1.34  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_59, c_153])).
% 2.34/1.34  tff(c_156, plain, (v2_struct_0('#skF_2'('#skF_3'))), inference(splitRight, [status(thm)], [c_139])).
% 2.34/1.34  tff(c_160, plain, (v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_156, c_16])).
% 2.34/1.34  tff(c_163, plain, (v1_compts_1('#skF_3') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_160])).
% 2.34/1.34  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_59, c_163])).
% 2.34/1.34  tff(c_166, plain, (~v2_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_32])).
% 2.34/1.34  tff(c_167, plain, (v1_compts_1('#skF_3')), inference(splitRight, [status(thm)], [c_32])).
% 2.34/1.34  tff(c_30, plain, (v4_orders_2('#skF_4') | ~v1_compts_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_168, plain, (~v1_compts_1('#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 2.34/1.34  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_168])).
% 2.34/1.34  tff(c_171, plain, (v4_orders_2('#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.34/1.34  tff(c_28, plain, (v7_waybel_0('#skF_4') | ~v1_compts_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_175, plain, (v7_waybel_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_28])).
% 2.34/1.34  tff(c_26, plain, (l1_waybel_0('#skF_4', '#skF_3') | ~v1_compts_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_177, plain, (l1_waybel_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_26])).
% 2.34/1.34  tff(c_205, plain, (![A_45, B_46]: (r3_waybel_9(A_45, B_46, '#skF_1'(A_45, B_46)) | ~l1_waybel_0(B_46, A_45) | ~v7_waybel_0(B_46) | ~v4_orders_2(B_46) | v2_struct_0(B_46) | ~v1_compts_1(A_45) | ~l1_pre_topc(A_45) | ~v2_pre_topc(A_45) | v2_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.34/1.34  tff(c_195, plain, (![A_42, B_43]: (m1_subset_1('#skF_1'(A_42, B_43), u1_struct_0(A_42)) | ~l1_waybel_0(B_43, A_42) | ~v7_waybel_0(B_43) | ~v4_orders_2(B_43) | v2_struct_0(B_43) | ~v1_compts_1(A_42) | ~l1_pre_topc(A_42) | ~v2_pre_topc(A_42) | v2_struct_0(A_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.34/1.34  tff(c_24, plain, (![C_20]: (~r3_waybel_9('#skF_3', '#skF_4', C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_3')) | ~v1_compts_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.34/1.34  tff(c_179, plain, (![C_20]: (~r3_waybel_9('#skF_3', '#skF_4', C_20) | ~m1_subset_1(C_20, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_24])).
% 2.34/1.34  tff(c_199, plain, (![B_43]: (~r3_waybel_9('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_43)) | ~l1_waybel_0(B_43, '#skF_3') | ~v7_waybel_0(B_43) | ~v4_orders_2(B_43) | v2_struct_0(B_43) | ~v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_195, c_179])).
% 2.34/1.34  tff(c_202, plain, (![B_43]: (~r3_waybel_9('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_43)) | ~l1_waybel_0(B_43, '#skF_3') | ~v7_waybel_0(B_43) | ~v4_orders_2(B_43) | v2_struct_0(B_43) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_167, c_199])).
% 2.34/1.34  tff(c_203, plain, (![B_43]: (~r3_waybel_9('#skF_3', '#skF_4', '#skF_1'('#skF_3', B_43)) | ~l1_waybel_0(B_43, '#skF_3') | ~v7_waybel_0(B_43) | ~v4_orders_2(B_43) | v2_struct_0(B_43))), inference(negUnitSimplification, [status(thm)], [c_22, c_202])).
% 2.34/1.34  tff(c_209, plain, (~l1_waybel_0('#skF_4', '#skF_3') | ~v7_waybel_0('#skF_4') | ~v4_orders_2('#skF_4') | v2_struct_0('#skF_4') | ~v1_compts_1('#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_205, c_203])).
% 2.34/1.34  tff(c_216, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_167, c_171, c_175, c_177, c_209])).
% 2.34/1.34  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_166, c_216])).
% 2.34/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.34  
% 2.34/1.34  Inference rules
% 2.34/1.34  ----------------------
% 2.34/1.34  #Ref     : 0
% 2.34/1.34  #Sup     : 13
% 2.34/1.34  #Fact    : 0
% 2.34/1.34  #Define  : 0
% 2.34/1.34  #Split   : 9
% 2.34/1.34  #Chain   : 0
% 2.34/1.34  #Close   : 0
% 2.34/1.34  
% 2.34/1.34  Ordering : KBO
% 2.34/1.34  
% 2.34/1.34  Simplification rules
% 2.34/1.34  ----------------------
% 2.34/1.34  #Subsume      : 17
% 2.34/1.34  #Demod        : 40
% 2.34/1.34  #Tautology    : 12
% 2.34/1.34  #SimpNegUnit  : 12
% 2.34/1.34  #BackRed      : 0
% 2.34/1.34  
% 2.34/1.34  #Partial instantiations: 0
% 2.34/1.34  #Strategies tried      : 1
% 2.34/1.34  
% 2.34/1.34  Timing (in seconds)
% 2.34/1.34  ----------------------
% 2.34/1.34  Preprocessing        : 0.30
% 2.34/1.34  Parsing              : 0.16
% 2.34/1.34  CNF conversion       : 0.02
% 2.34/1.34  Main loop            : 0.21
% 2.34/1.35  Inferencing          : 0.08
% 2.34/1.35  Reduction            : 0.06
% 2.34/1.35  Demodulation         : 0.04
% 2.34/1.35  BG Simplification    : 0.02
% 2.34/1.35  Subsumption          : 0.05
% 2.34/1.35  Abstraction          : 0.01
% 2.34/1.35  MUC search           : 0.00
% 2.34/1.35  Cooper               : 0.00
% 2.34/1.35  Total                : 0.55
% 2.34/1.35  Index Insertion      : 0.00
% 2.34/1.35  Index Deletion       : 0.00
% 2.34/1.35  Index Matching       : 0.00
% 2.34/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
