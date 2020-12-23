%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2076+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:51 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 532 expanded)
%              Number of leaves         :   23 ( 183 expanded)
%              Depth                    :   16
%              Number of atoms          :  286 (2918 expanded)
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

tff(f_105,negated_conjecture,(
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
             => ~ ( r2_hidden(B,k6_yellow_6(A))
                  & ! [C] :
                      ( m1_subset_1(C,u1_struct_0(A))
                     => ~ r3_waybel_9(A,B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_yellow19)).

tff(f_48,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l37_yellow19)).

tff(c_22,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_30,plain,
    ( v7_waybel_0('#skF_4')
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_65,plain,(
    ~ v1_compts_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_20,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_18,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_waybel_0('#skF_2'(A_7),A_7)
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_2'(A_7),k6_yellow_6(A_7))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_12,plain,(
    ! [A_7] :
      ( v7_waybel_0('#skF_2'(A_7))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_7] :
      ( v4_orders_2('#skF_2'(A_7))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    ! [B_21] :
      ( v1_compts_1('#skF_3')
      | r3_waybel_9('#skF_3',B_21,'#skF_5'(B_21))
      | ~ r2_hidden(B_21,k6_yellow_6('#skF_3'))
      | ~ l1_waybel_0(B_21,'#skF_3')
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_73,plain,(
    ! [B_30] :
      ( r3_waybel_9('#skF_3',B_30,'#skF_5'(B_30))
      | ~ r2_hidden(B_30,k6_yellow_6('#skF_3'))
      | ~ l1_waybel_0(B_30,'#skF_3')
      | ~ v7_waybel_0(B_30)
      | ~ v4_orders_2(B_30)
      | v2_struct_0(B_30) ) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_50])).

tff(c_6,plain,(
    ! [A_7,C_12] :
      ( ~ r3_waybel_9(A_7,'#skF_2'(A_7),C_12)
      | ~ m1_subset_1(C_12,u1_struct_0(A_7))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_77,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3'))
    | v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3'))
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ v4_orders_2('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_73,c_6])).

tff(c_80,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3'))
    | v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3'))
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ v4_orders_2('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_77])).

tff(c_81,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3'))
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ v4_orders_2('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_80])).

tff(c_91,plain,(
    ~ v4_orders_2('#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_94,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_91])).

tff(c_97,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_94])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_97])).

tff(c_101,plain,(
    v4_orders_2('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_64,plain,(
    ! [B_21] :
      ( v1_compts_1('#skF_3')
      | m1_subset_1('#skF_5'(B_21),u1_struct_0('#skF_3'))
      | ~ r2_hidden(B_21,k6_yellow_6('#skF_3'))
      | ~ l1_waybel_0(B_21,'#skF_3')
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_82,plain,(
    ! [B_21] :
      ( m1_subset_1('#skF_5'(B_21),u1_struct_0('#skF_3'))
      | ~ r2_hidden(B_21,k6_yellow_6('#skF_3'))
      | ~ l1_waybel_0(B_21,'#skF_3')
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21) ) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_64])).

tff(c_100,plain,
    ( ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3'))
    | ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_102,plain,(
    ~ m1_subset_1('#skF_5'('#skF_2'('#skF_3')),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_105,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3'))
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | ~ v4_orders_2('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(resolution,[status(thm)],[c_82,c_102])).

tff(c_108,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3'))
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_105])).

tff(c_109,plain,(
    ~ v7_waybel_0('#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_112,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_109])).

tff(c_115,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_115])).

tff(c_118,plain,
    ( ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_120,plain,(
    ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_123,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_120])).

tff(c_126,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_123])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_126])).

tff(c_129,plain,
    ( ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_131,plain,(
    ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_134,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_137,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_134])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_137])).

tff(c_140,plain,(
    v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_16,plain,(
    ! [A_7] :
      ( ~ v2_struct_0('#skF_2'(A_7))
      | v1_compts_1(A_7)
      | ~ l1_pre_topc(A_7)
      | ~ v2_pre_topc(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_144,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_140,c_16])).

tff(c_147,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_144])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_147])).

tff(c_150,plain,
    ( ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3'))
    | ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ v7_waybel_0('#skF_2'('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_152,plain,(
    ~ v7_waybel_0('#skF_2'('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_155,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_152])).

tff(c_158,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_155])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_158])).

tff(c_161,plain,
    ( ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3'))
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_163,plain,(
    ~ r2_hidden('#skF_2'('#skF_3'),k6_yellow_6('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_166,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_163])).

tff(c_169,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_169])).

tff(c_172,plain,
    ( ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3')
    | v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_174,plain,(
    ~ l1_waybel_0('#skF_2'('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_177,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_174])).

tff(c_180,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_177])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_180])).

tff(c_183,plain,(
    v2_struct_0('#skF_2'('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_187,plain,
    ( v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_16])).

tff(c_190,plain,
    ( v1_compts_1('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_187])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_65,c_190])).

tff(c_194,plain,(
    v1_compts_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( ~ v2_struct_0('#skF_4')
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_198,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_34])).

tff(c_32,plain,
    ( v4_orders_2('#skF_4')
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_196,plain,(
    v4_orders_2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_32])).

tff(c_193,plain,(
    v7_waybel_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_28,plain,
    ( l1_waybel_0('#skF_4','#skF_3')
    | ~ v1_compts_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_200,plain,(
    l1_waybel_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_28])).

tff(c_232,plain,(
    ! [A_47,B_48] :
      ( r3_waybel_9(A_47,B_48,'#skF_1'(A_47,B_48))
      | ~ l1_waybel_0(B_48,A_47)
      | ~ v7_waybel_0(B_48)
      | ~ v4_orders_2(B_48)
      | v2_struct_0(B_48)
      | ~ v1_compts_1(A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47)
      | v2_struct_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_222,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1('#skF_1'(A_44,B_45),u1_struct_0(A_44))
      | ~ l1_waybel_0(B_45,A_44)
      | ~ v7_waybel_0(B_45)
      | ~ v4_orders_2(B_45)
      | v2_struct_0(B_45)
      | ~ v1_compts_1(A_44)
      | ~ l1_pre_topc(A_44)
      | ~ v2_pre_topc(A_44)
      | v2_struct_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ! [C_20] :
      ( ~ r3_waybel_9('#skF_3','#skF_4',C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_3'))
      | ~ v1_compts_1('#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_204,plain,(
    ! [C_20] :
      ( ~ r3_waybel_9('#skF_3','#skF_4',C_20)
      | ~ m1_subset_1(C_20,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_24])).

tff(c_226,plain,(
    ! [B_45] :
      ( ~ r3_waybel_9('#skF_3','#skF_4','#skF_1'('#skF_3',B_45))
      | ~ l1_waybel_0(B_45,'#skF_3')
      | ~ v7_waybel_0(B_45)
      | ~ v4_orders_2(B_45)
      | v2_struct_0(B_45)
      | ~ v1_compts_1('#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_222,c_204])).

tff(c_229,plain,(
    ! [B_45] :
      ( ~ r3_waybel_9('#skF_3','#skF_4','#skF_1'('#skF_3',B_45))
      | ~ l1_waybel_0(B_45,'#skF_3')
      | ~ v7_waybel_0(B_45)
      | ~ v4_orders_2(B_45)
      | v2_struct_0(B_45)
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_194,c_226])).

tff(c_230,plain,(
    ! [B_45] :
      ( ~ r3_waybel_9('#skF_3','#skF_4','#skF_1'('#skF_3',B_45))
      | ~ l1_waybel_0(B_45,'#skF_3')
      | ~ v7_waybel_0(B_45)
      | ~ v4_orders_2(B_45)
      | v2_struct_0(B_45) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_229])).

tff(c_236,plain,
    ( ~ l1_waybel_0('#skF_4','#skF_3')
    | ~ v7_waybel_0('#skF_4')
    | ~ v4_orders_2('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ v1_compts_1('#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_232,c_230])).

tff(c_243,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_194,c_196,c_193,c_200,c_236])).

tff(c_245,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_198,c_243])).

%------------------------------------------------------------------------------
