%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2034+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:47 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 685 expanded)
%              Number of leaves         :   31 ( 285 expanded)
%              Depth                    :   21
%              Number of atoms          :  560 (5806 expanded)
%              Number of equality atoms :   16 ( 216 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > m2_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_209,negated_conjecture,(
    ~ ! [A] :
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

tff(f_28,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_136,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r3_waybel_9(A,B,C)
                  & ! [D] :
                      ( m2_yellow_6(D,A,B)
                     => ~ r2_hidden(C,k10_yellow_6(A,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m2_yellow_6(C,A,B)
         => ( ~ v2_struct_0(C)
            & v4_orders_2(C)
            & v7_waybel_0(C)
            & l1_waybel_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

tff(f_168,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( ~ r2_hidden(C,k10_yellow_6(A,B))
                  & ! [D] :
                      ( m2_yellow_6(D,A,B)
                     => ? [E] :
                          ( m2_yellow_6(E,A,D)
                          & r2_hidden(C,k10_yellow_6(A,E)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_yellow_6)).

tff(f_80,axiom,(
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

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m2_yellow_6(C,A,B)
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r3_waybel_9(A,C,D)
                   => r3_waybel_9(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_38,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_36,plain,(
    v7_waybel_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_34,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_131,plain,(
    ! [A_110,B_111,C_112] :
      ( m2_yellow_6('#skF_2'(A_110,B_111,C_112),A_110,B_111)
      | ~ r3_waybel_9(A_110,B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ l1_waybel_0(B_111,A_110)
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_8,plain,(
    ! [C_5,A_2,B_3] :
      ( v4_orders_2(C_5)
      | ~ m2_yellow_6(C_5,A_2,B_3)
      | ~ l1_waybel_0(B_3,A_2)
      | ~ v7_waybel_0(B_3)
      | ~ v4_orders_2(B_3)
      | v2_struct_0(B_3)
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_165,plain,(
    ! [A_118,B_119,C_120] :
      ( v4_orders_2('#skF_2'(A_118,B_119,C_120))
      | ~ l1_struct_0(A_118)
      | ~ r3_waybel_9(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ l1_waybel_0(B_119,A_118)
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc(A_118)
      | ~ v2_pre_topc(A_118)
      | v2_struct_0(A_118) ) ),
    inference(resolution,[status(thm)],[c_131,c_8])).

tff(c_169,plain,(
    ! [B_119] :
      ( v4_orders_2('#skF_2'('#skF_4',B_119,'#skF_6'))
      | ~ l1_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_119,'#skF_6')
      | ~ l1_waybel_0(B_119,'#skF_4')
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_165])).

tff(c_173,plain,(
    ! [B_119] :
      ( v4_orders_2('#skF_2'('#skF_4',B_119,'#skF_6'))
      | ~ l1_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_119,'#skF_6')
      | ~ l1_waybel_0(B_119,'#skF_4')
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_169])).

tff(c_174,plain,(
    ! [B_119] :
      ( v4_orders_2('#skF_2'('#skF_4',B_119,'#skF_6'))
      | ~ l1_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_119,'#skF_6')
      | ~ l1_waybel_0(B_119,'#skF_4')
      | ~ v7_waybel_0(B_119)
      | ~ v4_orders_2(B_119)
      | v2_struct_0(B_119) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_173])).

tff(c_175,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_186,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_175])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_186])).

tff(c_192,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_205,plain,(
    ! [A_130,B_131,C_132] :
      ( m2_yellow_6('#skF_3'(A_130,B_131,C_132),A_130,B_131)
      | r2_hidden(C_132,k10_yellow_6(A_130,B_131))
      | ~ m1_subset_1(C_132,u1_struct_0(A_130))
      | ~ l1_waybel_0(B_131,A_130)
      | ~ v7_waybel_0(B_131)
      | ~ v4_orders_2(B_131)
      | v2_struct_0(B_131)
      | ~ l1_pre_topc(A_130)
      | ~ v2_pre_topc(A_130)
      | v2_struct_0(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_10,plain,(
    ! [C_5,A_2,B_3] :
      ( ~ v2_struct_0(C_5)
      | ~ m2_yellow_6(C_5,A_2,B_3)
      | ~ l1_waybel_0(B_3,A_2)
      | ~ v7_waybel_0(B_3)
      | ~ v4_orders_2(B_3)
      | v2_struct_0(B_3)
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_248,plain,(
    ! [A_144,B_145,C_146] :
      ( ~ v2_struct_0('#skF_3'(A_144,B_145,C_146))
      | ~ l1_struct_0(A_144)
      | r2_hidden(C_146,k10_yellow_6(A_144,B_145))
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ l1_waybel_0(B_145,A_144)
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(resolution,[status(thm)],[c_205,c_10])).

tff(c_26,plain,(
    ~ r2_hidden('#skF_6',k10_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_251,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_248,c_26])).

tff(c_254,plain,
    ( ~ v2_struct_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_30,c_192,c_251])).

tff(c_255,plain,(
    ~ v2_struct_0('#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_254])).

tff(c_240,plain,(
    ! [A_141,B_142,C_143] :
      ( v4_orders_2('#skF_3'(A_141,B_142,C_143))
      | ~ l1_struct_0(A_141)
      | r2_hidden(C_143,k10_yellow_6(A_141,B_142))
      | ~ m1_subset_1(C_143,u1_struct_0(A_141))
      | ~ l1_waybel_0(B_142,A_141)
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ l1_pre_topc(A_141)
      | ~ v2_pre_topc(A_141)
      | v2_struct_0(A_141) ) ),
    inference(resolution,[status(thm)],[c_205,c_8])).

tff(c_243,plain,
    ( v4_orders_2('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_240,c_26])).

tff(c_246,plain,
    ( v4_orders_2('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_30,c_192,c_243])).

tff(c_247,plain,(
    v4_orders_2('#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_246])).

tff(c_6,plain,(
    ! [C_5,A_2,B_3] :
      ( v7_waybel_0(C_5)
      | ~ m2_yellow_6(C_5,A_2,B_3)
      | ~ l1_waybel_0(B_3,A_2)
      | ~ v7_waybel_0(B_3)
      | ~ v4_orders_2(B_3)
      | v2_struct_0(B_3)
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_278,plain,(
    ! [A_155,B_156,C_157] :
      ( v7_waybel_0('#skF_3'(A_155,B_156,C_157))
      | ~ l1_struct_0(A_155)
      | r2_hidden(C_157,k10_yellow_6(A_155,B_156))
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ l1_waybel_0(B_156,A_155)
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156)
      | ~ l1_pre_topc(A_155)
      | ~ v2_pre_topc(A_155)
      | v2_struct_0(A_155) ) ),
    inference(resolution,[status(thm)],[c_205,c_6])).

tff(c_281,plain,
    ( v7_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_278,c_26])).

tff(c_284,plain,
    ( v7_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_30,c_192,c_281])).

tff(c_285,plain,(
    v7_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_284])).

tff(c_4,plain,(
    ! [C_5,A_2,B_3] :
      ( l1_waybel_0(C_5,A_2)
      | ~ m2_yellow_6(C_5,A_2,B_3)
      | ~ l1_waybel_0(B_3,A_2)
      | ~ v7_waybel_0(B_3)
      | ~ v4_orders_2(B_3)
      | v2_struct_0(B_3)
      | ~ l1_struct_0(A_2)
      | v2_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_287,plain,(
    ! [A_160,B_161,C_162] :
      ( l1_waybel_0('#skF_3'(A_160,B_161,C_162),A_160)
      | ~ l1_struct_0(A_160)
      | r2_hidden(C_162,k10_yellow_6(A_160,B_161))
      | ~ m1_subset_1(C_162,u1_struct_0(A_160))
      | ~ l1_waybel_0(B_161,A_160)
      | ~ v7_waybel_0(B_161)
      | ~ v4_orders_2(B_161)
      | v2_struct_0(B_161)
      | ~ l1_pre_topc(A_160)
      | ~ v2_pre_topc(A_160)
      | v2_struct_0(A_160) ) ),
    inference(resolution,[status(thm)],[c_205,c_4])).

tff(c_290,plain,
    ( l1_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_287,c_26])).

tff(c_293,plain,
    ( l1_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_30,c_192,c_290])).

tff(c_294,plain,(
    l1_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_293])).

tff(c_46,plain,(
    v8_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_44,plain,(
    v1_compts_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_24,plain,(
    ! [A_41,B_57,C_65] :
      ( m2_yellow_6('#skF_3'(A_41,B_57,C_65),A_41,B_57)
      | r2_hidden(C_65,k10_yellow_6(A_41,B_57))
      | ~ m1_subset_1(C_65,u1_struct_0(A_41))
      | ~ l1_waybel_0(B_57,A_41)
      | ~ v7_waybel_0(B_57)
      | ~ v4_orders_2(B_57)
      | v2_struct_0(B_57)
      | ~ l1_pre_topc(A_41)
      | ~ v2_pre_topc(A_41)
      | v2_struct_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_14,plain,(
    ! [A_6,B_10] :
      ( m1_subset_1('#skF_1'(A_6,B_10),u1_struct_0(A_6))
      | ~ l1_waybel_0(B_10,A_6)
      | ~ v7_waybel_0(B_10)
      | ~ v4_orders_2(B_10)
      | v2_struct_0(B_10)
      | ~ l1_pre_topc(A_6)
      | ~ v1_compts_1(A_6)
      | ~ v8_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [A_6,B_10] :
      ( r3_waybel_9(A_6,B_10,'#skF_1'(A_6,B_10))
      | ~ l1_waybel_0(B_10,A_6)
      | ~ v7_waybel_0(B_10)
      | ~ v4_orders_2(B_10)
      | v2_struct_0(B_10)
      | ~ l1_pre_topc(A_6)
      | ~ v1_compts_1(A_6)
      | ~ v8_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_148,plain,(
    ! [A_113,B_114,D_115,C_116] :
      ( r3_waybel_9(A_113,B_114,D_115)
      | ~ r3_waybel_9(A_113,C_116,D_115)
      | ~ m1_subset_1(D_115,u1_struct_0(A_113))
      | ~ m2_yellow_6(C_116,A_113,B_114)
      | ~ l1_waybel_0(B_114,A_113)
      | ~ v7_waybel_0(B_114)
      | ~ v4_orders_2(B_114)
      | v2_struct_0(B_114)
      | ~ l1_pre_topc(A_113)
      | ~ v2_pre_topc(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_309,plain,(
    ! [A_169,B_170,B_171] :
      ( r3_waybel_9(A_169,B_170,'#skF_1'(A_169,B_171))
      | ~ m1_subset_1('#skF_1'(A_169,B_171),u1_struct_0(A_169))
      | ~ m2_yellow_6(B_171,A_169,B_170)
      | ~ l1_waybel_0(B_170,A_169)
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170)
      | ~ l1_waybel_0(B_171,A_169)
      | ~ v7_waybel_0(B_171)
      | ~ v4_orders_2(B_171)
      | v2_struct_0(B_171)
      | ~ l1_pre_topc(A_169)
      | ~ v1_compts_1(A_169)
      | ~ v8_pre_topc(A_169)
      | ~ v2_pre_topc(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_12,c_148])).

tff(c_344,plain,(
    ! [A_176,B_177,B_178] :
      ( r3_waybel_9(A_176,B_177,'#skF_1'(A_176,B_178))
      | ~ m2_yellow_6(B_178,A_176,B_177)
      | ~ l1_waybel_0(B_177,A_176)
      | ~ v7_waybel_0(B_177)
      | ~ v4_orders_2(B_177)
      | v2_struct_0(B_177)
      | ~ l1_waybel_0(B_178,A_176)
      | ~ v7_waybel_0(B_178)
      | ~ v4_orders_2(B_178)
      | v2_struct_0(B_178)
      | ~ l1_pre_topc(A_176)
      | ~ v1_compts_1(A_176)
      | ~ v8_pre_topc(A_176)
      | ~ v2_pre_topc(A_176)
      | v2_struct_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_14,c_309])).

tff(c_71,plain,(
    ! [A_105,B_106] :
      ( m1_subset_1('#skF_1'(A_105,B_106),u1_struct_0(A_105))
      | ~ l1_waybel_0(B_106,A_105)
      | ~ v7_waybel_0(B_106)
      | ~ v4_orders_2(B_106)
      | v2_struct_0(B_106)
      | ~ l1_pre_topc(A_105)
      | ~ v1_compts_1(A_105)
      | ~ v8_pre_topc(A_105)
      | ~ v2_pre_topc(A_105)
      | v2_struct_0(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    r3_waybel_9('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_52,plain,(
    ! [D_88,C_89] :
      ( D_88 = C_89
      | ~ r3_waybel_9('#skF_4','#skF_5',D_88)
      | ~ r3_waybel_9('#skF_4','#skF_5',C_89)
      | ~ m1_subset_1(D_88,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_89,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_54,plain,(
    ! [C_89] :
      ( C_89 = '#skF_6'
      | ~ r3_waybel_9('#skF_4','#skF_5','#skF_6')
      | ~ r3_waybel_9('#skF_4','#skF_5',C_89)
      | ~ m1_subset_1(C_89,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_30,c_52])).

tff(c_57,plain,(
    ! [C_89] :
      ( C_89 = '#skF_6'
      | ~ r3_waybel_9('#skF_4','#skF_5',C_89)
      | ~ m1_subset_1(C_89,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_54])).

tff(c_75,plain,(
    ! [B_106] :
      ( '#skF_1'('#skF_4',B_106) = '#skF_6'
      | ~ r3_waybel_9('#skF_4','#skF_5','#skF_1'('#skF_4',B_106))
      | ~ l1_waybel_0(B_106,'#skF_4')
      | ~ v7_waybel_0(B_106)
      | ~ v4_orders_2(B_106)
      | v2_struct_0(B_106)
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_71,c_57])).

tff(c_81,plain,(
    ! [B_106] :
      ( '#skF_1'('#skF_4',B_106) = '#skF_6'
      | ~ r3_waybel_9('#skF_4','#skF_5','#skF_1'('#skF_4',B_106))
      | ~ l1_waybel_0(B_106,'#skF_4')
      | ~ v7_waybel_0(B_106)
      | ~ v4_orders_2(B_106)
      | v2_struct_0(B_106)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_75])).

tff(c_82,plain,(
    ! [B_106] :
      ( '#skF_1'('#skF_4',B_106) = '#skF_6'
      | ~ r3_waybel_9('#skF_4','#skF_5','#skF_1'('#skF_4',B_106))
      | ~ l1_waybel_0(B_106,'#skF_4')
      | ~ v7_waybel_0(B_106)
      | ~ v4_orders_2(B_106)
      | v2_struct_0(B_106) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_81])).

tff(c_353,plain,(
    ! [B_178] :
      ( '#skF_1'('#skF_4',B_178) = '#skF_6'
      | ~ m2_yellow_6(B_178,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | ~ v7_waybel_0('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_178,'#skF_4')
      | ~ v7_waybel_0(B_178)
      | ~ v4_orders_2(B_178)
      | v2_struct_0(B_178)
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_344,c_82])).

tff(c_364,plain,(
    ! [B_178] :
      ( '#skF_1'('#skF_4',B_178) = '#skF_6'
      | ~ m2_yellow_6(B_178,'#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_178,'#skF_4')
      | ~ v7_waybel_0(B_178)
      | ~ v4_orders_2(B_178)
      | v2_struct_0(B_178)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_38,c_36,c_34,c_353])).

tff(c_369,plain,(
    ! [B_179] :
      ( '#skF_1'('#skF_4',B_179) = '#skF_6'
      | ~ m2_yellow_6(B_179,'#skF_4','#skF_5')
      | ~ l1_waybel_0(B_179,'#skF_4')
      | ~ v7_waybel_0(B_179)
      | ~ v4_orders_2(B_179)
      | v2_struct_0(B_179) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_364])).

tff(c_373,plain,(
    ! [C_65] :
      ( '#skF_1'('#skF_4','#skF_3'('#skF_4','#skF_5',C_65)) = '#skF_6'
      | ~ l1_waybel_0('#skF_3'('#skF_4','#skF_5',C_65),'#skF_4')
      | ~ v7_waybel_0('#skF_3'('#skF_4','#skF_5',C_65))
      | ~ v4_orders_2('#skF_3'('#skF_4','#skF_5',C_65))
      | v2_struct_0('#skF_3'('#skF_4','#skF_5',C_65))
      | r2_hidden(C_65,k10_yellow_6('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_65,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | ~ v7_waybel_0('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_369])).

tff(c_380,plain,(
    ! [C_65] :
      ( '#skF_1'('#skF_4','#skF_3'('#skF_4','#skF_5',C_65)) = '#skF_6'
      | ~ l1_waybel_0('#skF_3'('#skF_4','#skF_5',C_65),'#skF_4')
      | ~ v7_waybel_0('#skF_3'('#skF_4','#skF_5',C_65))
      | ~ v4_orders_2('#skF_3'('#skF_4','#skF_5',C_65))
      | v2_struct_0('#skF_3'('#skF_4','#skF_5',C_65))
      | r2_hidden(C_65,k10_yellow_6('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_65,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_373])).

tff(c_492,plain,(
    ! [C_191] :
      ( '#skF_1'('#skF_4','#skF_3'('#skF_4','#skF_5',C_191)) = '#skF_6'
      | ~ l1_waybel_0('#skF_3'('#skF_4','#skF_5',C_191),'#skF_4')
      | ~ v7_waybel_0('#skF_3'('#skF_4','#skF_5',C_191))
      | ~ v4_orders_2('#skF_3'('#skF_4','#skF_5',C_191))
      | v2_struct_0('#skF_3'('#skF_4','#skF_5',C_191))
      | r2_hidden(C_191,k10_yellow_6('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_191,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_380])).

tff(c_495,plain,
    ( '#skF_1'('#skF_4','#skF_3'('#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ l1_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ v7_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_492,c_26])).

tff(c_498,plain,
    ( '#skF_1'('#skF_4','#skF_3'('#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | v2_struct_0('#skF_3'('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_247,c_285,c_294,c_495])).

tff(c_499,plain,(
    '#skF_1'('#skF_4','#skF_3'('#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_255,c_498])).

tff(c_522,plain,
    ( r3_waybel_9('#skF_4','#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ v7_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_compts_1('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_499,c_12])).

tff(c_547,plain,
    ( r3_waybel_9('#skF_4','#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_6')
    | v2_struct_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_247,c_285,c_294,c_522])).

tff(c_548,plain,(
    r3_waybel_9('#skF_4','#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_255,c_547])).

tff(c_18,plain,(
    ! [C_39,A_27,B_35] :
      ( r2_hidden(C_39,k10_yellow_6(A_27,'#skF_2'(A_27,B_35,C_39)))
      | ~ r3_waybel_9(A_27,B_35,C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_27))
      | ~ l1_waybel_0(B_35,A_27)
      | ~ v7_waybel_0(B_35)
      | ~ v4_orders_2(B_35)
      | v2_struct_0(B_35)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_20,plain,(
    ! [A_27,B_35,C_39] :
      ( m2_yellow_6('#skF_2'(A_27,B_35,C_39),A_27,B_35)
      | ~ r3_waybel_9(A_27,B_35,C_39)
      | ~ m1_subset_1(C_39,u1_struct_0(A_27))
      | ~ l1_waybel_0(B_35,A_27)
      | ~ v7_waybel_0(B_35)
      | ~ v4_orders_2(B_35)
      | v2_struct_0(B_35)
      | ~ l1_pre_topc(A_27)
      | ~ v2_pre_topc(A_27)
      | v2_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_266,plain,(
    ! [C_150,A_151,E_152,B_153] :
      ( ~ r2_hidden(C_150,k10_yellow_6(A_151,E_152))
      | ~ m2_yellow_6(E_152,A_151,'#skF_3'(A_151,B_153,C_150))
      | r2_hidden(C_150,k10_yellow_6(A_151,B_153))
      | ~ m1_subset_1(C_150,u1_struct_0(A_151))
      | ~ l1_waybel_0(B_153,A_151)
      | ~ v7_waybel_0(B_153)
      | ~ v4_orders_2(B_153)
      | v2_struct_0(B_153)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_318,plain,(
    ! [C_172,A_173,B_174,C_175] :
      ( ~ r2_hidden(C_172,k10_yellow_6(A_173,'#skF_2'(A_173,'#skF_3'(A_173,B_174,C_172),C_175)))
      | r2_hidden(C_172,k10_yellow_6(A_173,B_174))
      | ~ m1_subset_1(C_172,u1_struct_0(A_173))
      | ~ l1_waybel_0(B_174,A_173)
      | ~ v7_waybel_0(B_174)
      | ~ v4_orders_2(B_174)
      | v2_struct_0(B_174)
      | ~ r3_waybel_9(A_173,'#skF_3'(A_173,B_174,C_172),C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ l1_waybel_0('#skF_3'(A_173,B_174,C_172),A_173)
      | ~ v7_waybel_0('#skF_3'(A_173,B_174,C_172))
      | ~ v4_orders_2('#skF_3'(A_173,B_174,C_172))
      | v2_struct_0('#skF_3'(A_173,B_174,C_172))
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_20,c_266])).

tff(c_668,plain,(
    ! [C_197,A_198,B_199] :
      ( r2_hidden(C_197,k10_yellow_6(A_198,B_199))
      | ~ l1_waybel_0(B_199,A_198)
      | ~ v7_waybel_0(B_199)
      | ~ v4_orders_2(B_199)
      | v2_struct_0(B_199)
      | ~ r3_waybel_9(A_198,'#skF_3'(A_198,B_199,C_197),C_197)
      | ~ m1_subset_1(C_197,u1_struct_0(A_198))
      | ~ l1_waybel_0('#skF_3'(A_198,B_199,C_197),A_198)
      | ~ v7_waybel_0('#skF_3'(A_198,B_199,C_197))
      | ~ v4_orders_2('#skF_3'(A_198,B_199,C_197))
      | v2_struct_0('#skF_3'(A_198,B_199,C_197))
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(resolution,[status(thm)],[c_18,c_318])).

tff(c_671,plain,
    ( r2_hidden('#skF_6',k10_yellow_6('#skF_4','#skF_5'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ v7_waybel_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_548,c_668])).

tff(c_682,plain,
    ( r2_hidden('#skF_6',k10_yellow_6('#skF_4','#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_247,c_285,c_294,c_30,c_38,c_36,c_34,c_671])).

tff(c_684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_255,c_40,c_26,c_682])).

%------------------------------------------------------------------------------
