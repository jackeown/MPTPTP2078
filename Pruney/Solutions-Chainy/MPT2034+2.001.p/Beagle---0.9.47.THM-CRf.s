%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:20 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
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
%$ r3_waybel_9 > m2_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(v8_pre_topc,type,(
    v8_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_210,negated_conjecture,(
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

tff(f_29,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_169,axiom,(
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

tff(f_55,axiom,(
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

tff(f_87,axiom,(
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

tff(f_113,axiom,(
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

tff(f_140,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_48,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_42,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_38,plain,(
    v4_orders_2('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_36,plain,(
    v7_waybel_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_34,plain,(
    l1_waybel_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_30,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_2,plain,(
    ! [A_1] :
      ( l1_struct_0(A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_110,B_111,C_112] :
      ( m2_yellow_6('#skF_3'(A_110,B_111,C_112),A_110,B_111)
      | ~ r3_waybel_9(A_110,B_111,C_112)
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ l1_waybel_0(B_111,A_110)
      | ~ v7_waybel_0(B_111)
      | ~ v4_orders_2(B_111)
      | v2_struct_0(B_111)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

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
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_149,plain,(
    ! [A_116,B_117,C_118] :
      ( v4_orders_2('#skF_3'(A_116,B_117,C_118))
      | ~ l1_struct_0(A_116)
      | ~ r3_waybel_9(A_116,B_117,C_118)
      | ~ m1_subset_1(C_118,u1_struct_0(A_116))
      | ~ l1_waybel_0(B_117,A_116)
      | ~ v7_waybel_0(B_117)
      | ~ v4_orders_2(B_117)
      | v2_struct_0(B_117)
      | ~ l1_pre_topc(A_116)
      | ~ v2_pre_topc(A_116)
      | v2_struct_0(A_116) ) ),
    inference(resolution,[status(thm)],[c_131,c_8])).

tff(c_153,plain,(
    ! [B_117] :
      ( v4_orders_2('#skF_3'('#skF_4',B_117,'#skF_6'))
      | ~ l1_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_117,'#skF_6')
      | ~ l1_waybel_0(B_117,'#skF_4')
      | ~ v7_waybel_0(B_117)
      | ~ v4_orders_2(B_117)
      | v2_struct_0(B_117)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_149])).

tff(c_157,plain,(
    ! [B_117] :
      ( v4_orders_2('#skF_3'('#skF_4',B_117,'#skF_6'))
      | ~ l1_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_117,'#skF_6')
      | ~ l1_waybel_0(B_117,'#skF_4')
      | ~ v7_waybel_0(B_117)
      | ~ v4_orders_2(B_117)
      | v2_struct_0(B_117)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_153])).

tff(c_158,plain,(
    ! [B_117] :
      ( v4_orders_2('#skF_3'('#skF_4',B_117,'#skF_6'))
      | ~ l1_struct_0('#skF_4')
      | ~ r3_waybel_9('#skF_4',B_117,'#skF_6')
      | ~ l1_waybel_0(B_117,'#skF_4')
      | ~ v7_waybel_0(B_117)
      | ~ v4_orders_2(B_117)
      | v2_struct_0(B_117) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_157])).

tff(c_159,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_158])).

tff(c_162,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_159])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_162])).

tff(c_168,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_158])).

tff(c_192,plain,(
    ! [A_131,B_132,C_133] :
      ( m2_yellow_6('#skF_1'(A_131,B_132,C_133),A_131,B_132)
      | r2_hidden(C_133,k10_yellow_6(A_131,B_132))
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ l1_waybel_0(B_132,A_131)
      | ~ v7_waybel_0(B_132)
      | ~ v4_orders_2(B_132)
      | v2_struct_0(B_132)
      | ~ l1_pre_topc(A_131)
      | ~ v2_pre_topc(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

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
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_250,plain,(
    ! [A_144,B_145,C_146] :
      ( ~ v2_struct_0('#skF_1'(A_144,B_145,C_146))
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
    inference(resolution,[status(thm)],[c_192,c_10])).

tff(c_26,plain,(
    ~ r2_hidden('#skF_6',k10_yellow_6('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_253,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_250,c_26])).

tff(c_256,plain,
    ( ~ v2_struct_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_30,c_168,c_253])).

tff(c_257,plain,(
    ~ v2_struct_0('#skF_1'('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_256])).

tff(c_258,plain,(
    ! [A_147,B_148,C_149] :
      ( v4_orders_2('#skF_1'(A_147,B_148,C_149))
      | ~ l1_struct_0(A_147)
      | r2_hidden(C_149,k10_yellow_6(A_147,B_148))
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ l1_waybel_0(B_148,A_147)
      | ~ v7_waybel_0(B_148)
      | ~ v4_orders_2(B_148)
      | v2_struct_0(B_148)
      | ~ l1_pre_topc(A_147)
      | ~ v2_pre_topc(A_147)
      | v2_struct_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_192,c_8])).

tff(c_261,plain,
    ( v4_orders_2('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_258,c_26])).

tff(c_264,plain,
    ( v4_orders_2('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_30,c_168,c_261])).

tff(c_265,plain,(
    v4_orders_2('#skF_1'('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_264])).

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
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_231,plain,(
    ! [A_137,B_138,C_139] :
      ( v7_waybel_0('#skF_1'(A_137,B_138,C_139))
      | ~ l1_struct_0(A_137)
      | r2_hidden(C_139,k10_yellow_6(A_137,B_138))
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ l1_waybel_0(B_138,A_137)
      | ~ v7_waybel_0(B_138)
      | ~ v4_orders_2(B_138)
      | v2_struct_0(B_138)
      | ~ l1_pre_topc(A_137)
      | ~ v2_pre_topc(A_137)
      | v2_struct_0(A_137) ) ),
    inference(resolution,[status(thm)],[c_192,c_6])).

tff(c_234,plain,
    ( v7_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_231,c_26])).

tff(c_237,plain,
    ( v7_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_30,c_168,c_234])).

tff(c_238,plain,(
    v7_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_237])).

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
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_277,plain,(
    ! [A_154,B_155,C_156] :
      ( l1_waybel_0('#skF_1'(A_154,B_155,C_156),A_154)
      | ~ l1_struct_0(A_154)
      | r2_hidden(C_156,k10_yellow_6(A_154,B_155))
      | ~ m1_subset_1(C_156,u1_struct_0(A_154))
      | ~ l1_waybel_0(B_155,A_154)
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | v2_struct_0(A_154) ) ),
    inference(resolution,[status(thm)],[c_192,c_4])).

tff(c_280,plain,
    ( l1_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ l1_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_277,c_26])).

tff(c_283,plain,
    ( l1_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_30,c_168,c_280])).

tff(c_284,plain,(
    l1_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_283])).

tff(c_46,plain,(
    v8_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_44,plain,(
    v1_compts_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_14,plain,(
    ! [A_6,B_22,C_30] :
      ( m2_yellow_6('#skF_1'(A_6,B_22,C_30),A_6,B_22)
      | r2_hidden(C_30,k10_yellow_6(A_6,B_22))
      | ~ m1_subset_1(C_30,u1_struct_0(A_6))
      | ~ l1_waybel_0(B_22,A_6)
      | ~ v7_waybel_0(B_22)
      | ~ v4_orders_2(B_22)
      | v2_struct_0(B_22)
      | ~ l1_pre_topc(A_6)
      | ~ v2_pre_topc(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18,plain,(
    ! [A_36,B_40] :
      ( m1_subset_1('#skF_2'(A_36,B_40),u1_struct_0(A_36))
      | ~ l1_waybel_0(B_40,A_36)
      | ~ v7_waybel_0(B_40)
      | ~ v4_orders_2(B_40)
      | v2_struct_0(B_40)
      | ~ l1_pre_topc(A_36)
      | ~ v1_compts_1(A_36)
      | ~ v8_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_16,plain,(
    ! [A_36,B_40] :
      ( r3_waybel_9(A_36,B_40,'#skF_2'(A_36,B_40))
      | ~ l1_waybel_0(B_40,A_36)
      | ~ v7_waybel_0(B_40)
      | ~ v4_orders_2(B_40)
      | v2_struct_0(B_40)
      | ~ l1_pre_topc(A_36)
      | ~ v1_compts_1(A_36)
      | ~ v8_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_182,plain,(
    ! [A_127,B_128,D_129,C_130] :
      ( r3_waybel_9(A_127,B_128,D_129)
      | ~ r3_waybel_9(A_127,C_130,D_129)
      | ~ m1_subset_1(D_129,u1_struct_0(A_127))
      | ~ m2_yellow_6(C_130,A_127,B_128)
      | ~ l1_waybel_0(B_128,A_127)
      | ~ v7_waybel_0(B_128)
      | ~ v4_orders_2(B_128)
      | v2_struct_0(B_128)
      | ~ l1_pre_topc(A_127)
      | ~ v2_pre_topc(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_300,plain,(
    ! [A_165,B_166,B_167] :
      ( r3_waybel_9(A_165,B_166,'#skF_2'(A_165,B_167))
      | ~ m1_subset_1('#skF_2'(A_165,B_167),u1_struct_0(A_165))
      | ~ m2_yellow_6(B_167,A_165,B_166)
      | ~ l1_waybel_0(B_166,A_165)
      | ~ v7_waybel_0(B_166)
      | ~ v4_orders_2(B_166)
      | v2_struct_0(B_166)
      | ~ l1_waybel_0(B_167,A_165)
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_165)
      | ~ v1_compts_1(A_165)
      | ~ v8_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_16,c_182])).

tff(c_309,plain,(
    ! [A_168,B_169,B_170] :
      ( r3_waybel_9(A_168,B_169,'#skF_2'(A_168,B_170))
      | ~ m2_yellow_6(B_170,A_168,B_169)
      | ~ l1_waybel_0(B_169,A_168)
      | ~ v7_waybel_0(B_169)
      | ~ v4_orders_2(B_169)
      | v2_struct_0(B_169)
      | ~ l1_waybel_0(B_170,A_168)
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc(A_168)
      | ~ v1_compts_1(A_168)
      | ~ v8_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(resolution,[status(thm)],[c_18,c_300])).

tff(c_70,plain,(
    ! [A_103,B_104] :
      ( m1_subset_1('#skF_2'(A_103,B_104),u1_struct_0(A_103))
      | ~ l1_waybel_0(B_104,A_103)
      | ~ v7_waybel_0(B_104)
      | ~ v4_orders_2(B_104)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc(A_103)
      | ~ v1_compts_1(A_103)
      | ~ v8_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_28,plain,(
    r3_waybel_9('#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_52,plain,(
    ! [D_88,C_89] :
      ( D_88 = C_89
      | ~ r3_waybel_9('#skF_4','#skF_5',D_88)
      | ~ r3_waybel_9('#skF_4','#skF_5',C_89)
      | ~ m1_subset_1(D_88,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(C_89,u1_struct_0('#skF_4')) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

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

tff(c_74,plain,(
    ! [B_104] :
      ( '#skF_2'('#skF_4',B_104) = '#skF_6'
      | ~ r3_waybel_9('#skF_4','#skF_5','#skF_2'('#skF_4',B_104))
      | ~ l1_waybel_0(B_104,'#skF_4')
      | ~ v7_waybel_0(B_104)
      | ~ v4_orders_2(B_104)
      | v2_struct_0(B_104)
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_57])).

tff(c_80,plain,(
    ! [B_104] :
      ( '#skF_2'('#skF_4',B_104) = '#skF_6'
      | ~ r3_waybel_9('#skF_4','#skF_5','#skF_2'('#skF_4',B_104))
      | ~ l1_waybel_0(B_104,'#skF_4')
      | ~ v7_waybel_0(B_104)
      | ~ v4_orders_2(B_104)
      | v2_struct_0(B_104)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_74])).

tff(c_81,plain,(
    ! [B_104] :
      ( '#skF_2'('#skF_4',B_104) = '#skF_6'
      | ~ r3_waybel_9('#skF_4','#skF_5','#skF_2'('#skF_4',B_104))
      | ~ l1_waybel_0(B_104,'#skF_4')
      | ~ v7_waybel_0(B_104)
      | ~ v4_orders_2(B_104)
      | v2_struct_0(B_104) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_80])).

tff(c_318,plain,(
    ! [B_170] :
      ( '#skF_2'('#skF_4',B_170) = '#skF_6'
      | ~ m2_yellow_6(B_170,'#skF_4','#skF_5')
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | ~ v7_waybel_0('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_170,'#skF_4')
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170)
      | ~ l1_pre_topc('#skF_4')
      | ~ v1_compts_1('#skF_4')
      | ~ v8_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_309,c_81])).

tff(c_329,plain,(
    ! [B_170] :
      ( '#skF_2'('#skF_4',B_170) = '#skF_6'
      | ~ m2_yellow_6(B_170,'#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_170,'#skF_4')
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_38,c_36,c_34,c_318])).

tff(c_334,plain,(
    ! [B_171] :
      ( '#skF_2'('#skF_4',B_171) = '#skF_6'
      | ~ m2_yellow_6(B_171,'#skF_4','#skF_5')
      | ~ l1_waybel_0(B_171,'#skF_4')
      | ~ v7_waybel_0(B_171)
      | ~ v4_orders_2(B_171)
      | v2_struct_0(B_171) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_329])).

tff(c_338,plain,(
    ! [C_30] :
      ( '#skF_2'('#skF_4','#skF_1'('#skF_4','#skF_5',C_30)) = '#skF_6'
      | ~ l1_waybel_0('#skF_1'('#skF_4','#skF_5',C_30),'#skF_4')
      | ~ v7_waybel_0('#skF_1'('#skF_4','#skF_5',C_30))
      | ~ v4_orders_2('#skF_1'('#skF_4','#skF_5',C_30))
      | v2_struct_0('#skF_1'('#skF_4','#skF_5',C_30))
      | r2_hidden(C_30,k10_yellow_6('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_30,u1_struct_0('#skF_4'))
      | ~ l1_waybel_0('#skF_5','#skF_4')
      | ~ v7_waybel_0('#skF_5')
      | ~ v4_orders_2('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_14,c_334])).

tff(c_345,plain,(
    ! [C_30] :
      ( '#skF_2'('#skF_4','#skF_1'('#skF_4','#skF_5',C_30)) = '#skF_6'
      | ~ l1_waybel_0('#skF_1'('#skF_4','#skF_5',C_30),'#skF_4')
      | ~ v7_waybel_0('#skF_1'('#skF_4','#skF_5',C_30))
      | ~ v4_orders_2('#skF_1'('#skF_4','#skF_5',C_30))
      | v2_struct_0('#skF_1'('#skF_4','#skF_5',C_30))
      | r2_hidden(C_30,k10_yellow_6('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_30,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_38,c_36,c_34,c_338])).

tff(c_494,plain,(
    ! [C_187] :
      ( '#skF_2'('#skF_4','#skF_1'('#skF_4','#skF_5',C_187)) = '#skF_6'
      | ~ l1_waybel_0('#skF_1'('#skF_4','#skF_5',C_187),'#skF_4')
      | ~ v7_waybel_0('#skF_1'('#skF_4','#skF_5',C_187))
      | ~ v4_orders_2('#skF_1'('#skF_4','#skF_5',C_187))
      | v2_struct_0('#skF_1'('#skF_4','#skF_5',C_187))
      | r2_hidden(C_187,k10_yellow_6('#skF_4','#skF_5'))
      | ~ m1_subset_1(C_187,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_345])).

tff(c_497,plain,
    ( '#skF_2'('#skF_4','#skF_1'('#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | ~ l1_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_494,c_26])).

tff(c_500,plain,
    ( '#skF_2'('#skF_4','#skF_1'('#skF_4','#skF_5','#skF_6')) = '#skF_6'
    | v2_struct_0('#skF_1'('#skF_4','#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_265,c_238,c_284,c_497])).

tff(c_501,plain,(
    '#skF_2'('#skF_4','#skF_1'('#skF_4','#skF_5','#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_500])).

tff(c_518,plain,
    ( r3_waybel_9('#skF_4','#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_6')
    | ~ l1_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v1_compts_1('#skF_4')
    | ~ v8_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_16])).

tff(c_543,plain,
    ( r3_waybel_9('#skF_4','#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_6')
    | v2_struct_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_265,c_238,c_284,c_518])).

tff(c_544,plain,(
    r3_waybel_9('#skF_4','#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_257,c_543])).

tff(c_22,plain,(
    ! [C_69,A_57,B_65] :
      ( r2_hidden(C_69,k10_yellow_6(A_57,'#skF_3'(A_57,B_65,C_69)))
      | ~ r3_waybel_9(A_57,B_65,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_57))
      | ~ l1_waybel_0(B_65,A_57)
      | ~ v7_waybel_0(B_65)
      | ~ v4_orders_2(B_65)
      | v2_struct_0(B_65)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_24,plain,(
    ! [A_57,B_65,C_69] :
      ( m2_yellow_6('#skF_3'(A_57,B_65,C_69),A_57,B_65)
      | ~ r3_waybel_9(A_57,B_65,C_69)
      | ~ m1_subset_1(C_69,u1_struct_0(A_57))
      | ~ l1_waybel_0(B_65,A_57)
      | ~ v7_waybel_0(B_65)
      | ~ v4_orders_2(B_65)
      | v2_struct_0(B_65)
      | ~ l1_pre_topc(A_57)
      | ~ v2_pre_topc(A_57)
      | v2_struct_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_266,plain,(
    ! [C_150,A_151,E_152,B_153] :
      ( ~ r2_hidden(C_150,k10_yellow_6(A_151,E_152))
      | ~ m2_yellow_6(E_152,A_151,'#skF_1'(A_151,B_153,C_150))
      | r2_hidden(C_150,k10_yellow_6(A_151,B_153))
      | ~ m1_subset_1(C_150,u1_struct_0(A_151))
      | ~ l1_waybel_0(B_153,A_151)
      | ~ v7_waybel_0(B_153)
      | ~ v4_orders_2(B_153)
      | v2_struct_0(B_153)
      | ~ l1_pre_topc(A_151)
      | ~ v2_pre_topc(A_151)
      | v2_struct_0(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_351,plain,(
    ! [C_172,A_173,B_174,C_175] :
      ( ~ r2_hidden(C_172,k10_yellow_6(A_173,'#skF_3'(A_173,'#skF_1'(A_173,B_174,C_172),C_175)))
      | r2_hidden(C_172,k10_yellow_6(A_173,B_174))
      | ~ m1_subset_1(C_172,u1_struct_0(A_173))
      | ~ l1_waybel_0(B_174,A_173)
      | ~ v7_waybel_0(B_174)
      | ~ v4_orders_2(B_174)
      | v2_struct_0(B_174)
      | ~ r3_waybel_9(A_173,'#skF_1'(A_173,B_174,C_172),C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ l1_waybel_0('#skF_1'(A_173,B_174,C_172),A_173)
      | ~ v7_waybel_0('#skF_1'(A_173,B_174,C_172))
      | ~ v4_orders_2('#skF_1'(A_173,B_174,C_172))
      | v2_struct_0('#skF_1'(A_173,B_174,C_172))
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(resolution,[status(thm)],[c_24,c_266])).

tff(c_661,plain,(
    ! [C_195,A_196,B_197] :
      ( r2_hidden(C_195,k10_yellow_6(A_196,B_197))
      | ~ l1_waybel_0(B_197,A_196)
      | ~ v7_waybel_0(B_197)
      | ~ v4_orders_2(B_197)
      | v2_struct_0(B_197)
      | ~ r3_waybel_9(A_196,'#skF_1'(A_196,B_197,C_195),C_195)
      | ~ m1_subset_1(C_195,u1_struct_0(A_196))
      | ~ l1_waybel_0('#skF_1'(A_196,B_197,C_195),A_196)
      | ~ v7_waybel_0('#skF_1'(A_196,B_197,C_195))
      | ~ v4_orders_2('#skF_1'(A_196,B_197,C_195))
      | v2_struct_0('#skF_1'(A_196,B_197,C_195))
      | ~ l1_pre_topc(A_196)
      | ~ v2_pre_topc(A_196)
      | v2_struct_0(A_196) ) ),
    inference(resolution,[status(thm)],[c_22,c_351])).

tff(c_664,plain,
    ( r2_hidden('#skF_6',k10_yellow_6('#skF_4','#skF_5'))
    | ~ l1_waybel_0('#skF_5','#skF_4')
    | ~ v7_waybel_0('#skF_5')
    | ~ v4_orders_2('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ l1_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ v7_waybel_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | ~ v4_orders_2('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_544,c_661])).

tff(c_675,plain,
    ( r2_hidden('#skF_6',k10_yellow_6('#skF_4','#skF_5'))
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_1'('#skF_4','#skF_5','#skF_6'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_42,c_265,c_238,c_284,c_30,c_38,c_36,c_34,c_664])).

tff(c_677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_257,c_40,c_26,c_675])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:00:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.58  %$ r3_waybel_9 > m2_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > #skF_1 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2
% 3.32/1.58  
% 3.32/1.58  %Foreground sorts:
% 3.32/1.58  
% 3.32/1.58  
% 3.32/1.58  %Background operators:
% 3.32/1.58  
% 3.32/1.58  
% 3.32/1.58  %Foreground operators:
% 3.32/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.32/1.58  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 3.32/1.58  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 3.32/1.58  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.58  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 3.32/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.32/1.58  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 3.32/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.32/1.58  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 3.32/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.58  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.32/1.58  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.58  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 3.32/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.32/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.32/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.32/1.58  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 3.32/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.58  
% 3.32/1.61  tff(f_210, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ((![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((r3_waybel_9(A, B, C) & r3_waybel_9(A, B, D)) => (C = D)))))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) => r2_hidden(C, k10_yellow_6(A, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_waybel_9)).
% 3.32/1.61  tff(f_29, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.32/1.61  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 3.32/1.61  tff(f_55, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 3.32/1.61  tff(f_87, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(~r2_hidden(C, k10_yellow_6(A, B)) & (![D]: (m2_yellow_6(D, A, B) => (?[E]: (m2_yellow_6(E, A, D) & r2_hidden(C, k10_yellow_6(A, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_yellow_6)).
% 3.32/1.61  tff(f_113, axiom, (![A]: (((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & v1_compts_1(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_waybel_9)).
% 3.32/1.61  tff(f_140, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_waybel_9)).
% 3.32/1.61  tff(c_50, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_40, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_48, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_42, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_38, plain, (v4_orders_2('#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_36, plain, (v7_waybel_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_34, plain, (l1_waybel_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_30, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_2, plain, (![A_1]: (l1_struct_0(A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.61  tff(c_131, plain, (![A_110, B_111, C_112]: (m2_yellow_6('#skF_3'(A_110, B_111, C_112), A_110, B_111) | ~r3_waybel_9(A_110, B_111, C_112) | ~m1_subset_1(C_112, u1_struct_0(A_110)) | ~l1_waybel_0(B_111, A_110) | ~v7_waybel_0(B_111) | ~v4_orders_2(B_111) | v2_struct_0(B_111) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.32/1.61  tff(c_8, plain, (![C_5, A_2, B_3]: (v4_orders_2(C_5) | ~m2_yellow_6(C_5, A_2, B_3) | ~l1_waybel_0(B_3, A_2) | ~v7_waybel_0(B_3) | ~v4_orders_2(B_3) | v2_struct_0(B_3) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.61  tff(c_149, plain, (![A_116, B_117, C_118]: (v4_orders_2('#skF_3'(A_116, B_117, C_118)) | ~l1_struct_0(A_116) | ~r3_waybel_9(A_116, B_117, C_118) | ~m1_subset_1(C_118, u1_struct_0(A_116)) | ~l1_waybel_0(B_117, A_116) | ~v7_waybel_0(B_117) | ~v4_orders_2(B_117) | v2_struct_0(B_117) | ~l1_pre_topc(A_116) | ~v2_pre_topc(A_116) | v2_struct_0(A_116))), inference(resolution, [status(thm)], [c_131, c_8])).
% 3.32/1.61  tff(c_153, plain, (![B_117]: (v4_orders_2('#skF_3'('#skF_4', B_117, '#skF_6')) | ~l1_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_117, '#skF_6') | ~l1_waybel_0(B_117, '#skF_4') | ~v7_waybel_0(B_117) | ~v4_orders_2(B_117) | v2_struct_0(B_117) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_149])).
% 3.32/1.61  tff(c_157, plain, (![B_117]: (v4_orders_2('#skF_3'('#skF_4', B_117, '#skF_6')) | ~l1_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_117, '#skF_6') | ~l1_waybel_0(B_117, '#skF_4') | ~v7_waybel_0(B_117) | ~v4_orders_2(B_117) | v2_struct_0(B_117) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_153])).
% 3.32/1.61  tff(c_158, plain, (![B_117]: (v4_orders_2('#skF_3'('#skF_4', B_117, '#skF_6')) | ~l1_struct_0('#skF_4') | ~r3_waybel_9('#skF_4', B_117, '#skF_6') | ~l1_waybel_0(B_117, '#skF_4') | ~v7_waybel_0(B_117) | ~v4_orders_2(B_117) | v2_struct_0(B_117))), inference(negUnitSimplification, [status(thm)], [c_50, c_157])).
% 3.32/1.61  tff(c_159, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_158])).
% 3.32/1.61  tff(c_162, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_2, c_159])).
% 3.32/1.61  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_162])).
% 3.32/1.61  tff(c_168, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_158])).
% 3.32/1.61  tff(c_192, plain, (![A_131, B_132, C_133]: (m2_yellow_6('#skF_1'(A_131, B_132, C_133), A_131, B_132) | r2_hidden(C_133, k10_yellow_6(A_131, B_132)) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~l1_waybel_0(B_132, A_131) | ~v7_waybel_0(B_132) | ~v4_orders_2(B_132) | v2_struct_0(B_132) | ~l1_pre_topc(A_131) | ~v2_pre_topc(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.61  tff(c_10, plain, (![C_5, A_2, B_3]: (~v2_struct_0(C_5) | ~m2_yellow_6(C_5, A_2, B_3) | ~l1_waybel_0(B_3, A_2) | ~v7_waybel_0(B_3) | ~v4_orders_2(B_3) | v2_struct_0(B_3) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.61  tff(c_250, plain, (![A_144, B_145, C_146]: (~v2_struct_0('#skF_1'(A_144, B_145, C_146)) | ~l1_struct_0(A_144) | r2_hidden(C_146, k10_yellow_6(A_144, B_145)) | ~m1_subset_1(C_146, u1_struct_0(A_144)) | ~l1_waybel_0(B_145, A_144) | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(resolution, [status(thm)], [c_192, c_10])).
% 3.32/1.61  tff(c_26, plain, (~r2_hidden('#skF_6', k10_yellow_6('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_253, plain, (~v2_struct_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | ~v7_waybel_0('#skF_5') | ~v4_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_250, c_26])).
% 3.32/1.61  tff(c_256, plain, (~v2_struct_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_38, c_36, c_34, c_30, c_168, c_253])).
% 3.32/1.61  tff(c_257, plain, (~v2_struct_0('#skF_1'('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_256])).
% 3.32/1.61  tff(c_258, plain, (![A_147, B_148, C_149]: (v4_orders_2('#skF_1'(A_147, B_148, C_149)) | ~l1_struct_0(A_147) | r2_hidden(C_149, k10_yellow_6(A_147, B_148)) | ~m1_subset_1(C_149, u1_struct_0(A_147)) | ~l1_waybel_0(B_148, A_147) | ~v7_waybel_0(B_148) | ~v4_orders_2(B_148) | v2_struct_0(B_148) | ~l1_pre_topc(A_147) | ~v2_pre_topc(A_147) | v2_struct_0(A_147))), inference(resolution, [status(thm)], [c_192, c_8])).
% 3.32/1.61  tff(c_261, plain, (v4_orders_2('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | ~v7_waybel_0('#skF_5') | ~v4_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_258, c_26])).
% 3.32/1.61  tff(c_264, plain, (v4_orders_2('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_38, c_36, c_34, c_30, c_168, c_261])).
% 3.32/1.61  tff(c_265, plain, (v4_orders_2('#skF_1'('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_264])).
% 3.32/1.61  tff(c_6, plain, (![C_5, A_2, B_3]: (v7_waybel_0(C_5) | ~m2_yellow_6(C_5, A_2, B_3) | ~l1_waybel_0(B_3, A_2) | ~v7_waybel_0(B_3) | ~v4_orders_2(B_3) | v2_struct_0(B_3) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.61  tff(c_231, plain, (![A_137, B_138, C_139]: (v7_waybel_0('#skF_1'(A_137, B_138, C_139)) | ~l1_struct_0(A_137) | r2_hidden(C_139, k10_yellow_6(A_137, B_138)) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~l1_waybel_0(B_138, A_137) | ~v7_waybel_0(B_138) | ~v4_orders_2(B_138) | v2_struct_0(B_138) | ~l1_pre_topc(A_137) | ~v2_pre_topc(A_137) | v2_struct_0(A_137))), inference(resolution, [status(thm)], [c_192, c_6])).
% 3.32/1.61  tff(c_234, plain, (v7_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | ~v7_waybel_0('#skF_5') | ~v4_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_231, c_26])).
% 3.32/1.61  tff(c_237, plain, (v7_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_38, c_36, c_34, c_30, c_168, c_234])).
% 3.32/1.61  tff(c_238, plain, (v7_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_237])).
% 3.32/1.61  tff(c_4, plain, (![C_5, A_2, B_3]: (l1_waybel_0(C_5, A_2) | ~m2_yellow_6(C_5, A_2, B_3) | ~l1_waybel_0(B_3, A_2) | ~v7_waybel_0(B_3) | ~v4_orders_2(B_3) | v2_struct_0(B_3) | ~l1_struct_0(A_2) | v2_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.61  tff(c_277, plain, (![A_154, B_155, C_156]: (l1_waybel_0('#skF_1'(A_154, B_155, C_156), A_154) | ~l1_struct_0(A_154) | r2_hidden(C_156, k10_yellow_6(A_154, B_155)) | ~m1_subset_1(C_156, u1_struct_0(A_154)) | ~l1_waybel_0(B_155, A_154) | ~v7_waybel_0(B_155) | ~v4_orders_2(B_155) | v2_struct_0(B_155) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | v2_struct_0(A_154))), inference(resolution, [status(thm)], [c_192, c_4])).
% 3.32/1.61  tff(c_280, plain, (l1_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~l1_struct_0('#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | ~v7_waybel_0('#skF_5') | ~v4_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_277, c_26])).
% 3.32/1.61  tff(c_283, plain, (l1_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_38, c_36, c_34, c_30, c_168, c_280])).
% 3.32/1.61  tff(c_284, plain, (l1_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_283])).
% 3.32/1.61  tff(c_46, plain, (v8_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_44, plain, (v1_compts_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_14, plain, (![A_6, B_22, C_30]: (m2_yellow_6('#skF_1'(A_6, B_22, C_30), A_6, B_22) | r2_hidden(C_30, k10_yellow_6(A_6, B_22)) | ~m1_subset_1(C_30, u1_struct_0(A_6)) | ~l1_waybel_0(B_22, A_6) | ~v7_waybel_0(B_22) | ~v4_orders_2(B_22) | v2_struct_0(B_22) | ~l1_pre_topc(A_6) | ~v2_pre_topc(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.61  tff(c_18, plain, (![A_36, B_40]: (m1_subset_1('#skF_2'(A_36, B_40), u1_struct_0(A_36)) | ~l1_waybel_0(B_40, A_36) | ~v7_waybel_0(B_40) | ~v4_orders_2(B_40) | v2_struct_0(B_40) | ~l1_pre_topc(A_36) | ~v1_compts_1(A_36) | ~v8_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.61  tff(c_16, plain, (![A_36, B_40]: (r3_waybel_9(A_36, B_40, '#skF_2'(A_36, B_40)) | ~l1_waybel_0(B_40, A_36) | ~v7_waybel_0(B_40) | ~v4_orders_2(B_40) | v2_struct_0(B_40) | ~l1_pre_topc(A_36) | ~v1_compts_1(A_36) | ~v8_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.61  tff(c_182, plain, (![A_127, B_128, D_129, C_130]: (r3_waybel_9(A_127, B_128, D_129) | ~r3_waybel_9(A_127, C_130, D_129) | ~m1_subset_1(D_129, u1_struct_0(A_127)) | ~m2_yellow_6(C_130, A_127, B_128) | ~l1_waybel_0(B_128, A_127) | ~v7_waybel_0(B_128) | ~v4_orders_2(B_128) | v2_struct_0(B_128) | ~l1_pre_topc(A_127) | ~v2_pre_topc(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.32/1.61  tff(c_300, plain, (![A_165, B_166, B_167]: (r3_waybel_9(A_165, B_166, '#skF_2'(A_165, B_167)) | ~m1_subset_1('#skF_2'(A_165, B_167), u1_struct_0(A_165)) | ~m2_yellow_6(B_167, A_165, B_166) | ~l1_waybel_0(B_166, A_165) | ~v7_waybel_0(B_166) | ~v4_orders_2(B_166) | v2_struct_0(B_166) | ~l1_waybel_0(B_167, A_165) | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~l1_pre_topc(A_165) | ~v1_compts_1(A_165) | ~v8_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_16, c_182])).
% 3.32/1.61  tff(c_309, plain, (![A_168, B_169, B_170]: (r3_waybel_9(A_168, B_169, '#skF_2'(A_168, B_170)) | ~m2_yellow_6(B_170, A_168, B_169) | ~l1_waybel_0(B_169, A_168) | ~v7_waybel_0(B_169) | ~v4_orders_2(B_169) | v2_struct_0(B_169) | ~l1_waybel_0(B_170, A_168) | ~v7_waybel_0(B_170) | ~v4_orders_2(B_170) | v2_struct_0(B_170) | ~l1_pre_topc(A_168) | ~v1_compts_1(A_168) | ~v8_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(resolution, [status(thm)], [c_18, c_300])).
% 3.32/1.61  tff(c_70, plain, (![A_103, B_104]: (m1_subset_1('#skF_2'(A_103, B_104), u1_struct_0(A_103)) | ~l1_waybel_0(B_104, A_103) | ~v7_waybel_0(B_104) | ~v4_orders_2(B_104) | v2_struct_0(B_104) | ~l1_pre_topc(A_103) | ~v1_compts_1(A_103) | ~v8_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.32/1.61  tff(c_28, plain, (r3_waybel_9('#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_52, plain, (![D_88, C_89]: (D_88=C_89 | ~r3_waybel_9('#skF_4', '#skF_5', D_88) | ~r3_waybel_9('#skF_4', '#skF_5', C_89) | ~m1_subset_1(D_88, u1_struct_0('#skF_4')) | ~m1_subset_1(C_89, u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 3.32/1.61  tff(c_54, plain, (![C_89]: (C_89='#skF_6' | ~r3_waybel_9('#skF_4', '#skF_5', '#skF_6') | ~r3_waybel_9('#skF_4', '#skF_5', C_89) | ~m1_subset_1(C_89, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_30, c_52])).
% 3.32/1.61  tff(c_57, plain, (![C_89]: (C_89='#skF_6' | ~r3_waybel_9('#skF_4', '#skF_5', C_89) | ~m1_subset_1(C_89, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_54])).
% 3.32/1.61  tff(c_74, plain, (![B_104]: ('#skF_2'('#skF_4', B_104)='#skF_6' | ~r3_waybel_9('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_104)) | ~l1_waybel_0(B_104, '#skF_4') | ~v7_waybel_0(B_104) | ~v4_orders_2(B_104) | v2_struct_0(B_104) | ~l1_pre_topc('#skF_4') | ~v1_compts_1('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_57])).
% 3.32/1.61  tff(c_80, plain, (![B_104]: ('#skF_2'('#skF_4', B_104)='#skF_6' | ~r3_waybel_9('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_104)) | ~l1_waybel_0(B_104, '#skF_4') | ~v7_waybel_0(B_104) | ~v4_orders_2(B_104) | v2_struct_0(B_104) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_74])).
% 3.32/1.61  tff(c_81, plain, (![B_104]: ('#skF_2'('#skF_4', B_104)='#skF_6' | ~r3_waybel_9('#skF_4', '#skF_5', '#skF_2'('#skF_4', B_104)) | ~l1_waybel_0(B_104, '#skF_4') | ~v7_waybel_0(B_104) | ~v4_orders_2(B_104) | v2_struct_0(B_104))), inference(negUnitSimplification, [status(thm)], [c_50, c_80])).
% 3.32/1.61  tff(c_318, plain, (![B_170]: ('#skF_2'('#skF_4', B_170)='#skF_6' | ~m2_yellow_6(B_170, '#skF_4', '#skF_5') | ~l1_waybel_0('#skF_5', '#skF_4') | ~v7_waybel_0('#skF_5') | ~v4_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~l1_waybel_0(B_170, '#skF_4') | ~v7_waybel_0(B_170) | ~v4_orders_2(B_170) | v2_struct_0(B_170) | ~l1_pre_topc('#skF_4') | ~v1_compts_1('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_309, c_81])).
% 3.32/1.61  tff(c_329, plain, (![B_170]: ('#skF_2'('#skF_4', B_170)='#skF_6' | ~m2_yellow_6(B_170, '#skF_4', '#skF_5') | v2_struct_0('#skF_5') | ~l1_waybel_0(B_170, '#skF_4') | ~v7_waybel_0(B_170) | ~v4_orders_2(B_170) | v2_struct_0(B_170) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_38, c_36, c_34, c_318])).
% 3.32/1.61  tff(c_334, plain, (![B_171]: ('#skF_2'('#skF_4', B_171)='#skF_6' | ~m2_yellow_6(B_171, '#skF_4', '#skF_5') | ~l1_waybel_0(B_171, '#skF_4') | ~v7_waybel_0(B_171) | ~v4_orders_2(B_171) | v2_struct_0(B_171))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_329])).
% 3.32/1.61  tff(c_338, plain, (![C_30]: ('#skF_2'('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_30))='#skF_6' | ~l1_waybel_0('#skF_1'('#skF_4', '#skF_5', C_30), '#skF_4') | ~v7_waybel_0('#skF_1'('#skF_4', '#skF_5', C_30)) | ~v4_orders_2('#skF_1'('#skF_4', '#skF_5', C_30)) | v2_struct_0('#skF_1'('#skF_4', '#skF_5', C_30)) | r2_hidden(C_30, k10_yellow_6('#skF_4', '#skF_5')) | ~m1_subset_1(C_30, u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_5', '#skF_4') | ~v7_waybel_0('#skF_5') | ~v4_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_14, c_334])).
% 3.32/1.61  tff(c_345, plain, (![C_30]: ('#skF_2'('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_30))='#skF_6' | ~l1_waybel_0('#skF_1'('#skF_4', '#skF_5', C_30), '#skF_4') | ~v7_waybel_0('#skF_1'('#skF_4', '#skF_5', C_30)) | ~v4_orders_2('#skF_1'('#skF_4', '#skF_5', C_30)) | v2_struct_0('#skF_1'('#skF_4', '#skF_5', C_30)) | r2_hidden(C_30, k10_yellow_6('#skF_4', '#skF_5')) | ~m1_subset_1(C_30, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_38, c_36, c_34, c_338])).
% 3.32/1.61  tff(c_494, plain, (![C_187]: ('#skF_2'('#skF_4', '#skF_1'('#skF_4', '#skF_5', C_187))='#skF_6' | ~l1_waybel_0('#skF_1'('#skF_4', '#skF_5', C_187), '#skF_4') | ~v7_waybel_0('#skF_1'('#skF_4', '#skF_5', C_187)) | ~v4_orders_2('#skF_1'('#skF_4', '#skF_5', C_187)) | v2_struct_0('#skF_1'('#skF_4', '#skF_5', C_187)) | r2_hidden(C_187, k10_yellow_6('#skF_4', '#skF_5')) | ~m1_subset_1(C_187, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_345])).
% 3.32/1.61  tff(c_497, plain, ('#skF_2'('#skF_4', '#skF_1'('#skF_4', '#skF_5', '#skF_6'))='#skF_6' | ~l1_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~v7_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | ~v4_orders_2('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_494, c_26])).
% 3.32/1.61  tff(c_500, plain, ('#skF_2'('#skF_4', '#skF_1'('#skF_4', '#skF_5', '#skF_6'))='#skF_6' | v2_struct_0('#skF_1'('#skF_4', '#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_265, c_238, c_284, c_497])).
% 3.32/1.61  tff(c_501, plain, ('#skF_2'('#skF_4', '#skF_1'('#skF_4', '#skF_5', '#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_257, c_500])).
% 3.32/1.61  tff(c_518, plain, (r3_waybel_9('#skF_4', '#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_6') | ~l1_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~v7_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | ~v4_orders_2('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_4') | ~v1_compts_1('#skF_4') | ~v8_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_501, c_16])).
% 3.32/1.61  tff(c_543, plain, (r3_waybel_9('#skF_4', '#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_6') | v2_struct_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_265, c_238, c_284, c_518])).
% 3.32/1.61  tff(c_544, plain, (r3_waybel_9('#skF_4', '#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_50, c_257, c_543])).
% 3.32/1.61  tff(c_22, plain, (![C_69, A_57, B_65]: (r2_hidden(C_69, k10_yellow_6(A_57, '#skF_3'(A_57, B_65, C_69))) | ~r3_waybel_9(A_57, B_65, C_69) | ~m1_subset_1(C_69, u1_struct_0(A_57)) | ~l1_waybel_0(B_65, A_57) | ~v7_waybel_0(B_65) | ~v4_orders_2(B_65) | v2_struct_0(B_65) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.32/1.61  tff(c_24, plain, (![A_57, B_65, C_69]: (m2_yellow_6('#skF_3'(A_57, B_65, C_69), A_57, B_65) | ~r3_waybel_9(A_57, B_65, C_69) | ~m1_subset_1(C_69, u1_struct_0(A_57)) | ~l1_waybel_0(B_65, A_57) | ~v7_waybel_0(B_65) | ~v4_orders_2(B_65) | v2_struct_0(B_65) | ~l1_pre_topc(A_57) | ~v2_pre_topc(A_57) | v2_struct_0(A_57))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.32/1.61  tff(c_266, plain, (![C_150, A_151, E_152, B_153]: (~r2_hidden(C_150, k10_yellow_6(A_151, E_152)) | ~m2_yellow_6(E_152, A_151, '#skF_1'(A_151, B_153, C_150)) | r2_hidden(C_150, k10_yellow_6(A_151, B_153)) | ~m1_subset_1(C_150, u1_struct_0(A_151)) | ~l1_waybel_0(B_153, A_151) | ~v7_waybel_0(B_153) | ~v4_orders_2(B_153) | v2_struct_0(B_153) | ~l1_pre_topc(A_151) | ~v2_pre_topc(A_151) | v2_struct_0(A_151))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.61  tff(c_351, plain, (![C_172, A_173, B_174, C_175]: (~r2_hidden(C_172, k10_yellow_6(A_173, '#skF_3'(A_173, '#skF_1'(A_173, B_174, C_172), C_175))) | r2_hidden(C_172, k10_yellow_6(A_173, B_174)) | ~m1_subset_1(C_172, u1_struct_0(A_173)) | ~l1_waybel_0(B_174, A_173) | ~v7_waybel_0(B_174) | ~v4_orders_2(B_174) | v2_struct_0(B_174) | ~r3_waybel_9(A_173, '#skF_1'(A_173, B_174, C_172), C_175) | ~m1_subset_1(C_175, u1_struct_0(A_173)) | ~l1_waybel_0('#skF_1'(A_173, B_174, C_172), A_173) | ~v7_waybel_0('#skF_1'(A_173, B_174, C_172)) | ~v4_orders_2('#skF_1'(A_173, B_174, C_172)) | v2_struct_0('#skF_1'(A_173, B_174, C_172)) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(resolution, [status(thm)], [c_24, c_266])).
% 3.32/1.61  tff(c_661, plain, (![C_195, A_196, B_197]: (r2_hidden(C_195, k10_yellow_6(A_196, B_197)) | ~l1_waybel_0(B_197, A_196) | ~v7_waybel_0(B_197) | ~v4_orders_2(B_197) | v2_struct_0(B_197) | ~r3_waybel_9(A_196, '#skF_1'(A_196, B_197, C_195), C_195) | ~m1_subset_1(C_195, u1_struct_0(A_196)) | ~l1_waybel_0('#skF_1'(A_196, B_197, C_195), A_196) | ~v7_waybel_0('#skF_1'(A_196, B_197, C_195)) | ~v4_orders_2('#skF_1'(A_196, B_197, C_195)) | v2_struct_0('#skF_1'(A_196, B_197, C_195)) | ~l1_pre_topc(A_196) | ~v2_pre_topc(A_196) | v2_struct_0(A_196))), inference(resolution, [status(thm)], [c_22, c_351])).
% 3.32/1.61  tff(c_664, plain, (r2_hidden('#skF_6', k10_yellow_6('#skF_4', '#skF_5')) | ~l1_waybel_0('#skF_5', '#skF_4') | ~v7_waybel_0('#skF_5') | ~v4_orders_2('#skF_5') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~l1_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~v7_waybel_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | ~v4_orders_2('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_544, c_661])).
% 3.32/1.61  tff(c_675, plain, (r2_hidden('#skF_6', k10_yellow_6('#skF_4', '#skF_5')) | v2_struct_0('#skF_5') | v2_struct_0('#skF_1'('#skF_4', '#skF_5', '#skF_6')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_42, c_265, c_238, c_284, c_30, c_38, c_36, c_34, c_664])).
% 3.32/1.61  tff(c_677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_257, c_40, c_26, c_675])).
% 3.32/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.32/1.61  
% 3.32/1.61  Inference rules
% 3.32/1.61  ----------------------
% 3.32/1.61  #Ref     : 0
% 3.32/1.61  #Sup     : 101
% 3.32/1.61  #Fact    : 0
% 3.32/1.61  #Define  : 0
% 3.32/1.61  #Split   : 6
% 3.32/1.61  #Chain   : 0
% 3.32/1.61  #Close   : 0
% 3.32/1.61  
% 3.32/1.61  Ordering : KBO
% 3.32/1.61  
% 3.32/1.61  Simplification rules
% 3.32/1.61  ----------------------
% 3.32/1.61  #Subsume      : 23
% 3.32/1.61  #Demod        : 387
% 3.32/1.61  #Tautology    : 16
% 3.32/1.61  #SimpNegUnit  : 61
% 3.32/1.61  #BackRed      : 0
% 3.32/1.61  
% 3.32/1.61  #Partial instantiations: 0
% 3.32/1.61  #Strategies tried      : 1
% 3.32/1.61  
% 3.32/1.61  Timing (in seconds)
% 3.32/1.61  ----------------------
% 3.32/1.61  Preprocessing        : 0.35
% 3.32/1.61  Parsing              : 0.20
% 3.32/1.61  CNF conversion       : 0.03
% 3.32/1.61  Main loop            : 0.44
% 3.32/1.61  Inferencing          : 0.18
% 3.32/1.61  Reduction            : 0.13
% 3.32/1.61  Demodulation         : 0.10
% 3.32/1.61  BG Simplification    : 0.03
% 3.32/1.61  Subsumption          : 0.09
% 3.32/1.61  Abstraction          : 0.02
% 3.32/1.61  MUC search           : 0.00
% 3.32/1.61  Cooper               : 0.00
% 3.32/1.61  Total                : 0.84
% 3.32/1.61  Index Insertion      : 0.00
% 3.32/1.61  Index Deletion       : 0.00
% 3.32/1.61  Index Matching       : 0.00
% 3.32/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
