%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT2077+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:51 EST 2020

% Result     : Theorem 9.25s
% Output     : CNFRefutation 9.46s
% Verified   : 
% Statistics : Number of formulae       :  255 (3419 expanded)
%              Number of leaves         :   45 (1129 expanded)
%              Depth                    :   37
%              Number of atoms          : 1191 (20723 expanded)
%              Number of equality atoms :   38 (  88 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > m2_yellow_6 > v3_yellow_6 > r2_hidden > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_7 > #skF_4 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(v3_yellow_6,type,(
    v3_yellow_6: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_251,negated_conjecture,(
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
                  ( m2_yellow_6(C,A,B)
                  & v3_yellow_6(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_yellow19)).

tff(f_209,axiom,(
    ! [A] :
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

tff(f_99,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k10_yellow_6(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

tff(f_215,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_123,axiom,(
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
             => ( r2_hidden(C,k10_yellow_6(A,B))
               => r3_waybel_9(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

tff(f_156,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_95,axiom,(
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

tff(f_226,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_46,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ( v3_yellow_6(B,A)
          <=> k10_yellow_6(A,B) != k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

tff(f_222,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_47,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_96,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_185,axiom,(
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

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_68,plain,
    ( ~ v2_struct_0('#skF_6')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_100,plain,(
    ~ v1_compts_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_56,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_54,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_40,plain,(
    ! [A_51] :
      ( v4_orders_2('#skF_4'(A_51))
      | v1_compts_1(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_94,plain,(
    ! [B_77] :
      ( v1_compts_1('#skF_5')
      | m2_yellow_6('#skF_7'(B_77),'#skF_5',B_77)
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_237,plain,(
    ! [B_77] :
      ( m2_yellow_6('#skF_7'(B_77),'#skF_5',B_77)
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_94])).

tff(c_22,plain,(
    ! [A_11] : m1_subset_1('#skF_1'(A_11),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_426,plain,(
    ! [A_143,B_144] :
      ( m1_subset_1(k10_yellow_6(A_143,B_144),k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_waybel_0(B_144,A_143)
      | ~ v7_waybel_0(B_144)
      | ~ v4_orders_2(B_144)
      | v2_struct_0(B_144)
      | ~ l1_pre_topc(A_143)
      | ~ v2_pre_topc(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_48,plain,(
    ! [A_62,C_64,B_63] :
      ( m1_subset_1(A_62,C_64)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_497,plain,(
    ! [A_164,A_165,B_166] :
      ( m1_subset_1(A_164,u1_struct_0(A_165))
      | ~ r2_hidden(A_164,k10_yellow_6(A_165,B_166))
      | ~ l1_waybel_0(B_166,A_165)
      | ~ v7_waybel_0(B_166)
      | ~ v4_orders_2(B_166)
      | v2_struct_0(B_166)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_426,c_48])).

tff(c_582,plain,(
    ! [A_183,A_184,B_185] :
      ( m1_subset_1(A_183,u1_struct_0(A_184))
      | ~ l1_waybel_0(B_185,A_184)
      | ~ v7_waybel_0(B_185)
      | ~ v4_orders_2(B_185)
      | v2_struct_0(B_185)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | v1_xboole_0(k10_yellow_6(A_184,B_185))
      | ~ m1_subset_1(A_183,k10_yellow_6(A_184,B_185)) ) ),
    inference(resolution,[status(thm)],[c_26,c_497])).

tff(c_602,plain,(
    ! [A_184,B_185] :
      ( m1_subset_1('#skF_1'(k10_yellow_6(A_184,B_185)),u1_struct_0(A_184))
      | ~ l1_waybel_0(B_185,A_184)
      | ~ v7_waybel_0(B_185)
      | ~ v4_orders_2(B_185)
      | v2_struct_0(B_185)
      | ~ l1_pre_topc(A_184)
      | ~ v2_pre_topc(A_184)
      | v2_struct_0(A_184)
      | v1_xboole_0(k10_yellow_6(A_184,B_185)) ) ),
    inference(resolution,[status(thm)],[c_22,c_582])).

tff(c_491,plain,(
    ! [A_161,B_162,C_163] :
      ( r3_waybel_9(A_161,B_162,C_163)
      | ~ r2_hidden(C_163,k10_yellow_6(A_161,B_162))
      | ~ m1_subset_1(C_163,u1_struct_0(A_161))
      | ~ l1_waybel_0(B_162,A_161)
      | ~ v7_waybel_0(B_162)
      | ~ v4_orders_2(B_162)
      | v2_struct_0(B_162)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_950,plain,(
    ! [A_223,B_224,A_225] :
      ( r3_waybel_9(A_223,B_224,A_225)
      | ~ m1_subset_1(A_225,u1_struct_0(A_223))
      | ~ l1_waybel_0(B_224,A_223)
      | ~ v7_waybel_0(B_224)
      | ~ v4_orders_2(B_224)
      | v2_struct_0(B_224)
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223)
      | v1_xboole_0(k10_yellow_6(A_223,B_224))
      | ~ m1_subset_1(A_225,k10_yellow_6(A_223,B_224)) ) ),
    inference(resolution,[status(thm)],[c_26,c_491])).

tff(c_1450,plain,(
    ! [A_248,B_249] :
      ( r3_waybel_9(A_248,B_249,'#skF_1'(k10_yellow_6(A_248,B_249)))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6(A_248,B_249)),u1_struct_0(A_248))
      | ~ l1_waybel_0(B_249,A_248)
      | ~ v7_waybel_0(B_249)
      | ~ v4_orders_2(B_249)
      | v2_struct_0(B_249)
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248)
      | v1_xboole_0(k10_yellow_6(A_248,B_249)) ) ),
    inference(resolution,[status(thm)],[c_22,c_950])).

tff(c_1468,plain,(
    ! [A_250,B_251] :
      ( r3_waybel_9(A_250,B_251,'#skF_1'(k10_yellow_6(A_250,B_251)))
      | ~ l1_waybel_0(B_251,A_250)
      | ~ v7_waybel_0(B_251)
      | ~ v4_orders_2(B_251)
      | v2_struct_0(B_251)
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250)
      | v1_xboole_0(k10_yellow_6(A_250,B_251)) ) ),
    inference(resolution,[status(thm)],[c_602,c_1450])).

tff(c_28,plain,(
    ! [A_22,B_30,D_36,C_34] :
      ( r3_waybel_9(A_22,B_30,D_36)
      | ~ r3_waybel_9(A_22,C_34,D_36)
      | ~ m1_subset_1(D_36,u1_struct_0(A_22))
      | ~ m2_yellow_6(C_34,A_22,B_30)
      | ~ l1_waybel_0(B_30,A_22)
      | ~ v7_waybel_0(B_30)
      | ~ v4_orders_2(B_30)
      | v2_struct_0(B_30)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4078,plain,(
    ! [A_384,B_385,B_386] :
      ( r3_waybel_9(A_384,B_385,'#skF_1'(k10_yellow_6(A_384,B_386)))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6(A_384,B_386)),u1_struct_0(A_384))
      | ~ m2_yellow_6(B_386,A_384,B_385)
      | ~ l1_waybel_0(B_385,A_384)
      | ~ v7_waybel_0(B_385)
      | ~ v4_orders_2(B_385)
      | v2_struct_0(B_385)
      | ~ l1_waybel_0(B_386,A_384)
      | ~ v7_waybel_0(B_386)
      | ~ v4_orders_2(B_386)
      | v2_struct_0(B_386)
      | ~ l1_pre_topc(A_384)
      | ~ v2_pre_topc(A_384)
      | v2_struct_0(A_384)
      | v1_xboole_0(k10_yellow_6(A_384,B_386)) ) ),
    inference(resolution,[status(thm)],[c_1468,c_28])).

tff(c_4085,plain,(
    ! [A_387,B_388,B_389] :
      ( r3_waybel_9(A_387,B_388,'#skF_1'(k10_yellow_6(A_387,B_389)))
      | ~ m2_yellow_6(B_389,A_387,B_388)
      | ~ l1_waybel_0(B_388,A_387)
      | ~ v7_waybel_0(B_388)
      | ~ v4_orders_2(B_388)
      | v2_struct_0(B_388)
      | ~ l1_waybel_0(B_389,A_387)
      | ~ v7_waybel_0(B_389)
      | ~ v4_orders_2(B_389)
      | v2_struct_0(B_389)
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387)
      | v1_xboole_0(k10_yellow_6(A_387,B_389)) ) ),
    inference(resolution,[status(thm)],[c_602,c_4078])).

tff(c_34,plain,(
    ! [A_51,C_61] :
      ( ~ r3_waybel_9(A_51,'#skF_4'(A_51),C_61)
      | ~ m1_subset_1(C_61,u1_struct_0(A_51))
      | v1_compts_1(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_4699,plain,(
    ! [A_406,B_407] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6(A_406,B_407)),u1_struct_0(A_406))
      | v1_compts_1(A_406)
      | ~ m2_yellow_6(B_407,A_406,'#skF_4'(A_406))
      | ~ l1_waybel_0('#skF_4'(A_406),A_406)
      | ~ v7_waybel_0('#skF_4'(A_406))
      | ~ v4_orders_2('#skF_4'(A_406))
      | v2_struct_0('#skF_4'(A_406))
      | ~ l1_waybel_0(B_407,A_406)
      | ~ v7_waybel_0(B_407)
      | ~ v4_orders_2(B_407)
      | v2_struct_0(B_407)
      | ~ l1_pre_topc(A_406)
      | ~ v2_pre_topc(A_406)
      | v2_struct_0(A_406)
      | v1_xboole_0(k10_yellow_6(A_406,B_407)) ) ),
    inference(resolution,[status(thm)],[c_4085,c_34])).

tff(c_4708,plain,(
    ! [A_408,B_409] :
      ( v1_compts_1(A_408)
      | ~ m2_yellow_6(B_409,A_408,'#skF_4'(A_408))
      | ~ l1_waybel_0('#skF_4'(A_408),A_408)
      | ~ v7_waybel_0('#skF_4'(A_408))
      | ~ v4_orders_2('#skF_4'(A_408))
      | v2_struct_0('#skF_4'(A_408))
      | ~ l1_waybel_0(B_409,A_408)
      | ~ v7_waybel_0(B_409)
      | ~ v4_orders_2(B_409)
      | v2_struct_0(B_409)
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408)
      | v1_xboole_0(k10_yellow_6(A_408,B_409)) ) ),
    inference(resolution,[status(thm)],[c_602,c_4699])).

tff(c_4716,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5')
    | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
    | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
    | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_237,c_4708])).

tff(c_4720,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5')
    | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
    | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
    | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
    | v2_struct_0('#skF_5')
    | v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4716])).

tff(c_4721,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5')
    | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
    | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
    | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
    | v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4720])).

tff(c_4722,plain,(
    ~ v4_orders_2('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4721])).

tff(c_4725,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_4722])).

tff(c_4728,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4725])).

tff(c_4730,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4728])).

tff(c_4732,plain,(
    v4_orders_2('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4721])).

tff(c_38,plain,(
    ! [A_51] :
      ( v7_waybel_0('#skF_4'(A_51))
      | v1_compts_1(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_36,plain,(
    ! [A_51] :
      ( l1_waybel_0('#skF_4'(A_51),A_51)
      | v1_compts_1(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_261,plain,(
    ! [C_116,A_117,B_118] :
      ( v7_waybel_0(C_116)
      | ~ m2_yellow_6(C_116,A_117,B_118)
      | ~ l1_waybel_0(B_118,A_117)
      | ~ v7_waybel_0(B_118)
      | ~ v4_orders_2(B_118)
      | v2_struct_0(B_118)
      | ~ l1_struct_0(A_117)
      | v2_struct_0(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_264,plain,(
    ! [B_77] :
      ( v7_waybel_0('#skF_7'(B_77))
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(resolution,[status(thm)],[c_237,c_261])).

tff(c_267,plain,(
    ! [B_77] :
      ( v7_waybel_0('#skF_7'(B_77))
      | ~ l1_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_264])).

tff(c_268,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_271,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_271])).

tff(c_277,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_298,plain,(
    ! [C_128,A_129,B_130] :
      ( l1_waybel_0(C_128,A_129)
      | ~ m2_yellow_6(C_128,A_129,B_130)
      | ~ l1_waybel_0(B_130,A_129)
      | ~ v7_waybel_0(B_130)
      | ~ v4_orders_2(B_130)
      | v2_struct_0(B_130)
      | ~ l1_struct_0(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_301,plain,(
    ! [B_77] :
      ( l1_waybel_0('#skF_7'(B_77),'#skF_5')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(resolution,[status(thm)],[c_237,c_298])).

tff(c_304,plain,(
    ! [B_77] :
      ( l1_waybel_0('#skF_7'(B_77),'#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_301])).

tff(c_305,plain,(
    ! [B_77] :
      ( l1_waybel_0('#skF_7'(B_77),'#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_304])).

tff(c_4731,plain,
    ( ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
    | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
    | ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5'))
    | v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_4721])).

tff(c_4733,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_4'('#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4731])).

tff(c_4740,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_305,c_4733])).

tff(c_4743,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4732,c_4740])).

tff(c_4744,plain,(
    ~ v7_waybel_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4743])).

tff(c_4747,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_4744])).

tff(c_4750,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4747])).

tff(c_4752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4750])).

tff(c_4753,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4743])).

tff(c_4755,plain,(
    ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4753])).

tff(c_4758,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_4755])).

tff(c_4761,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4758])).

tff(c_4763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4761])).

tff(c_4764,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4753])).

tff(c_42,plain,(
    ! [A_51] :
      ( ~ v2_struct_0('#skF_4'(A_51))
      | v1_compts_1(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_4768,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4764,c_42])).

tff(c_4771,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4768])).

tff(c_4773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4771])).

tff(c_4774,plain,
    ( ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
    | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
    | v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4731])).

tff(c_4776,plain,(
    ~ v7_waybel_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4774])).

tff(c_4783,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_4776])).

tff(c_4786,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4783])).

tff(c_4788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4786])).

tff(c_4790,plain,(
    v7_waybel_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4774])).

tff(c_276,plain,(
    ! [B_77] :
      ( v7_waybel_0('#skF_7'(B_77))
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_4789,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
    | ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5')))
    | v2_struct_0('#skF_4'('#skF_5'))
    | v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_4774])).

tff(c_4791,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_4789])).

tff(c_4794,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_276,c_4791])).

tff(c_4797,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4732,c_4790,c_4794])).

tff(c_4798,plain,(
    ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4797])).

tff(c_4801,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_4798])).

tff(c_4804,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4801])).

tff(c_4806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4804])).

tff(c_4807,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4797])).

tff(c_4811,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4807,c_42])).

tff(c_4814,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4811])).

tff(c_4816,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4814])).

tff(c_4817,plain,
    ( ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
    | ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
    | v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4789])).

tff(c_4819,plain,(
    ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_4817])).

tff(c_4826,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_4819])).

tff(c_4829,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4826])).

tff(c_4831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4829])).

tff(c_4833,plain,(
    l1_waybel_0('#skF_4'('#skF_5'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_4817])).

tff(c_278,plain,(
    ! [C_119,A_120,B_121] :
      ( v4_orders_2(C_119)
      | ~ m2_yellow_6(C_119,A_120,B_121)
      | ~ l1_waybel_0(B_121,A_120)
      | ~ v7_waybel_0(B_121)
      | ~ v4_orders_2(B_121)
      | v2_struct_0(B_121)
      | ~ l1_struct_0(A_120)
      | v2_struct_0(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_281,plain,(
    ! [B_77] :
      ( v4_orders_2('#skF_7'(B_77))
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(resolution,[status(thm)],[c_237,c_278])).

tff(c_284,plain,(
    ! [B_77] :
      ( v4_orders_2('#skF_7'(B_77))
      | ~ l1_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_281])).

tff(c_287,plain,(
    ! [B_77] :
      ( v4_orders_2('#skF_7'(B_77))
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_284])).

tff(c_4832,plain,
    ( ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5')))
    | v2_struct_0('#skF_4'('#skF_5'))
    | v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_4817])).

tff(c_4834,plain,(
    ~ v4_orders_2('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_4832])).

tff(c_4837,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_287,c_4834])).

tff(c_4840,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4732,c_4790,c_4833,c_4837])).

tff(c_4843,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4840,c_42])).

tff(c_4846,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4843])).

tff(c_4848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4846])).

tff(c_4849,plain,
    ( v2_struct_0('#skF_7'('#skF_4'('#skF_5')))
    | v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4832])).

tff(c_4851,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_4849])).

tff(c_4854,plain,
    ( v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4851,c_42])).

tff(c_4857,plain,
    ( v1_compts_1('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4854])).

tff(c_4859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_100,c_4857])).

tff(c_4861,plain,(
    ~ v2_struct_0('#skF_4'('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_4849])).

tff(c_4860,plain,
    ( v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))))
    | v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_4849])).

tff(c_4866,plain,(
    v2_struct_0('#skF_7'('#skF_4'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_4860])).

tff(c_289,plain,(
    ! [C_124,A_125,B_126] :
      ( ~ v2_struct_0(C_124)
      | ~ m2_yellow_6(C_124,A_125,B_126)
      | ~ l1_waybel_0(B_126,A_125)
      | ~ v7_waybel_0(B_126)
      | ~ v4_orders_2(B_126)
      | v2_struct_0(B_126)
      | ~ l1_struct_0(A_125)
      | v2_struct_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_292,plain,(
    ! [B_77] :
      ( ~ v2_struct_0('#skF_7'(B_77))
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(resolution,[status(thm)],[c_237,c_289])).

tff(c_295,plain,(
    ! [B_77] :
      ( ~ v2_struct_0('#skF_7'(B_77))
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_292])).

tff(c_296,plain,(
    ! [B_77] :
      ( ~ v2_struct_0('#skF_7'(B_77))
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_295])).

tff(c_4869,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_4866,c_296])).

tff(c_4872,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4732,c_4790,c_4833,c_4869])).

tff(c_4874,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4861,c_4872])).

tff(c_4875,plain,(
    v1_xboole_0(k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_4860])).

tff(c_52,plain,(
    ! [A_68] :
      ( k1_xboole_0 = A_68
      | ~ v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_226])).

tff(c_4880,plain,(
    k10_yellow_6('#skF_5','#skF_7'('#skF_4'('#skF_5'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4875,c_52])).

tff(c_82,plain,(
    ! [B_77] :
      ( v1_compts_1('#skF_5')
      | v3_yellow_6('#skF_7'(B_77),'#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_190,plain,(
    ! [B_77] :
      ( v3_yellow_6('#skF_7'(B_77),'#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_82])).

tff(c_433,plain,(
    ! [A_145,B_146] :
      ( k10_yellow_6(A_145,B_146) != k1_xboole_0
      | ~ v3_yellow_6(B_146,A_145)
      | ~ l1_waybel_0(B_146,A_145)
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_439,plain,(
    ! [B_77] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_77)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(B_77),'#skF_5')
      | ~ v7_waybel_0('#skF_7'(B_77))
      | ~ v4_orders_2('#skF_7'(B_77))
      | v2_struct_0('#skF_7'(B_77))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(resolution,[status(thm)],[c_190,c_433])).

tff(c_443,plain,(
    ! [B_77] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_77)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(B_77),'#skF_5')
      | ~ v7_waybel_0('#skF_7'(B_77))
      | ~ v4_orders_2('#skF_7'(B_77))
      | v2_struct_0('#skF_7'(B_77))
      | v2_struct_0('#skF_5')
      | ~ l1_waybel_0(B_77,'#skF_5')
      | ~ v7_waybel_0(B_77)
      | ~ v4_orders_2(B_77)
      | v2_struct_0(B_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_439])).

tff(c_458,plain,(
    ! [B_154] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_154)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_7'(B_154),'#skF_5')
      | ~ v7_waybel_0('#skF_7'(B_154))
      | ~ v4_orders_2('#skF_7'(B_154))
      | v2_struct_0('#skF_7'(B_154))
      | ~ l1_waybel_0(B_154,'#skF_5')
      | ~ v7_waybel_0(B_154)
      | ~ v4_orders_2(B_154)
      | v2_struct_0(B_154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_443])).

tff(c_463,plain,(
    ! [B_155] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_155)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_7'(B_155))
      | ~ v4_orders_2('#skF_7'(B_155))
      | v2_struct_0('#skF_7'(B_155))
      | ~ l1_waybel_0(B_155,'#skF_5')
      | ~ v7_waybel_0(B_155)
      | ~ v4_orders_2(B_155)
      | v2_struct_0(B_155) ) ),
    inference(resolution,[status(thm)],[c_305,c_458])).

tff(c_468,plain,(
    ! [B_156] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_156)) != k1_xboole_0
      | ~ v4_orders_2('#skF_7'(B_156))
      | v2_struct_0('#skF_7'(B_156))
      | ~ l1_waybel_0(B_156,'#skF_5')
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156) ) ),
    inference(resolution,[status(thm)],[c_276,c_463])).

tff(c_473,plain,(
    ! [B_157] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_157)) != k1_xboole_0
      | v2_struct_0('#skF_7'(B_157))
      | ~ l1_waybel_0(B_157,'#skF_5')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(resolution,[status(thm)],[c_287,c_468])).

tff(c_477,plain,(
    ! [B_157] :
      ( k10_yellow_6('#skF_5','#skF_7'(B_157)) != k1_xboole_0
      | ~ l1_waybel_0(B_157,'#skF_5')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(resolution,[status(thm)],[c_473,c_296])).

tff(c_4925,plain,
    ( ~ l1_waybel_0('#skF_4'('#skF_5'),'#skF_5')
    | ~ v7_waybel_0('#skF_4'('#skF_5'))
    | ~ v4_orders_2('#skF_4'('#skF_5'))
    | v2_struct_0('#skF_4'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4880,c_477])).

tff(c_4975,plain,(
    v2_struct_0('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4732,c_4790,c_4833,c_4925])).

tff(c_4977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4861,c_4975])).

tff(c_4978,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_4979,plain,(
    v1_compts_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_66,plain,
    ( v4_orders_2('#skF_6')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_4991,plain,(
    v4_orders_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4979,c_66])).

tff(c_64,plain,
    ( v7_waybel_0('#skF_6')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_4988,plain,(
    v7_waybel_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4979,c_64])).

tff(c_62,plain,
    ( l1_waybel_0('#skF_6','#skF_5')
    | ~ v1_compts_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_4993,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4979,c_62])).

tff(c_44,plain,(
    ! [A_51,B_58] :
      ( r3_waybel_9(A_51,B_58,'#skF_3'(A_51,B_58))
      | ~ l1_waybel_0(B_58,A_51)
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ v1_compts_1(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_46,plain,(
    ! [A_51,B_58] :
      ( m1_subset_1('#skF_3'(A_51,B_58),u1_struct_0(A_51))
      | ~ l1_waybel_0(B_58,A_51)
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ v1_compts_1(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_4998,plain,(
    ! [C_428,B_429,A_430] :
      ( ~ v1_xboole_0(C_428)
      | ~ m1_subset_1(B_429,k1_zfmisc_1(C_428))
      | ~ r2_hidden(A_430,B_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_5003,plain,(
    ! [C_431,A_432] :
      ( ~ v1_xboole_0(C_431)
      | ~ r2_hidden(A_432,'#skF_1'(k1_zfmisc_1(C_431))) ) ),
    inference(resolution,[status(thm)],[c_22,c_4998])).

tff(c_5023,plain,(
    ! [C_441,A_442] :
      ( ~ v1_xboole_0(C_441)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(C_441)))
      | ~ m1_subset_1(A_442,'#skF_1'(k1_zfmisc_1(C_441))) ) ),
    inference(resolution,[status(thm)],[c_26,c_5003])).

tff(c_5028,plain,(
    ! [C_443] :
      ( ~ v1_xboole_0(C_443)
      | v1_xboole_0('#skF_1'(k1_zfmisc_1(C_443))) ) ),
    inference(resolution,[status(thm)],[c_22,c_5023])).

tff(c_5033,plain,(
    ! [C_444] :
      ( '#skF_1'(k1_zfmisc_1(C_444)) = k1_xboole_0
      | ~ v1_xboole_0(C_444) ) ),
    inference(resolution,[status(thm)],[c_5028,c_52])).

tff(c_5055,plain,(
    ! [C_445] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(C_445))
      | ~ v1_xboole_0(C_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5033,c_22])).

tff(c_50,plain,(
    ! [C_67,B_66,A_65] :
      ( ~ v1_xboole_0(C_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_67))
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_5061,plain,(
    ! [A_65,C_445] :
      ( ~ r2_hidden(A_65,k1_xboole_0)
      | ~ v1_xboole_0(C_445) ) ),
    inference(resolution,[status(thm)],[c_5055,c_50])).

tff(c_5062,plain,(
    ! [C_445] : ~ v1_xboole_0(C_445) ),
    inference(splitLeft,[status(thm)],[c_5061])).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_95,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_20])).

tff(c_5066,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5062,c_95])).

tff(c_5067,plain,(
    ! [A_65] : ~ r2_hidden(A_65,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_5061])).

tff(c_5333,plain,(
    ! [A_502,B_503,C_504] :
      ( m2_yellow_6('#skF_2'(A_502,B_503,C_504),A_502,B_503)
      | ~ r3_waybel_9(A_502,B_503,C_504)
      | ~ m1_subset_1(C_504,u1_struct_0(A_502))
      | ~ l1_waybel_0(B_503,A_502)
      | ~ v7_waybel_0(B_503)
      | ~ v4_orders_2(B_503)
      | v2_struct_0(B_503)
      | ~ l1_pre_topc(A_502)
      | ~ v2_pre_topc(A_502)
      | v2_struct_0(A_502) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_12,plain,(
    ! [C_10,A_7,B_8] :
      ( l1_waybel_0(C_10,A_7)
      | ~ m2_yellow_6(C_10,A_7,B_8)
      | ~ l1_waybel_0(B_8,A_7)
      | ~ v7_waybel_0(B_8)
      | ~ v4_orders_2(B_8)
      | v2_struct_0(B_8)
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5680,plain,(
    ! [A_547,B_548,C_549] :
      ( l1_waybel_0('#skF_2'(A_547,B_548,C_549),A_547)
      | ~ l1_struct_0(A_547)
      | ~ r3_waybel_9(A_547,B_548,C_549)
      | ~ m1_subset_1(C_549,u1_struct_0(A_547))
      | ~ l1_waybel_0(B_548,A_547)
      | ~ v7_waybel_0(B_548)
      | ~ v4_orders_2(B_548)
      | v2_struct_0(B_548)
      | ~ l1_pre_topc(A_547)
      | ~ v2_pre_topc(A_547)
      | v2_struct_0(A_547) ) ),
    inference(resolution,[status(thm)],[c_5333,c_12])).

tff(c_6514,plain,(
    ! [A_598,B_599,B_600] :
      ( l1_waybel_0('#skF_2'(A_598,B_599,'#skF_3'(A_598,B_600)),A_598)
      | ~ l1_struct_0(A_598)
      | ~ r3_waybel_9(A_598,B_599,'#skF_3'(A_598,B_600))
      | ~ l1_waybel_0(B_599,A_598)
      | ~ v7_waybel_0(B_599)
      | ~ v4_orders_2(B_599)
      | v2_struct_0(B_599)
      | ~ l1_waybel_0(B_600,A_598)
      | ~ v7_waybel_0(B_600)
      | ~ v4_orders_2(B_600)
      | v2_struct_0(B_600)
      | ~ v1_compts_1(A_598)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(resolution,[status(thm)],[c_46,c_5680])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v3_yellow_6(B_3,A_1)
      | k10_yellow_6(A_1,B_3) = k1_xboole_0
      | ~ l1_waybel_0(B_3,A_1)
      | ~ v7_waybel_0(B_3)
      | ~ v4_orders_2(B_3)
      | v2_struct_0(B_3)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    ! [C_76] :
      ( ~ v3_yellow_6(C_76,'#skF_5')
      | ~ m2_yellow_6(C_76,'#skF_5','#skF_6')
      | ~ v1_compts_1('#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_251])).

tff(c_4995,plain,(
    ! [C_76] :
      ( ~ v3_yellow_6(C_76,'#skF_5')
      | ~ m2_yellow_6(C_76,'#skF_5','#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4979,c_60])).

tff(c_5349,plain,(
    ! [C_504] :
      ( ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_504),'#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6',C_504)
      | ~ m1_subset_1(C_504,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5333,c_4995])).

tff(c_5356,plain,(
    ! [C_504] :
      ( ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_504),'#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6',C_504)
      | ~ m1_subset_1(C_504,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4991,c_4988,c_4993,c_5349])).

tff(c_5358,plain,(
    ! [C_505] :
      ( ~ v3_yellow_6('#skF_2'('#skF_5','#skF_6',C_505),'#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6',C_505)
      | ~ m1_subset_1(C_505,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4978,c_5356])).

tff(c_5361,plain,(
    ! [C_505] :
      ( ~ r3_waybel_9('#skF_5','#skF_6',C_505)
      | ~ m1_subset_1(C_505,u1_struct_0('#skF_5'))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6',C_505)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6',C_505),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6',C_505))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6',C_505))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6',C_505))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_2,c_5358])).

tff(c_5364,plain,(
    ! [C_505] :
      ( ~ r3_waybel_9('#skF_5','#skF_6',C_505)
      | ~ m1_subset_1(C_505,u1_struct_0('#skF_5'))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6',C_505)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6',C_505),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6',C_505))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6',C_505))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6',C_505))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_5361])).

tff(c_5451,plain,(
    ! [C_525] :
      ( ~ r3_waybel_9('#skF_5','#skF_6',C_525)
      | ~ m1_subset_1(C_525,u1_struct_0('#skF_5'))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6',C_525)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6',C_525),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6',C_525))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6',C_525))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6',C_525)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5364])).

tff(c_5459,plain,(
    ! [B_58] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_5451])).

tff(c_5482,plain,(
    ! [B_58] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4979,c_5459])).

tff(c_5483,plain,(
    ! [B_58] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)),'#skF_5')
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_5482])).

tff(c_6518,plain,(
    ! [B_600] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_600))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_600,'#skF_5')
      | ~ v7_waybel_0(B_600)
      | ~ v4_orders_2(B_600)
      | v2_struct_0(B_600)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_6514,c_5483])).

tff(c_6521,plain,(
    ! [B_600] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_600))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_600,'#skF_5')
      | ~ v7_waybel_0(B_600)
      | ~ v4_orders_2(B_600)
      | v2_struct_0(B_600)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4979,c_4991,c_4988,c_4993,c_6518])).

tff(c_6522,plain,(
    ! [B_600] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_600)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_600))
      | ~ l1_waybel_0(B_600,'#skF_5')
      | ~ v7_waybel_0(B_600)
      | ~ v4_orders_2(B_600)
      | v2_struct_0(B_600) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4978,c_6521])).

tff(c_6526,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6522])).

tff(c_6529,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_6526])).

tff(c_6533,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6529])).

tff(c_6535,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_6522])).

tff(c_16,plain,(
    ! [C_10,A_7,B_8] :
      ( v4_orders_2(C_10)
      | ~ m2_yellow_6(C_10,A_7,B_8)
      | ~ l1_waybel_0(B_8,A_7)
      | ~ v7_waybel_0(B_8)
      | ~ v4_orders_2(B_8)
      | v2_struct_0(B_8)
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5602,plain,(
    ! [A_529,B_530,C_531] :
      ( v4_orders_2('#skF_2'(A_529,B_530,C_531))
      | ~ l1_struct_0(A_529)
      | ~ r3_waybel_9(A_529,B_530,C_531)
      | ~ m1_subset_1(C_531,u1_struct_0(A_529))
      | ~ l1_waybel_0(B_530,A_529)
      | ~ v7_waybel_0(B_530)
      | ~ v4_orders_2(B_530)
      | v2_struct_0(B_530)
      | ~ l1_pre_topc(A_529)
      | ~ v2_pre_topc(A_529)
      | v2_struct_0(A_529) ) ),
    inference(resolution,[status(thm)],[c_5333,c_16])).

tff(c_5632,plain,(
    ! [A_51,B_530,B_58] :
      ( v4_orders_2('#skF_2'(A_51,B_530,'#skF_3'(A_51,B_58)))
      | ~ l1_struct_0(A_51)
      | ~ r3_waybel_9(A_51,B_530,'#skF_3'(A_51,B_58))
      | ~ l1_waybel_0(B_530,A_51)
      | ~ v7_waybel_0(B_530)
      | ~ v4_orders_2(B_530)
      | v2_struct_0(B_530)
      | ~ l1_waybel_0(B_58,A_51)
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ v1_compts_1(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_46,c_5602])).

tff(c_14,plain,(
    ! [C_10,A_7,B_8] :
      ( v7_waybel_0(C_10)
      | ~ m2_yellow_6(C_10,A_7,B_8)
      | ~ l1_waybel_0(B_8,A_7)
      | ~ v7_waybel_0(B_8)
      | ~ v4_orders_2(B_8)
      | v2_struct_0(B_8)
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5641,plain,(
    ! [A_536,B_537,C_538] :
      ( v7_waybel_0('#skF_2'(A_536,B_537,C_538))
      | ~ l1_struct_0(A_536)
      | ~ r3_waybel_9(A_536,B_537,C_538)
      | ~ m1_subset_1(C_538,u1_struct_0(A_536))
      | ~ l1_waybel_0(B_537,A_536)
      | ~ v7_waybel_0(B_537)
      | ~ v4_orders_2(B_537)
      | v2_struct_0(B_537)
      | ~ l1_pre_topc(A_536)
      | ~ v2_pre_topc(A_536)
      | v2_struct_0(A_536) ) ),
    inference(resolution,[status(thm)],[c_5333,c_14])).

tff(c_5671,plain,(
    ! [A_51,B_537,B_58] :
      ( v7_waybel_0('#skF_2'(A_51,B_537,'#skF_3'(A_51,B_58)))
      | ~ l1_struct_0(A_51)
      | ~ r3_waybel_9(A_51,B_537,'#skF_3'(A_51,B_58))
      | ~ l1_waybel_0(B_537,A_51)
      | ~ v7_waybel_0(B_537)
      | ~ v4_orders_2(B_537)
      | v2_struct_0(B_537)
      | ~ l1_waybel_0(B_58,A_51)
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ v1_compts_1(A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51)
      | v2_struct_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_46,c_5641])).

tff(c_6741,plain,(
    ! [B_614] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_614))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_614)))
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_614)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_614)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_614))
      | ~ l1_waybel_0(B_614,'#skF_5')
      | ~ v7_waybel_0(B_614)
      | ~ v4_orders_2(B_614)
      | v2_struct_0(B_614) ) ),
    inference(splitRight,[status(thm)],[c_6522])).

tff(c_6745,plain,(
    ! [B_58] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5671,c_6741])).

tff(c_6748,plain,(
    ! [B_58] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4979,c_4991,c_4988,c_4993,c_6535,c_6745])).

tff(c_6954,plain,(
    ! [B_627] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_627))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_627)))
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_627)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_627))
      | ~ l1_waybel_0(B_627,'#skF_5')
      | ~ v7_waybel_0(B_627)
      | ~ v4_orders_2(B_627)
      | v2_struct_0(B_627) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4978,c_6748])).

tff(c_6958,plain,(
    ! [B_58] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ l1_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_5632,c_6954])).

tff(c_6961,plain,(
    ! [B_58] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4979,c_4991,c_4988,c_4993,c_6535,c_6958])).

tff(c_7093,plain,(
    ! [B_636] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_636))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_636)))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_636))
      | ~ l1_waybel_0(B_636,'#skF_5')
      | ~ v7_waybel_0(B_636)
      | ~ v4_orders_2(B_636)
      | v2_struct_0(B_636) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4978,c_6961])).

tff(c_18,plain,(
    ! [C_10,A_7,B_8] :
      ( ~ v2_struct_0(C_10)
      | ~ m2_yellow_6(C_10,A_7,B_8)
      | ~ l1_waybel_0(B_8,A_7)
      | ~ v7_waybel_0(B_8)
      | ~ v4_orders_2(B_8)
      | v2_struct_0(B_8)
      | ~ l1_struct_0(A_7)
      | v2_struct_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_5352,plain,(
    ! [A_502,B_503,C_504] :
      ( ~ v2_struct_0('#skF_2'(A_502,B_503,C_504))
      | ~ l1_struct_0(A_502)
      | ~ r3_waybel_9(A_502,B_503,C_504)
      | ~ m1_subset_1(C_504,u1_struct_0(A_502))
      | ~ l1_waybel_0(B_503,A_502)
      | ~ v7_waybel_0(B_503)
      | ~ v4_orders_2(B_503)
      | v2_struct_0(B_503)
      | ~ l1_pre_topc(A_502)
      | ~ v2_pre_topc(A_502)
      | v2_struct_0(A_502) ) ),
    inference(resolution,[status(thm)],[c_5333,c_18])).

tff(c_7095,plain,(
    ! [B_636] :
      ( ~ l1_struct_0('#skF_5')
      | ~ m1_subset_1('#skF_3'('#skF_5',B_636),u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_636))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_636))
      | ~ l1_waybel_0(B_636,'#skF_5')
      | ~ v7_waybel_0(B_636)
      | ~ v4_orders_2(B_636)
      | v2_struct_0(B_636) ) ),
    inference(resolution,[status(thm)],[c_7093,c_5352])).

tff(c_7098,plain,(
    ! [B_636] :
      ( ~ m1_subset_1('#skF_3'('#skF_5',B_636),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_636))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_636))
      | ~ l1_waybel_0(B_636,'#skF_5')
      | ~ v7_waybel_0(B_636)
      | ~ v4_orders_2(B_636)
      | v2_struct_0(B_636) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4991,c_4988,c_4993,c_6535,c_7095])).

tff(c_7100,plain,(
    ! [B_637] :
      ( ~ m1_subset_1('#skF_3'('#skF_5',B_637),u1_struct_0('#skF_5'))
      | k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_637))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_637))
      | ~ l1_waybel_0(B_637,'#skF_5')
      | ~ v7_waybel_0(B_637)
      | ~ v4_orders_2(B_637)
      | v2_struct_0(B_637) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4978,c_7098])).

tff(c_7104,plain,(
    ! [B_58] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_7100])).

tff(c_7107,plain,(
    ! [B_58] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4979,c_7104])).

tff(c_7109,plain,(
    ! [B_638] :
      ( k10_yellow_6('#skF_5','#skF_2'('#skF_5','#skF_6','#skF_3'('#skF_5',B_638))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_638))
      | ~ l1_waybel_0(B_638,'#skF_5')
      | ~ v7_waybel_0(B_638)
      | ~ v4_orders_2(B_638)
      | v2_struct_0(B_638) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7107])).

tff(c_30,plain,(
    ! [C_49,A_37,B_45] :
      ( r2_hidden(C_49,k10_yellow_6(A_37,'#skF_2'(A_37,B_45,C_49)))
      | ~ r3_waybel_9(A_37,B_45,C_49)
      | ~ m1_subset_1(C_49,u1_struct_0(A_37))
      | ~ l1_waybel_0(B_45,A_37)
      | ~ v7_waybel_0(B_45)
      | ~ v4_orders_2(B_45)
      | v2_struct_0(B_45)
      | ~ l1_pre_topc(A_37)
      | ~ v2_pre_topc(A_37)
      | v2_struct_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_185])).

tff(c_7136,plain,(
    ! [B_638] :
      ( r2_hidden('#skF_3'('#skF_5',B_638),k1_xboole_0)
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_638))
      | ~ m1_subset_1('#skF_3'('#skF_5',B_638),u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_638))
      | ~ l1_waybel_0(B_638,'#skF_5')
      | ~ v7_waybel_0(B_638)
      | ~ v4_orders_2(B_638)
      | v2_struct_0(B_638) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7109,c_30])).

tff(c_7176,plain,(
    ! [B_638] :
      ( r2_hidden('#skF_3'('#skF_5',B_638),k1_xboole_0)
      | ~ m1_subset_1('#skF_3'('#skF_5',B_638),u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_638))
      | ~ l1_waybel_0(B_638,'#skF_5')
      | ~ v7_waybel_0(B_638)
      | ~ v4_orders_2(B_638)
      | v2_struct_0(B_638) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4991,c_4988,c_4993,c_7136])).

tff(c_7194,plain,(
    ! [B_639] :
      ( ~ m1_subset_1('#skF_3'('#skF_5',B_639),u1_struct_0('#skF_5'))
      | ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_639))
      | ~ l1_waybel_0(B_639,'#skF_5')
      | ~ v7_waybel_0(B_639)
      | ~ v4_orders_2(B_639)
      | v2_struct_0(B_639) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4978,c_5067,c_7176])).

tff(c_7198,plain,(
    ! [B_58] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ v1_compts_1('#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_46,c_7194])).

tff(c_7201,plain,(
    ! [B_58] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_58))
      | ~ l1_waybel_0(B_58,'#skF_5')
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4979,c_7198])).

tff(c_7203,plain,(
    ! [B_640] :
      ( ~ r3_waybel_9('#skF_5','#skF_6','#skF_3'('#skF_5',B_640))
      | ~ l1_waybel_0(B_640,'#skF_5')
      | ~ v7_waybel_0(B_640)
      | ~ v4_orders_2(B_640)
      | v2_struct_0(B_640) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_7201])).

tff(c_7211,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ v1_compts_1('#skF_5')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_7203])).

tff(c_7218,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_4979,c_4991,c_4988,c_4993,c_7211])).

tff(c_7220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_4978,c_7218])).

%------------------------------------------------------------------------------
