%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:42 EST 2020

% Result     : Theorem 6.94s
% Output     : CNFRefutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :  254 (3559 expanded)
%              Number of leaves         :   45 (1178 expanded)
%              Depth                    :   37
%              Number of atoms          : 1312 (24668 expanded)
%              Number of equality atoms :   61 ( 992 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_9 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_273,negated_conjecture,(
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

tff(f_248,axiom,(
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

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_78,axiom,(
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
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k10_yellow_6(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ! [E] :
                          ( m1_connsp_2(E,A,D)
                         => r1_waybel_0(A,B,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_96,axiom,(
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
             => ( r2_hidden(C,k10_yellow_6(A,B))
               => r3_waybel_9(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_195,axiom,(
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

tff(f_46,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_122,axiom,(
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

tff(f_144,axiom,(
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

tff(f_224,axiom,(
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

tff(c_74,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_84,plain,
    ( ~ v2_struct_0('#skF_8')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_111,plain,(
    ~ v1_compts_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_72,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_70,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_62,plain,(
    ! [A_139] :
      ( v4_orders_2('#skF_6'(A_139))
      | v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_110,plain,(
    ! [B_158] :
      ( v1_compts_1('#skF_7')
      | m2_yellow_6('#skF_9'(B_158),'#skF_7',B_158)
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_145,plain,(
    ! [B_158] :
      ( m2_yellow_6('#skF_9'(B_158),'#skF_7',B_158)
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_110])).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_54,C_76] :
      ( m1_subset_1('#skF_2'(A_10,B_54,C_76),u1_struct_0(A_10))
      | k10_yellow_6(A_10,B_54) = C_76
      | ~ m1_subset_1(C_76,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_waybel_0(B_54,A_10)
      | ~ v7_waybel_0(B_54)
      | ~ v4_orders_2(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_116,plain,(
    ! [A_166,B_167] :
      ( r1_tarski(A_166,B_167)
      | ~ m1_subset_1(A_166,k1_zfmisc_1(B_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_116])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_94,B_95] :
      ( m1_subset_1(k10_yellow_6(A_94,B_95),k1_zfmisc_1(u1_struct_0(A_94)))
      | ~ l1_waybel_0(B_95,A_94)
      | ~ v7_waybel_0(B_95)
      | ~ v4_orders_2(B_95)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_324,plain,(
    ! [A_266,B_267,D_268] :
      ( m1_connsp_2('#skF_1'(A_266,B_267,k10_yellow_6(A_266,B_267),D_268),A_266,D_268)
      | r2_hidden(D_268,k10_yellow_6(A_266,B_267))
      | ~ m1_subset_1(D_268,u1_struct_0(A_266))
      | ~ m1_subset_1(k10_yellow_6(A_266,B_267),k1_zfmisc_1(u1_struct_0(A_266)))
      | ~ l1_waybel_0(B_267,A_266)
      | ~ v7_waybel_0(B_267)
      | ~ v4_orders_2(B_267)
      | v2_struct_0(B_267)
      | ~ l1_pre_topc(A_266)
      | ~ v2_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_330,plain,(
    ! [A_94,B_95,D_268] :
      ( m1_connsp_2('#skF_1'(A_94,B_95,k10_yellow_6(A_94,B_95),D_268),A_94,D_268)
      | r2_hidden(D_268,k10_yellow_6(A_94,B_95))
      | ~ m1_subset_1(D_268,u1_struct_0(A_94))
      | ~ l1_waybel_0(B_95,A_94)
      | ~ v7_waybel_0(B_95)
      | ~ v4_orders_2(B_95)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_94)
      | ~ v2_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_34,c_324])).

tff(c_336,plain,(
    ! [A_272,B_273,C_274,E_275] :
      ( r2_hidden('#skF_2'(A_272,B_273,C_274),C_274)
      | r1_waybel_0(A_272,B_273,E_275)
      | ~ m1_connsp_2(E_275,A_272,'#skF_2'(A_272,B_273,C_274))
      | k10_yellow_6(A_272,B_273) = C_274
      | ~ m1_subset_1(C_274,k1_zfmisc_1(u1_struct_0(A_272)))
      | ~ l1_waybel_0(B_273,A_272)
      | ~ v7_waybel_0(B_273)
      | ~ v4_orders_2(B_273)
      | v2_struct_0(B_273)
      | ~ l1_pre_topc(A_272)
      | ~ v2_pre_topc(A_272)
      | v2_struct_0(A_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_458,plain,(
    ! [A_376,B_377,C_378,B_379] :
      ( r2_hidden('#skF_2'(A_376,B_377,C_378),C_378)
      | r1_waybel_0(A_376,B_377,'#skF_1'(A_376,B_379,k10_yellow_6(A_376,B_379),'#skF_2'(A_376,B_377,C_378)))
      | k10_yellow_6(A_376,B_377) = C_378
      | ~ m1_subset_1(C_378,k1_zfmisc_1(u1_struct_0(A_376)))
      | ~ l1_waybel_0(B_377,A_376)
      | ~ v7_waybel_0(B_377)
      | ~ v4_orders_2(B_377)
      | v2_struct_0(B_377)
      | r2_hidden('#skF_2'(A_376,B_377,C_378),k10_yellow_6(A_376,B_379))
      | ~ m1_subset_1('#skF_2'(A_376,B_377,C_378),u1_struct_0(A_376))
      | ~ l1_waybel_0(B_379,A_376)
      | ~ v7_waybel_0(B_379)
      | ~ v4_orders_2(B_379)
      | v2_struct_0(B_379)
      | ~ l1_pre_topc(A_376)
      | ~ v2_pre_topc(A_376)
      | v2_struct_0(A_376) ) ),
    inference(resolution,[status(thm)],[c_330,c_336])).

tff(c_30,plain,(
    ! [A_10,B_54,D_87] :
      ( ~ r1_waybel_0(A_10,B_54,'#skF_1'(A_10,B_54,k10_yellow_6(A_10,B_54),D_87))
      | r2_hidden(D_87,k10_yellow_6(A_10,B_54))
      | ~ m1_subset_1(D_87,u1_struct_0(A_10))
      | ~ m1_subset_1(k10_yellow_6(A_10,B_54),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_waybel_0(B_54,A_10)
      | ~ v7_waybel_0(B_54)
      | ~ v4_orders_2(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_485,plain,(
    ! [A_380,B_381,C_382] :
      ( ~ m1_subset_1(k10_yellow_6(A_380,B_381),k1_zfmisc_1(u1_struct_0(A_380)))
      | r2_hidden('#skF_2'(A_380,B_381,C_382),C_382)
      | k10_yellow_6(A_380,B_381) = C_382
      | ~ m1_subset_1(C_382,k1_zfmisc_1(u1_struct_0(A_380)))
      | r2_hidden('#skF_2'(A_380,B_381,C_382),k10_yellow_6(A_380,B_381))
      | ~ m1_subset_1('#skF_2'(A_380,B_381,C_382),u1_struct_0(A_380))
      | ~ l1_waybel_0(B_381,A_380)
      | ~ v7_waybel_0(B_381)
      | ~ v4_orders_2(B_381)
      | v2_struct_0(B_381)
      | ~ l1_pre_topc(A_380)
      | ~ v2_pre_topc(A_380)
      | v2_struct_0(A_380) ) ),
    inference(resolution,[status(thm)],[c_458,c_30])).

tff(c_509,plain,(
    ! [A_383,B_384,C_385] :
      ( r2_hidden('#skF_2'(A_383,B_384,C_385),C_385)
      | k10_yellow_6(A_383,B_384) = C_385
      | ~ m1_subset_1(C_385,k1_zfmisc_1(u1_struct_0(A_383)))
      | r2_hidden('#skF_2'(A_383,B_384,C_385),k10_yellow_6(A_383,B_384))
      | ~ m1_subset_1('#skF_2'(A_383,B_384,C_385),u1_struct_0(A_383))
      | ~ l1_waybel_0(B_384,A_383)
      | ~ v7_waybel_0(B_384)
      | ~ v4_orders_2(B_384)
      | v2_struct_0(B_384)
      | ~ l1_pre_topc(A_383)
      | ~ v2_pre_topc(A_383)
      | v2_struct_0(A_383) ) ),
    inference(resolution,[status(thm)],[c_34,c_485])).

tff(c_48,plain,(
    ! [A_103,B_107,C_109] :
      ( r3_waybel_9(A_103,B_107,C_109)
      | ~ r2_hidden(C_109,k10_yellow_6(A_103,B_107))
      | ~ m1_subset_1(C_109,u1_struct_0(A_103))
      | ~ l1_waybel_0(B_107,A_103)
      | ~ v7_waybel_0(B_107)
      | ~ v4_orders_2(B_107)
      | v2_struct_0(B_107)
      | ~ l1_pre_topc(A_103)
      | ~ v2_pre_topc(A_103)
      | v2_struct_0(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_550,plain,(
    ! [A_386,B_387,C_388] :
      ( r3_waybel_9(A_386,B_387,'#skF_2'(A_386,B_387,C_388))
      | r2_hidden('#skF_2'(A_386,B_387,C_388),C_388)
      | k10_yellow_6(A_386,B_387) = C_388
      | ~ m1_subset_1(C_388,k1_zfmisc_1(u1_struct_0(A_386)))
      | ~ m1_subset_1('#skF_2'(A_386,B_387,C_388),u1_struct_0(A_386))
      | ~ l1_waybel_0(B_387,A_386)
      | ~ v7_waybel_0(B_387)
      | ~ v4_orders_2(B_387)
      | v2_struct_0(B_387)
      | ~ l1_pre_topc(A_386)
      | ~ v2_pre_topc(A_386)
      | v2_struct_0(A_386) ) ),
    inference(resolution,[status(thm)],[c_509,c_48])).

tff(c_554,plain,(
    ! [A_389,B_390,C_391] :
      ( r3_waybel_9(A_389,B_390,'#skF_2'(A_389,B_390,C_391))
      | r2_hidden('#skF_2'(A_389,B_390,C_391),C_391)
      | k10_yellow_6(A_389,B_390) = C_391
      | ~ m1_subset_1(C_391,k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ l1_waybel_0(B_390,A_389)
      | ~ v7_waybel_0(B_390)
      | ~ v4_orders_2(B_390)
      | v2_struct_0(B_390)
      | ~ l1_pre_topc(A_389)
      | ~ v2_pre_topc(A_389)
      | v2_struct_0(A_389) ) ),
    inference(resolution,[status(thm)],[c_14,c_550])).

tff(c_575,plain,(
    ! [A_394,B_395,A_396] :
      ( r3_waybel_9(A_394,B_395,'#skF_2'(A_394,B_395,A_396))
      | r2_hidden('#skF_2'(A_394,B_395,A_396),A_396)
      | k10_yellow_6(A_394,B_395) = A_396
      | ~ l1_waybel_0(B_395,A_394)
      | ~ v7_waybel_0(B_395)
      | ~ v4_orders_2(B_395)
      | v2_struct_0(B_395)
      | ~ l1_pre_topc(A_394)
      | ~ v2_pre_topc(A_394)
      | v2_struct_0(A_394)
      | ~ r1_tarski(A_396,u1_struct_0(A_394)) ) ),
    inference(resolution,[status(thm)],[c_6,c_554])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( ~ r1_tarski(B_8,A_7)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_620,plain,(
    ! [A_401,A_402,B_403] :
      ( ~ r1_tarski(A_401,'#skF_2'(A_402,B_403,A_401))
      | r3_waybel_9(A_402,B_403,'#skF_2'(A_402,B_403,A_401))
      | k10_yellow_6(A_402,B_403) = A_401
      | ~ l1_waybel_0(B_403,A_402)
      | ~ v7_waybel_0(B_403)
      | ~ v4_orders_2(B_403)
      | v2_struct_0(B_403)
      | ~ l1_pre_topc(A_402)
      | ~ v2_pre_topc(A_402)
      | v2_struct_0(A_402)
      | ~ r1_tarski(A_401,u1_struct_0(A_402)) ) ),
    inference(resolution,[status(thm)],[c_575,c_10])).

tff(c_623,plain,(
    ! [A_402,B_403] :
      ( r3_waybel_9(A_402,B_403,'#skF_2'(A_402,B_403,k1_xboole_0))
      | k10_yellow_6(A_402,B_403) = k1_xboole_0
      | ~ l1_waybel_0(B_403,A_402)
      | ~ v7_waybel_0(B_403)
      | ~ v4_orders_2(B_403)
      | v2_struct_0(B_403)
      | ~ l1_pre_topc(A_402)
      | ~ v2_pre_topc(A_402)
      | v2_struct_0(A_402)
      | ~ r1_tarski(k1_xboole_0,u1_struct_0(A_402)) ) ),
    inference(resolution,[status(thm)],[c_124,c_620])).

tff(c_627,plain,(
    ! [A_404,B_405] :
      ( r3_waybel_9(A_404,B_405,'#skF_2'(A_404,B_405,k1_xboole_0))
      | k10_yellow_6(A_404,B_405) = k1_xboole_0
      | ~ l1_waybel_0(B_405,A_404)
      | ~ v7_waybel_0(B_405)
      | ~ v4_orders_2(B_405)
      | v2_struct_0(B_405)
      | ~ l1_pre_topc(A_404)
      | ~ v2_pre_topc(A_404)
      | v2_struct_0(A_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_623])).

tff(c_50,plain,(
    ! [A_110,B_118,D_124,C_122] :
      ( r3_waybel_9(A_110,B_118,D_124)
      | ~ r3_waybel_9(A_110,C_122,D_124)
      | ~ m1_subset_1(D_124,u1_struct_0(A_110))
      | ~ m2_yellow_6(C_122,A_110,B_118)
      | ~ l1_waybel_0(B_118,A_110)
      | ~ v7_waybel_0(B_118)
      | ~ v4_orders_2(B_118)
      | v2_struct_0(B_118)
      | ~ l1_pre_topc(A_110)
      | ~ v2_pre_topc(A_110)
      | v2_struct_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_1103,plain,(
    ! [A_473,B_474,B_475] :
      ( r3_waybel_9(A_473,B_474,'#skF_2'(A_473,B_475,k1_xboole_0))
      | ~ m1_subset_1('#skF_2'(A_473,B_475,k1_xboole_0),u1_struct_0(A_473))
      | ~ m2_yellow_6(B_475,A_473,B_474)
      | ~ l1_waybel_0(B_474,A_473)
      | ~ v7_waybel_0(B_474)
      | ~ v4_orders_2(B_474)
      | v2_struct_0(B_474)
      | k10_yellow_6(A_473,B_475) = k1_xboole_0
      | ~ l1_waybel_0(B_475,A_473)
      | ~ v7_waybel_0(B_475)
      | ~ v4_orders_2(B_475)
      | v2_struct_0(B_475)
      | ~ l1_pre_topc(A_473)
      | ~ v2_pre_topc(A_473)
      | v2_struct_0(A_473) ) ),
    inference(resolution,[status(thm)],[c_627,c_50])).

tff(c_1112,plain,(
    ! [A_10,B_474,B_54] :
      ( r3_waybel_9(A_10,B_474,'#skF_2'(A_10,B_54,k1_xboole_0))
      | ~ m2_yellow_6(B_54,A_10,B_474)
      | ~ l1_waybel_0(B_474,A_10)
      | ~ v7_waybel_0(B_474)
      | ~ v4_orders_2(B_474)
      | v2_struct_0(B_474)
      | k10_yellow_6(A_10,B_54) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_waybel_0(B_54,A_10)
      | ~ v7_waybel_0(B_54)
      | ~ v4_orders_2(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_1103])).

tff(c_1122,plain,(
    ! [A_476,B_477,B_478] :
      ( r3_waybel_9(A_476,B_477,'#skF_2'(A_476,B_478,k1_xboole_0))
      | ~ m2_yellow_6(B_478,A_476,B_477)
      | ~ l1_waybel_0(B_477,A_476)
      | ~ v7_waybel_0(B_477)
      | ~ v4_orders_2(B_477)
      | v2_struct_0(B_477)
      | k10_yellow_6(A_476,B_478) = k1_xboole_0
      | ~ l1_waybel_0(B_478,A_476)
      | ~ v7_waybel_0(B_478)
      | ~ v4_orders_2(B_478)
      | v2_struct_0(B_478)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1112])).

tff(c_56,plain,(
    ! [A_139,C_149] :
      ( ~ r3_waybel_9(A_139,'#skF_6'(A_139),C_149)
      | ~ m1_subset_1(C_149,u1_struct_0(A_139))
      | v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_1149,plain,(
    ! [A_482,B_483] :
      ( ~ m1_subset_1('#skF_2'(A_482,B_483,k1_xboole_0),u1_struct_0(A_482))
      | v1_compts_1(A_482)
      | ~ m2_yellow_6(B_483,A_482,'#skF_6'(A_482))
      | ~ l1_waybel_0('#skF_6'(A_482),A_482)
      | ~ v7_waybel_0('#skF_6'(A_482))
      | ~ v4_orders_2('#skF_6'(A_482))
      | v2_struct_0('#skF_6'(A_482))
      | k10_yellow_6(A_482,B_483) = k1_xboole_0
      | ~ l1_waybel_0(B_483,A_482)
      | ~ v7_waybel_0(B_483)
      | ~ v4_orders_2(B_483)
      | v2_struct_0(B_483)
      | ~ l1_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(resolution,[status(thm)],[c_1122,c_56])).

tff(c_1161,plain,(
    ! [A_10,B_54] :
      ( v1_compts_1(A_10)
      | ~ m2_yellow_6(B_54,A_10,'#skF_6'(A_10))
      | ~ l1_waybel_0('#skF_6'(A_10),A_10)
      | ~ v7_waybel_0('#skF_6'(A_10))
      | ~ v4_orders_2('#skF_6'(A_10))
      | v2_struct_0('#skF_6'(A_10))
      | k10_yellow_6(A_10,B_54) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_waybel_0(B_54,A_10)
      | ~ v7_waybel_0(B_54)
      | ~ v4_orders_2(B_54)
      | v2_struct_0(B_54)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_1149])).

tff(c_1171,plain,(
    ! [A_484,B_485] :
      ( v1_compts_1(A_484)
      | ~ m2_yellow_6(B_485,A_484,'#skF_6'(A_484))
      | ~ l1_waybel_0('#skF_6'(A_484),A_484)
      | ~ v7_waybel_0('#skF_6'(A_484))
      | ~ v4_orders_2('#skF_6'(A_484))
      | v2_struct_0('#skF_6'(A_484))
      | k10_yellow_6(A_484,B_485) = k1_xboole_0
      | ~ l1_waybel_0(B_485,A_484)
      | ~ v7_waybel_0(B_485)
      | ~ v4_orders_2(B_485)
      | v2_struct_0(B_485)
      | ~ l1_pre_topc(A_484)
      | ~ v2_pre_topc(A_484)
      | v2_struct_0(A_484) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1161])).

tff(c_1179,plain,
    ( v1_compts_1('#skF_7')
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_145,c_1171])).

tff(c_1183,plain,
    ( v1_compts_1('#skF_7')
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_7')
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1179])).

tff(c_1184,plain,
    ( k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1183])).

tff(c_1235,plain,(
    ~ v4_orders_2('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1184])).

tff(c_1238,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_1235])).

tff(c_1241,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1238])).

tff(c_1243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1241])).

tff(c_1245,plain,(
    v4_orders_2('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1184])).

tff(c_60,plain,(
    ! [A_139] :
      ( v7_waybel_0('#skF_6'(A_139))
      | v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_58,plain,(
    ! [A_139] :
      ( l1_waybel_0('#skF_6'(A_139),A_139)
      | v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_12,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_149,plain,(
    ! [C_185,A_186,B_187] :
      ( v7_waybel_0(C_185)
      | ~ m2_yellow_6(C_185,A_186,B_187)
      | ~ l1_waybel_0(B_187,A_186)
      | ~ v7_waybel_0(B_187)
      | ~ v4_orders_2(B_187)
      | v2_struct_0(B_187)
      | ~ l1_struct_0(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_152,plain,(
    ! [B_158] :
      ( v7_waybel_0('#skF_9'(B_158))
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(resolution,[status(thm)],[c_145,c_149])).

tff(c_155,plain,(
    ! [B_158] :
      ( v7_waybel_0('#skF_9'(B_158))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_152])).

tff(c_156,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_159,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_156])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_159])).

tff(c_165,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_184,plain,(
    ! [C_196,A_197,B_198] :
      ( l1_waybel_0(C_196,A_197)
      | ~ m2_yellow_6(C_196,A_197,B_198)
      | ~ l1_waybel_0(B_198,A_197)
      | ~ v7_waybel_0(B_198)
      | ~ v4_orders_2(B_198)
      | v2_struct_0(B_198)
      | ~ l1_struct_0(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_187,plain,(
    ! [B_158] :
      ( l1_waybel_0('#skF_9'(B_158),'#skF_7')
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(resolution,[status(thm)],[c_145,c_184])).

tff(c_190,plain,(
    ! [B_158] :
      ( l1_waybel_0('#skF_9'(B_158),'#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_187])).

tff(c_191,plain,(
    ! [B_158] :
      ( l1_waybel_0('#skF_9'(B_158),'#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_190])).

tff(c_1244,plain,
    ( ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | v2_struct_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1184])).

tff(c_1246,plain,(
    ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1244])).

tff(c_1249,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_191,c_1246])).

tff(c_1252,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_1249])).

tff(c_1253,plain,(
    ~ v7_waybel_0('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1252])).

tff(c_1256,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1253])).

tff(c_1259,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1256])).

tff(c_1261,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1259])).

tff(c_1262,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1252])).

tff(c_1264,plain,(
    ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1262])).

tff(c_1298,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1264])).

tff(c_1301,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1298])).

tff(c_1303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1301])).

tff(c_1304,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1262])).

tff(c_64,plain,(
    ! [A_139] :
      ( ~ v2_struct_0('#skF_6'(A_139))
      | v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_1308,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1304,c_64])).

tff(c_1311,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1308])).

tff(c_1313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1311])).

tff(c_1314,plain,
    ( ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1244])).

tff(c_1316,plain,(
    ~ v7_waybel_0('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1314])).

tff(c_1319,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1316])).

tff(c_1322,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1319])).

tff(c_1324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1322])).

tff(c_1326,plain,(
    v7_waybel_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_164,plain,(
    ! [B_158] :
      ( v7_waybel_0('#skF_9'(B_158))
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_1325,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_1327,plain,(
    ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_1325])).

tff(c_1330,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_164,c_1327])).

tff(c_1333,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_1326,c_1330])).

tff(c_1334,plain,(
    ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1333])).

tff(c_1368,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1334])).

tff(c_1371,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1368])).

tff(c_1373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1371])).

tff(c_1374,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1333])).

tff(c_1378,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1374,c_64])).

tff(c_1381,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1378])).

tff(c_1383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1381])).

tff(c_1384,plain,
    ( ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1325])).

tff(c_1386,plain,(
    ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1384])).

tff(c_1389,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_1386])).

tff(c_1392,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1389])).

tff(c_1394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1392])).

tff(c_1396,plain,(
    l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1384])).

tff(c_176,plain,(
    ! [C_193,A_194,B_195] :
      ( v4_orders_2(C_193)
      | ~ m2_yellow_6(C_193,A_194,B_195)
      | ~ l1_waybel_0(B_195,A_194)
      | ~ v7_waybel_0(B_195)
      | ~ v4_orders_2(B_195)
      | v2_struct_0(B_195)
      | ~ l1_struct_0(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_179,plain,(
    ! [B_158] :
      ( v4_orders_2('#skF_9'(B_158))
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(resolution,[status(thm)],[c_145,c_176])).

tff(c_182,plain,(
    ! [B_158] :
      ( v4_orders_2('#skF_9'(B_158))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_179])).

tff(c_183,plain,(
    ! [B_158] :
      ( v4_orders_2('#skF_9'(B_158))
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_182])).

tff(c_1395,plain,
    ( ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1384])).

tff(c_1397,plain,(
    ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_1395])).

tff(c_1400,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_183,c_1397])).

tff(c_1403,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_1326,c_1396,c_1400])).

tff(c_1406,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1403,c_64])).

tff(c_1409,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1406])).

tff(c_1411,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1409])).

tff(c_1412,plain,
    ( k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1395])).

tff(c_1445,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_1412])).

tff(c_1448,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1445,c_64])).

tff(c_1451,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1448])).

tff(c_1453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_111,c_1451])).

tff(c_1455,plain,(
    ~ v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_1412])).

tff(c_1454,plain,
    ( v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1412])).

tff(c_1456,plain,(
    k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1454])).

tff(c_98,plain,(
    ! [B_158] :
      ( v1_compts_1('#skF_7')
      | v3_yellow_6('#skF_9'(B_158),'#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_142,plain,(
    ! [B_158] :
      ( v3_yellow_6('#skF_9'(B_158),'#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_98])).

tff(c_194,plain,(
    ! [A_201,B_202] :
      ( k10_yellow_6(A_201,B_202) != k1_xboole_0
      | ~ v3_yellow_6(B_202,A_201)
      | ~ l1_waybel_0(B_202,A_201)
      | ~ v7_waybel_0(B_202)
      | ~ v4_orders_2(B_202)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_197,plain,(
    ! [B_158] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_158)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_9'(B_158),'#skF_7')
      | ~ v7_waybel_0('#skF_9'(B_158))
      | ~ v4_orders_2('#skF_9'(B_158))
      | v2_struct_0('#skF_9'(B_158))
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(resolution,[status(thm)],[c_142,c_194])).

tff(c_200,plain,(
    ! [B_158] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_158)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_9'(B_158),'#skF_7')
      | ~ v7_waybel_0('#skF_9'(B_158))
      | ~ v4_orders_2('#skF_9'(B_158))
      | v2_struct_0('#skF_9'(B_158))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_197])).

tff(c_225,plain,(
    ! [B_219] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_219)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_9'(B_219),'#skF_7')
      | ~ v7_waybel_0('#skF_9'(B_219))
      | ~ v4_orders_2('#skF_9'(B_219))
      | v2_struct_0('#skF_9'(B_219))
      | ~ l1_waybel_0(B_219,'#skF_7')
      | ~ v7_waybel_0(B_219)
      | ~ v4_orders_2(B_219)
      | v2_struct_0(B_219) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_200])).

tff(c_230,plain,(
    ! [B_220] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_220)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_9'(B_220))
      | ~ v4_orders_2('#skF_9'(B_220))
      | v2_struct_0('#skF_9'(B_220))
      | ~ l1_waybel_0(B_220,'#skF_7')
      | ~ v7_waybel_0(B_220)
      | ~ v4_orders_2(B_220)
      | v2_struct_0(B_220) ) ),
    inference(resolution,[status(thm)],[c_191,c_225])).

tff(c_235,plain,(
    ! [B_221] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_221)) != k1_xboole_0
      | ~ v4_orders_2('#skF_9'(B_221))
      | v2_struct_0('#skF_9'(B_221))
      | ~ l1_waybel_0(B_221,'#skF_7')
      | ~ v7_waybel_0(B_221)
      | ~ v4_orders_2(B_221)
      | v2_struct_0(B_221) ) ),
    inference(resolution,[status(thm)],[c_164,c_230])).

tff(c_240,plain,(
    ! [B_222] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_222)) != k1_xboole_0
      | v2_struct_0('#skF_9'(B_222))
      | ~ l1_waybel_0(B_222,'#skF_7')
      | ~ v7_waybel_0(B_222)
      | ~ v4_orders_2(B_222)
      | v2_struct_0(B_222) ) ),
    inference(resolution,[status(thm)],[c_183,c_235])).

tff(c_167,plain,(
    ! [C_189,A_190,B_191] :
      ( ~ v2_struct_0(C_189)
      | ~ m2_yellow_6(C_189,A_190,B_191)
      | ~ l1_waybel_0(B_191,A_190)
      | ~ v7_waybel_0(B_191)
      | ~ v4_orders_2(B_191)
      | v2_struct_0(B_191)
      | ~ l1_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_170,plain,(
    ! [B_158] :
      ( ~ v2_struct_0('#skF_9'(B_158))
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(resolution,[status(thm)],[c_145,c_167])).

tff(c_173,plain,(
    ! [B_158] :
      ( ~ v2_struct_0('#skF_9'(B_158))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_170])).

tff(c_174,plain,(
    ! [B_158] :
      ( ~ v2_struct_0('#skF_9'(B_158))
      | ~ l1_waybel_0(B_158,'#skF_7')
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_173])).

tff(c_244,plain,(
    ! [B_222] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_222)) != k1_xboole_0
      | ~ l1_waybel_0(B_222,'#skF_7')
      | ~ v7_waybel_0(B_222)
      | ~ v4_orders_2(B_222)
      | v2_struct_0(B_222) ) ),
    inference(resolution,[status(thm)],[c_240,c_174])).

tff(c_1505,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1456,c_244])).

tff(c_1573,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_1326,c_1396,c_1505])).

tff(c_1575,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_1573])).

tff(c_1576,plain,(
    v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_1454])).

tff(c_1580,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1576,c_174])).

tff(c_1583,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_1326,c_1396,c_1580])).

tff(c_1585,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1455,c_1583])).

tff(c_1586,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_1587,plain,(
    v1_compts_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_82,plain,
    ( v4_orders_2('#skF_8')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_1589,plain,(
    v4_orders_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_82])).

tff(c_80,plain,
    ( v7_waybel_0('#skF_8')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_1591,plain,(
    v7_waybel_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_80])).

tff(c_78,plain,
    ( l1_waybel_0('#skF_8','#skF_7')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_1595,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_78])).

tff(c_66,plain,(
    ! [A_139,B_146] :
      ( r3_waybel_9(A_139,B_146,'#skF_5'(A_139,B_146))
      | ~ l1_waybel_0(B_146,A_139)
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_68,plain,(
    ! [A_139,B_146] :
      ( m1_subset_1('#skF_5'(A_139,B_146),u1_struct_0(A_139))
      | ~ l1_waybel_0(B_146,A_139)
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_1598,plain,(
    ! [A_512,B_513] :
      ( r1_tarski(A_512,B_513)
      | ~ m1_subset_1(A_512,k1_zfmisc_1(B_513)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1606,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(resolution,[status(thm)],[c_2,c_1598])).

tff(c_1661,plain,(
    ! [A_560,B_561,C_562] :
      ( m2_yellow_6('#skF_4'(A_560,B_561,C_562),A_560,B_561)
      | ~ r3_waybel_9(A_560,B_561,C_562)
      | ~ m1_subset_1(C_562,u1_struct_0(A_560))
      | ~ l1_waybel_0(B_561,A_560)
      | ~ v7_waybel_0(B_561)
      | ~ v4_orders_2(B_561)
      | v2_struct_0(B_561)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_36,plain,(
    ! [C_99,A_96,B_97] :
      ( l1_waybel_0(C_99,A_96)
      | ~ m2_yellow_6(C_99,A_96,B_97)
      | ~ l1_waybel_0(B_97,A_96)
      | ~ v7_waybel_0(B_97)
      | ~ v4_orders_2(B_97)
      | v2_struct_0(B_97)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1753,plain,(
    ! [A_587,B_588,C_589] :
      ( l1_waybel_0('#skF_4'(A_587,B_588,C_589),A_587)
      | ~ l1_struct_0(A_587)
      | ~ r3_waybel_9(A_587,B_588,C_589)
      | ~ m1_subset_1(C_589,u1_struct_0(A_587))
      | ~ l1_waybel_0(B_588,A_587)
      | ~ v7_waybel_0(B_588)
      | ~ v4_orders_2(B_588)
      | v2_struct_0(B_588)
      | ~ l1_pre_topc(A_587)
      | ~ v2_pre_topc(A_587)
      | v2_struct_0(A_587) ) ),
    inference(resolution,[status(thm)],[c_1661,c_36])).

tff(c_1811,plain,(
    ! [A_636,B_637,B_638] :
      ( l1_waybel_0('#skF_4'(A_636,B_637,'#skF_5'(A_636,B_638)),A_636)
      | ~ l1_struct_0(A_636)
      | ~ r3_waybel_9(A_636,B_637,'#skF_5'(A_636,B_638))
      | ~ l1_waybel_0(B_637,A_636)
      | ~ v7_waybel_0(B_637)
      | ~ v4_orders_2(B_637)
      | v2_struct_0(B_637)
      | ~ l1_waybel_0(B_638,A_636)
      | ~ v7_waybel_0(B_638)
      | ~ v4_orders_2(B_638)
      | v2_struct_0(B_638)
      | ~ v1_compts_1(A_636)
      | ~ l1_pre_topc(A_636)
      | ~ v2_pre_topc(A_636)
      | v2_struct_0(A_636) ) ),
    inference(resolution,[status(thm)],[c_68,c_1753])).

tff(c_44,plain,(
    ! [B_102,A_100] :
      ( v3_yellow_6(B_102,A_100)
      | k10_yellow_6(A_100,B_102) = k1_xboole_0
      | ~ l1_waybel_0(B_102,A_100)
      | ~ v7_waybel_0(B_102)
      | ~ v4_orders_2(B_102)
      | v2_struct_0(B_102)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_76,plain,(
    ! [C_157] :
      ( ~ v3_yellow_6(C_157,'#skF_7')
      | ~ m2_yellow_6(C_157,'#skF_7','#skF_8')
      | ~ v1_compts_1('#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_1609,plain,(
    ! [C_157] :
      ( ~ v3_yellow_6(C_157,'#skF_7')
      | ~ m2_yellow_6(C_157,'#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1587,c_76])).

tff(c_1677,plain,(
    ! [C_562] :
      ( ~ v3_yellow_6('#skF_4'('#skF_7','#skF_8',C_562),'#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8',C_562)
      | ~ m1_subset_1(C_562,u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1661,c_1609])).

tff(c_1684,plain,(
    ! [C_562] :
      ( ~ v3_yellow_6('#skF_4'('#skF_7','#skF_8',C_562),'#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8',C_562)
      | ~ m1_subset_1(C_562,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1589,c_1591,c_1595,c_1677])).

tff(c_1686,plain,(
    ! [C_563] :
      ( ~ v3_yellow_6('#skF_4'('#skF_7','#skF_8',C_563),'#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8',C_563)
      | ~ m1_subset_1(C_563,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1586,c_1684])).

tff(c_1689,plain,(
    ! [C_563] :
      ( ~ r3_waybel_9('#skF_7','#skF_8',C_563)
      | ~ m1_subset_1(C_563,u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8',C_563)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8',C_563),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8',C_563))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8',C_563))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8',C_563))
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_44,c_1686])).

tff(c_1692,plain,(
    ! [C_563] :
      ( ~ r3_waybel_9('#skF_7','#skF_8',C_563)
      | ~ m1_subset_1(C_563,u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8',C_563)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8',C_563),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8',C_563))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8',C_563))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8',C_563))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1689])).

tff(c_1694,plain,(
    ! [C_564] :
      ( ~ r3_waybel_9('#skF_7','#skF_8',C_564)
      | ~ m1_subset_1(C_564,u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8',C_564)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8',C_564),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8',C_564))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8',C_564))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8',C_564)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1692])).

tff(c_1698,plain,(
    ! [B_146] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_1694])).

tff(c_1701,plain,(
    ! [B_146] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1587,c_1698])).

tff(c_1702,plain,(
    ! [B_146] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1701])).

tff(c_1815,plain,(
    ! [B_638] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_638))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_638,'#skF_7')
      | ~ v7_waybel_0(B_638)
      | ~ v4_orders_2(B_638)
      | v2_struct_0(B_638)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1811,c_1702])).

tff(c_1818,plain,(
    ! [B_638] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_638))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_638,'#skF_7')
      | ~ v7_waybel_0(B_638)
      | ~ v4_orders_2(B_638)
      | v2_struct_0(B_638)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1587,c_1589,c_1591,c_1595,c_1815])).

tff(c_1819,plain,(
    ! [B_638] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_638)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_638))
      | ~ l1_waybel_0(B_638,'#skF_7')
      | ~ v7_waybel_0(B_638)
      | ~ v4_orders_2(B_638)
      | v2_struct_0(B_638) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1586,c_1818])).

tff(c_1828,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1819])).

tff(c_1831,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_1828])).

tff(c_1835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1831])).

tff(c_1837,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1819])).

tff(c_40,plain,(
    ! [C_99,A_96,B_97] :
      ( v4_orders_2(C_99)
      | ~ m2_yellow_6(C_99,A_96,B_97)
      | ~ l1_waybel_0(B_97,A_96)
      | ~ v7_waybel_0(B_97)
      | ~ v4_orders_2(B_97)
      | v2_struct_0(B_97)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1703,plain,(
    ! [A_565,B_566,C_567] :
      ( v4_orders_2('#skF_4'(A_565,B_566,C_567))
      | ~ l1_struct_0(A_565)
      | ~ r3_waybel_9(A_565,B_566,C_567)
      | ~ m1_subset_1(C_567,u1_struct_0(A_565))
      | ~ l1_waybel_0(B_566,A_565)
      | ~ v7_waybel_0(B_566)
      | ~ v4_orders_2(B_566)
      | v2_struct_0(B_566)
      | ~ l1_pre_topc(A_565)
      | ~ v2_pre_topc(A_565)
      | v2_struct_0(A_565) ) ),
    inference(resolution,[status(thm)],[c_1661,c_40])).

tff(c_1706,plain,(
    ! [A_139,B_566,B_146] :
      ( v4_orders_2('#skF_4'(A_139,B_566,'#skF_5'(A_139,B_146)))
      | ~ l1_struct_0(A_139)
      | ~ r3_waybel_9(A_139,B_566,'#skF_5'(A_139,B_146))
      | ~ l1_waybel_0(B_566,A_139)
      | ~ v7_waybel_0(B_566)
      | ~ v4_orders_2(B_566)
      | v2_struct_0(B_566)
      | ~ l1_waybel_0(B_146,A_139)
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_68,c_1703])).

tff(c_38,plain,(
    ! [C_99,A_96,B_97] :
      ( v7_waybel_0(C_99)
      | ~ m2_yellow_6(C_99,A_96,B_97)
      | ~ l1_waybel_0(B_97,A_96)
      | ~ v7_waybel_0(B_97)
      | ~ v4_orders_2(B_97)
      | v2_struct_0(B_97)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1708,plain,(
    ! [A_571,B_572,C_573] :
      ( v7_waybel_0('#skF_4'(A_571,B_572,C_573))
      | ~ l1_struct_0(A_571)
      | ~ r3_waybel_9(A_571,B_572,C_573)
      | ~ m1_subset_1(C_573,u1_struct_0(A_571))
      | ~ l1_waybel_0(B_572,A_571)
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572)
      | ~ l1_pre_topc(A_571)
      | ~ v2_pre_topc(A_571)
      | v2_struct_0(A_571) ) ),
    inference(resolution,[status(thm)],[c_1661,c_38])).

tff(c_1711,plain,(
    ! [A_139,B_572,B_146] :
      ( v7_waybel_0('#skF_4'(A_139,B_572,'#skF_5'(A_139,B_146)))
      | ~ l1_struct_0(A_139)
      | ~ r3_waybel_9(A_139,B_572,'#skF_5'(A_139,B_146))
      | ~ l1_waybel_0(B_572,A_139)
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572)
      | ~ l1_waybel_0(B_146,A_139)
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ v1_compts_1(A_139)
      | ~ l1_pre_topc(A_139)
      | ~ v2_pre_topc(A_139)
      | v2_struct_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_68,c_1708])).

tff(c_1838,plain,(
    ! [B_643] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_643))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_643)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_643)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_643)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_643))
      | ~ l1_waybel_0(B_643,'#skF_7')
      | ~ v7_waybel_0(B_643)
      | ~ v4_orders_2(B_643)
      | v2_struct_0(B_643) ) ),
    inference(splitRight,[status(thm)],[c_1819])).

tff(c_1842,plain,(
    ! [B_146] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1711,c_1838])).

tff(c_1845,plain,(
    ! [B_146] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1587,c_1589,c_1591,c_1595,c_1837,c_1842])).

tff(c_1847,plain,(
    ! [B_644] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_644))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_644)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_644)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_644))
      | ~ l1_waybel_0(B_644,'#skF_7')
      | ~ v7_waybel_0(B_644)
      | ~ v4_orders_2(B_644)
      | v2_struct_0(B_644) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1586,c_1845])).

tff(c_1851,plain,(
    ! [B_146] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1706,c_1847])).

tff(c_1854,plain,(
    ! [B_146] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1587,c_1589,c_1591,c_1595,c_1837,c_1851])).

tff(c_1856,plain,(
    ! [B_645] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_645))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_645)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_645))
      | ~ l1_waybel_0(B_645,'#skF_7')
      | ~ v7_waybel_0(B_645)
      | ~ v4_orders_2(B_645)
      | v2_struct_0(B_645) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1586,c_1854])).

tff(c_42,plain,(
    ! [C_99,A_96,B_97] :
      ( ~ v2_struct_0(C_99)
      | ~ m2_yellow_6(C_99,A_96,B_97)
      | ~ l1_waybel_0(B_97,A_96)
      | ~ v7_waybel_0(B_97)
      | ~ v4_orders_2(B_97)
      | v2_struct_0(B_97)
      | ~ l1_struct_0(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1681,plain,(
    ! [A_560,B_561,C_562] :
      ( ~ v2_struct_0('#skF_4'(A_560,B_561,C_562))
      | ~ l1_struct_0(A_560)
      | ~ r3_waybel_9(A_560,B_561,C_562)
      | ~ m1_subset_1(C_562,u1_struct_0(A_560))
      | ~ l1_waybel_0(B_561,A_560)
      | ~ v7_waybel_0(B_561)
      | ~ v4_orders_2(B_561)
      | v2_struct_0(B_561)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(resolution,[status(thm)],[c_1661,c_42])).

tff(c_1858,plain,(
    ! [B_645] :
      ( ~ l1_struct_0('#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_7',B_645),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_645))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_645))
      | ~ l1_waybel_0(B_645,'#skF_7')
      | ~ v7_waybel_0(B_645)
      | ~ v4_orders_2(B_645)
      | v2_struct_0(B_645) ) ),
    inference(resolution,[status(thm)],[c_1856,c_1681])).

tff(c_1861,plain,(
    ! [B_645] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_645),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7')
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_645))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_645))
      | ~ l1_waybel_0(B_645,'#skF_7')
      | ~ v7_waybel_0(B_645)
      | ~ v4_orders_2(B_645)
      | v2_struct_0(B_645) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1589,c_1591,c_1595,c_1837,c_1858])).

tff(c_1863,plain,(
    ! [B_646] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_646),u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_646))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_646))
      | ~ l1_waybel_0(B_646,'#skF_7')
      | ~ v7_waybel_0(B_646)
      | ~ v4_orders_2(B_646)
      | v2_struct_0(B_646) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1586,c_1861])).

tff(c_1867,plain,(
    ! [B_146] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_1863])).

tff(c_1870,plain,(
    ! [B_146] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1587,c_1867])).

tff(c_1872,plain,(
    ! [B_647] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_647))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_647))
      | ~ l1_waybel_0(B_647,'#skF_7')
      | ~ v7_waybel_0(B_647)
      | ~ v4_orders_2(B_647)
      | v2_struct_0(B_647) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1870])).

tff(c_1727,plain,(
    ! [C_577,A_578,B_579] :
      ( r2_hidden(C_577,k10_yellow_6(A_578,'#skF_4'(A_578,B_579,C_577)))
      | ~ r3_waybel_9(A_578,B_579,C_577)
      | ~ m1_subset_1(C_577,u1_struct_0(A_578))
      | ~ l1_waybel_0(B_579,A_578)
      | ~ v7_waybel_0(B_579)
      | ~ v4_orders_2(B_579)
      | v2_struct_0(B_579)
      | ~ l1_pre_topc(A_578)
      | ~ v2_pre_topc(A_578)
      | v2_struct_0(A_578) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_1742,plain,(
    ! [A_578,B_579,C_577] :
      ( ~ r1_tarski(k10_yellow_6(A_578,'#skF_4'(A_578,B_579,C_577)),C_577)
      | ~ r3_waybel_9(A_578,B_579,C_577)
      | ~ m1_subset_1(C_577,u1_struct_0(A_578))
      | ~ l1_waybel_0(B_579,A_578)
      | ~ v7_waybel_0(B_579)
      | ~ v4_orders_2(B_579)
      | v2_struct_0(B_579)
      | ~ l1_pre_topc(A_578)
      | ~ v2_pre_topc(A_578)
      | v2_struct_0(A_578) ) ),
    inference(resolution,[status(thm)],[c_1727,c_10])).

tff(c_1886,plain,(
    ! [B_647] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_5'('#skF_7',B_647))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_647))
      | ~ m1_subset_1('#skF_5'('#skF_7',B_647),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_647))
      | ~ l1_waybel_0(B_647,'#skF_7')
      | ~ v7_waybel_0(B_647)
      | ~ v4_orders_2(B_647)
      | v2_struct_0(B_647) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1872,c_1742])).

tff(c_1916,plain,(
    ! [B_647] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_647),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_647))
      | ~ l1_waybel_0(B_647,'#skF_7')
      | ~ v7_waybel_0(B_647)
      | ~ v4_orders_2(B_647)
      | v2_struct_0(B_647) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1589,c_1591,c_1595,c_1606,c_1886])).

tff(c_1934,plain,(
    ! [B_648] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_648),u1_struct_0('#skF_7'))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_648))
      | ~ l1_waybel_0(B_648,'#skF_7')
      | ~ v7_waybel_0(B_648)
      | ~ v4_orders_2(B_648)
      | v2_struct_0(B_648) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1586,c_1916])).

tff(c_1938,plain,(
    ! [B_146] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_1934])).

tff(c_1941,plain,(
    ! [B_146] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_146))
      | ~ l1_waybel_0(B_146,'#skF_7')
      | ~ v7_waybel_0(B_146)
      | ~ v4_orders_2(B_146)
      | v2_struct_0(B_146)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1587,c_1938])).

tff(c_1947,plain,(
    ! [B_652] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_652))
      | ~ l1_waybel_0(B_652,'#skF_7')
      | ~ v7_waybel_0(B_652)
      | ~ v4_orders_2(B_652)
      | v2_struct_0(B_652) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1941])).

tff(c_1955,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ v7_waybel_0('#skF_8')
    | ~ v4_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_1947])).

tff(c_1962,plain,
    ( v2_struct_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1587,c_1589,c_1591,c_1595,c_1955])).

tff(c_1964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1586,c_1962])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.94/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.46  
% 6.94/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.46  %$ r3_waybel_9 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_9 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_6
% 6.94/2.46  
% 6.94/2.46  %Foreground sorts:
% 6.94/2.46  
% 6.94/2.46  
% 6.94/2.46  %Background operators:
% 6.94/2.46  
% 6.94/2.46  
% 6.94/2.46  %Foreground operators:
% 6.94/2.46  tff('#skF_9', type, '#skF_9': $i > $i).
% 6.94/2.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.94/2.46  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 6.94/2.46  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.94/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.94/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.94/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.94/2.46  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 6.94/2.46  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 6.94/2.46  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.94/2.46  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 6.94/2.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.94/2.46  tff('#skF_7', type, '#skF_7': $i).
% 6.94/2.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.94/2.46  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 6.94/2.46  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 6.94/2.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.94/2.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.94/2.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.94/2.46  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.94/2.46  tff('#skF_8', type, '#skF_8': $i).
% 6.94/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.94/2.46  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 6.94/2.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.94/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.94/2.46  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.94/2.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.94/2.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.94/2.46  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 6.94/2.46  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.94/2.46  tff('#skF_6', type, '#skF_6': $i > $i).
% 6.94/2.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.94/2.46  
% 7.35/2.49  tff(f_273, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow19)).
% 7.35/2.49  tff(f_248, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_yellow19)).
% 7.35/2.49  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 7.35/2.49  tff(f_78, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 7.35/2.49  tff(f_31, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.35/2.49  tff(f_96, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 7.35/2.49  tff(f_168, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_waybel_9)).
% 7.35/2.49  tff(f_42, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.35/2.49  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_waybel_9)).
% 7.35/2.49  tff(f_46, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 7.35/2.49  tff(f_122, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 7.35/2.49  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_yellow_6)).
% 7.35/2.50  tff(f_224, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 7.35/2.50  tff(c_74, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_84, plain, (~v2_struct_0('#skF_8') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_111, plain, (~v1_compts_1('#skF_7')), inference(splitLeft, [status(thm)], [c_84])).
% 7.35/2.50  tff(c_72, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_70, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_62, plain, (![A_139]: (v4_orders_2('#skF_6'(A_139)) | v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.35/2.50  tff(c_110, plain, (![B_158]: (v1_compts_1('#skF_7') | m2_yellow_6('#skF_9'(B_158), '#skF_7', B_158) | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_145, plain, (![B_158]: (m2_yellow_6('#skF_9'(B_158), '#skF_7', B_158) | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(negUnitSimplification, [status(thm)], [c_111, c_110])).
% 7.35/2.50  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.35/2.50  tff(c_14, plain, (![A_10, B_54, C_76]: (m1_subset_1('#skF_2'(A_10, B_54, C_76), u1_struct_0(A_10)) | k10_yellow_6(A_10, B_54)=C_76 | ~m1_subset_1(C_76, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_waybel_0(B_54, A_10) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.35/2.50  tff(c_116, plain, (![A_166, B_167]: (r1_tarski(A_166, B_167) | ~m1_subset_1(A_166, k1_zfmisc_1(B_167)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.35/2.50  tff(c_124, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_116])).
% 7.35/2.50  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.35/2.50  tff(c_34, plain, (![A_94, B_95]: (m1_subset_1(k10_yellow_6(A_94, B_95), k1_zfmisc_1(u1_struct_0(A_94))) | ~l1_waybel_0(B_95, A_94) | ~v7_waybel_0(B_95) | ~v4_orders_2(B_95) | v2_struct_0(B_95) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.35/2.50  tff(c_324, plain, (![A_266, B_267, D_268]: (m1_connsp_2('#skF_1'(A_266, B_267, k10_yellow_6(A_266, B_267), D_268), A_266, D_268) | r2_hidden(D_268, k10_yellow_6(A_266, B_267)) | ~m1_subset_1(D_268, u1_struct_0(A_266)) | ~m1_subset_1(k10_yellow_6(A_266, B_267), k1_zfmisc_1(u1_struct_0(A_266))) | ~l1_waybel_0(B_267, A_266) | ~v7_waybel_0(B_267) | ~v4_orders_2(B_267) | v2_struct_0(B_267) | ~l1_pre_topc(A_266) | ~v2_pre_topc(A_266) | v2_struct_0(A_266))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.35/2.50  tff(c_330, plain, (![A_94, B_95, D_268]: (m1_connsp_2('#skF_1'(A_94, B_95, k10_yellow_6(A_94, B_95), D_268), A_94, D_268) | r2_hidden(D_268, k10_yellow_6(A_94, B_95)) | ~m1_subset_1(D_268, u1_struct_0(A_94)) | ~l1_waybel_0(B_95, A_94) | ~v7_waybel_0(B_95) | ~v4_orders_2(B_95) | v2_struct_0(B_95) | ~l1_pre_topc(A_94) | ~v2_pre_topc(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_34, c_324])).
% 7.35/2.50  tff(c_336, plain, (![A_272, B_273, C_274, E_275]: (r2_hidden('#skF_2'(A_272, B_273, C_274), C_274) | r1_waybel_0(A_272, B_273, E_275) | ~m1_connsp_2(E_275, A_272, '#skF_2'(A_272, B_273, C_274)) | k10_yellow_6(A_272, B_273)=C_274 | ~m1_subset_1(C_274, k1_zfmisc_1(u1_struct_0(A_272))) | ~l1_waybel_0(B_273, A_272) | ~v7_waybel_0(B_273) | ~v4_orders_2(B_273) | v2_struct_0(B_273) | ~l1_pre_topc(A_272) | ~v2_pre_topc(A_272) | v2_struct_0(A_272))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.35/2.50  tff(c_458, plain, (![A_376, B_377, C_378, B_379]: (r2_hidden('#skF_2'(A_376, B_377, C_378), C_378) | r1_waybel_0(A_376, B_377, '#skF_1'(A_376, B_379, k10_yellow_6(A_376, B_379), '#skF_2'(A_376, B_377, C_378))) | k10_yellow_6(A_376, B_377)=C_378 | ~m1_subset_1(C_378, k1_zfmisc_1(u1_struct_0(A_376))) | ~l1_waybel_0(B_377, A_376) | ~v7_waybel_0(B_377) | ~v4_orders_2(B_377) | v2_struct_0(B_377) | r2_hidden('#skF_2'(A_376, B_377, C_378), k10_yellow_6(A_376, B_379)) | ~m1_subset_1('#skF_2'(A_376, B_377, C_378), u1_struct_0(A_376)) | ~l1_waybel_0(B_379, A_376) | ~v7_waybel_0(B_379) | ~v4_orders_2(B_379) | v2_struct_0(B_379) | ~l1_pre_topc(A_376) | ~v2_pre_topc(A_376) | v2_struct_0(A_376))), inference(resolution, [status(thm)], [c_330, c_336])).
% 7.35/2.50  tff(c_30, plain, (![A_10, B_54, D_87]: (~r1_waybel_0(A_10, B_54, '#skF_1'(A_10, B_54, k10_yellow_6(A_10, B_54), D_87)) | r2_hidden(D_87, k10_yellow_6(A_10, B_54)) | ~m1_subset_1(D_87, u1_struct_0(A_10)) | ~m1_subset_1(k10_yellow_6(A_10, B_54), k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_waybel_0(B_54, A_10) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.35/2.50  tff(c_485, plain, (![A_380, B_381, C_382]: (~m1_subset_1(k10_yellow_6(A_380, B_381), k1_zfmisc_1(u1_struct_0(A_380))) | r2_hidden('#skF_2'(A_380, B_381, C_382), C_382) | k10_yellow_6(A_380, B_381)=C_382 | ~m1_subset_1(C_382, k1_zfmisc_1(u1_struct_0(A_380))) | r2_hidden('#skF_2'(A_380, B_381, C_382), k10_yellow_6(A_380, B_381)) | ~m1_subset_1('#skF_2'(A_380, B_381, C_382), u1_struct_0(A_380)) | ~l1_waybel_0(B_381, A_380) | ~v7_waybel_0(B_381) | ~v4_orders_2(B_381) | v2_struct_0(B_381) | ~l1_pre_topc(A_380) | ~v2_pre_topc(A_380) | v2_struct_0(A_380))), inference(resolution, [status(thm)], [c_458, c_30])).
% 7.35/2.50  tff(c_509, plain, (![A_383, B_384, C_385]: (r2_hidden('#skF_2'(A_383, B_384, C_385), C_385) | k10_yellow_6(A_383, B_384)=C_385 | ~m1_subset_1(C_385, k1_zfmisc_1(u1_struct_0(A_383))) | r2_hidden('#skF_2'(A_383, B_384, C_385), k10_yellow_6(A_383, B_384)) | ~m1_subset_1('#skF_2'(A_383, B_384, C_385), u1_struct_0(A_383)) | ~l1_waybel_0(B_384, A_383) | ~v7_waybel_0(B_384) | ~v4_orders_2(B_384) | v2_struct_0(B_384) | ~l1_pre_topc(A_383) | ~v2_pre_topc(A_383) | v2_struct_0(A_383))), inference(resolution, [status(thm)], [c_34, c_485])).
% 7.35/2.50  tff(c_48, plain, (![A_103, B_107, C_109]: (r3_waybel_9(A_103, B_107, C_109) | ~r2_hidden(C_109, k10_yellow_6(A_103, B_107)) | ~m1_subset_1(C_109, u1_struct_0(A_103)) | ~l1_waybel_0(B_107, A_103) | ~v7_waybel_0(B_107) | ~v4_orders_2(B_107) | v2_struct_0(B_107) | ~l1_pre_topc(A_103) | ~v2_pre_topc(A_103) | v2_struct_0(A_103))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.35/2.50  tff(c_550, plain, (![A_386, B_387, C_388]: (r3_waybel_9(A_386, B_387, '#skF_2'(A_386, B_387, C_388)) | r2_hidden('#skF_2'(A_386, B_387, C_388), C_388) | k10_yellow_6(A_386, B_387)=C_388 | ~m1_subset_1(C_388, k1_zfmisc_1(u1_struct_0(A_386))) | ~m1_subset_1('#skF_2'(A_386, B_387, C_388), u1_struct_0(A_386)) | ~l1_waybel_0(B_387, A_386) | ~v7_waybel_0(B_387) | ~v4_orders_2(B_387) | v2_struct_0(B_387) | ~l1_pre_topc(A_386) | ~v2_pre_topc(A_386) | v2_struct_0(A_386))), inference(resolution, [status(thm)], [c_509, c_48])).
% 7.35/2.50  tff(c_554, plain, (![A_389, B_390, C_391]: (r3_waybel_9(A_389, B_390, '#skF_2'(A_389, B_390, C_391)) | r2_hidden('#skF_2'(A_389, B_390, C_391), C_391) | k10_yellow_6(A_389, B_390)=C_391 | ~m1_subset_1(C_391, k1_zfmisc_1(u1_struct_0(A_389))) | ~l1_waybel_0(B_390, A_389) | ~v7_waybel_0(B_390) | ~v4_orders_2(B_390) | v2_struct_0(B_390) | ~l1_pre_topc(A_389) | ~v2_pre_topc(A_389) | v2_struct_0(A_389))), inference(resolution, [status(thm)], [c_14, c_550])).
% 7.35/2.50  tff(c_575, plain, (![A_394, B_395, A_396]: (r3_waybel_9(A_394, B_395, '#skF_2'(A_394, B_395, A_396)) | r2_hidden('#skF_2'(A_394, B_395, A_396), A_396) | k10_yellow_6(A_394, B_395)=A_396 | ~l1_waybel_0(B_395, A_394) | ~v7_waybel_0(B_395) | ~v4_orders_2(B_395) | v2_struct_0(B_395) | ~l1_pre_topc(A_394) | ~v2_pre_topc(A_394) | v2_struct_0(A_394) | ~r1_tarski(A_396, u1_struct_0(A_394)))), inference(resolution, [status(thm)], [c_6, c_554])).
% 7.35/2.50  tff(c_10, plain, (![B_8, A_7]: (~r1_tarski(B_8, A_7) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.35/2.50  tff(c_620, plain, (![A_401, A_402, B_403]: (~r1_tarski(A_401, '#skF_2'(A_402, B_403, A_401)) | r3_waybel_9(A_402, B_403, '#skF_2'(A_402, B_403, A_401)) | k10_yellow_6(A_402, B_403)=A_401 | ~l1_waybel_0(B_403, A_402) | ~v7_waybel_0(B_403) | ~v4_orders_2(B_403) | v2_struct_0(B_403) | ~l1_pre_topc(A_402) | ~v2_pre_topc(A_402) | v2_struct_0(A_402) | ~r1_tarski(A_401, u1_struct_0(A_402)))), inference(resolution, [status(thm)], [c_575, c_10])).
% 7.35/2.50  tff(c_623, plain, (![A_402, B_403]: (r3_waybel_9(A_402, B_403, '#skF_2'(A_402, B_403, k1_xboole_0)) | k10_yellow_6(A_402, B_403)=k1_xboole_0 | ~l1_waybel_0(B_403, A_402) | ~v7_waybel_0(B_403) | ~v4_orders_2(B_403) | v2_struct_0(B_403) | ~l1_pre_topc(A_402) | ~v2_pre_topc(A_402) | v2_struct_0(A_402) | ~r1_tarski(k1_xboole_0, u1_struct_0(A_402)))), inference(resolution, [status(thm)], [c_124, c_620])).
% 7.35/2.50  tff(c_627, plain, (![A_404, B_405]: (r3_waybel_9(A_404, B_405, '#skF_2'(A_404, B_405, k1_xboole_0)) | k10_yellow_6(A_404, B_405)=k1_xboole_0 | ~l1_waybel_0(B_405, A_404) | ~v7_waybel_0(B_405) | ~v4_orders_2(B_405) | v2_struct_0(B_405) | ~l1_pre_topc(A_404) | ~v2_pre_topc(A_404) | v2_struct_0(A_404))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_623])).
% 7.35/2.50  tff(c_50, plain, (![A_110, B_118, D_124, C_122]: (r3_waybel_9(A_110, B_118, D_124) | ~r3_waybel_9(A_110, C_122, D_124) | ~m1_subset_1(D_124, u1_struct_0(A_110)) | ~m2_yellow_6(C_122, A_110, B_118) | ~l1_waybel_0(B_118, A_110) | ~v7_waybel_0(B_118) | ~v4_orders_2(B_118) | v2_struct_0(B_118) | ~l1_pre_topc(A_110) | ~v2_pre_topc(A_110) | v2_struct_0(A_110))), inference(cnfTransformation, [status(thm)], [f_195])).
% 7.35/2.50  tff(c_1103, plain, (![A_473, B_474, B_475]: (r3_waybel_9(A_473, B_474, '#skF_2'(A_473, B_475, k1_xboole_0)) | ~m1_subset_1('#skF_2'(A_473, B_475, k1_xboole_0), u1_struct_0(A_473)) | ~m2_yellow_6(B_475, A_473, B_474) | ~l1_waybel_0(B_474, A_473) | ~v7_waybel_0(B_474) | ~v4_orders_2(B_474) | v2_struct_0(B_474) | k10_yellow_6(A_473, B_475)=k1_xboole_0 | ~l1_waybel_0(B_475, A_473) | ~v7_waybel_0(B_475) | ~v4_orders_2(B_475) | v2_struct_0(B_475) | ~l1_pre_topc(A_473) | ~v2_pre_topc(A_473) | v2_struct_0(A_473))), inference(resolution, [status(thm)], [c_627, c_50])).
% 7.35/2.50  tff(c_1112, plain, (![A_10, B_474, B_54]: (r3_waybel_9(A_10, B_474, '#skF_2'(A_10, B_54, k1_xboole_0)) | ~m2_yellow_6(B_54, A_10, B_474) | ~l1_waybel_0(B_474, A_10) | ~v7_waybel_0(B_474) | ~v4_orders_2(B_474) | v2_struct_0(B_474) | k10_yellow_6(A_10, B_54)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_waybel_0(B_54, A_10) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(resolution, [status(thm)], [c_14, c_1103])).
% 7.35/2.50  tff(c_1122, plain, (![A_476, B_477, B_478]: (r3_waybel_9(A_476, B_477, '#skF_2'(A_476, B_478, k1_xboole_0)) | ~m2_yellow_6(B_478, A_476, B_477) | ~l1_waybel_0(B_477, A_476) | ~v7_waybel_0(B_477) | ~v4_orders_2(B_477) | v2_struct_0(B_477) | k10_yellow_6(A_476, B_478)=k1_xboole_0 | ~l1_waybel_0(B_478, A_476) | ~v7_waybel_0(B_478) | ~v4_orders_2(B_478) | v2_struct_0(B_478) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1112])).
% 7.35/2.50  tff(c_56, plain, (![A_139, C_149]: (~r3_waybel_9(A_139, '#skF_6'(A_139), C_149) | ~m1_subset_1(C_149, u1_struct_0(A_139)) | v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.35/2.50  tff(c_1149, plain, (![A_482, B_483]: (~m1_subset_1('#skF_2'(A_482, B_483, k1_xboole_0), u1_struct_0(A_482)) | v1_compts_1(A_482) | ~m2_yellow_6(B_483, A_482, '#skF_6'(A_482)) | ~l1_waybel_0('#skF_6'(A_482), A_482) | ~v7_waybel_0('#skF_6'(A_482)) | ~v4_orders_2('#skF_6'(A_482)) | v2_struct_0('#skF_6'(A_482)) | k10_yellow_6(A_482, B_483)=k1_xboole_0 | ~l1_waybel_0(B_483, A_482) | ~v7_waybel_0(B_483) | ~v4_orders_2(B_483) | v2_struct_0(B_483) | ~l1_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(resolution, [status(thm)], [c_1122, c_56])).
% 7.35/2.50  tff(c_1161, plain, (![A_10, B_54]: (v1_compts_1(A_10) | ~m2_yellow_6(B_54, A_10, '#skF_6'(A_10)) | ~l1_waybel_0('#skF_6'(A_10), A_10) | ~v7_waybel_0('#skF_6'(A_10)) | ~v4_orders_2('#skF_6'(A_10)) | v2_struct_0('#skF_6'(A_10)) | k10_yellow_6(A_10, B_54)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_waybel_0(B_54, A_10) | ~v7_waybel_0(B_54) | ~v4_orders_2(B_54) | v2_struct_0(B_54) | ~l1_pre_topc(A_10) | ~v2_pre_topc(A_10) | v2_struct_0(A_10))), inference(resolution, [status(thm)], [c_14, c_1149])).
% 7.35/2.50  tff(c_1171, plain, (![A_484, B_485]: (v1_compts_1(A_484) | ~m2_yellow_6(B_485, A_484, '#skF_6'(A_484)) | ~l1_waybel_0('#skF_6'(A_484), A_484) | ~v7_waybel_0('#skF_6'(A_484)) | ~v4_orders_2('#skF_6'(A_484)) | v2_struct_0('#skF_6'(A_484)) | k10_yellow_6(A_484, B_485)=k1_xboole_0 | ~l1_waybel_0(B_485, A_484) | ~v7_waybel_0(B_485) | ~v4_orders_2(B_485) | v2_struct_0(B_485) | ~l1_pre_topc(A_484) | ~v2_pre_topc(A_484) | v2_struct_0(A_484))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1161])).
% 7.35/2.50  tff(c_1179, plain, (v1_compts_1('#skF_7') | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_145, c_1171])).
% 7.35/2.50  tff(c_1183, plain, (v1_compts_1('#skF_7') | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1179])).
% 7.35/2.50  tff(c_1184, plain, (k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1183])).
% 7.35/2.50  tff(c_1235, plain, (~v4_orders_2('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_1184])).
% 7.35/2.50  tff(c_1238, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_62, c_1235])).
% 7.35/2.50  tff(c_1241, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1238])).
% 7.35/2.50  tff(c_1243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1241])).
% 7.35/2.50  tff(c_1245, plain, (v4_orders_2('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1184])).
% 7.35/2.50  tff(c_60, plain, (![A_139]: (v7_waybel_0('#skF_6'(A_139)) | v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.35/2.50  tff(c_58, plain, (![A_139]: (l1_waybel_0('#skF_6'(A_139), A_139) | v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.35/2.50  tff(c_12, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.35/2.50  tff(c_149, plain, (![C_185, A_186, B_187]: (v7_waybel_0(C_185) | ~m2_yellow_6(C_185, A_186, B_187) | ~l1_waybel_0(B_187, A_186) | ~v7_waybel_0(B_187) | ~v4_orders_2(B_187) | v2_struct_0(B_187) | ~l1_struct_0(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.35/2.50  tff(c_152, plain, (![B_158]: (v7_waybel_0('#skF_9'(B_158)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(resolution, [status(thm)], [c_145, c_149])).
% 7.35/2.50  tff(c_155, plain, (![B_158]: (v7_waybel_0('#skF_9'(B_158)) | ~l1_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(negUnitSimplification, [status(thm)], [c_74, c_152])).
% 7.35/2.50  tff(c_156, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_155])).
% 7.35/2.50  tff(c_159, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_12, c_156])).
% 7.35/2.50  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_159])).
% 7.35/2.50  tff(c_165, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_155])).
% 7.35/2.50  tff(c_184, plain, (![C_196, A_197, B_198]: (l1_waybel_0(C_196, A_197) | ~m2_yellow_6(C_196, A_197, B_198) | ~l1_waybel_0(B_198, A_197) | ~v7_waybel_0(B_198) | ~v4_orders_2(B_198) | v2_struct_0(B_198) | ~l1_struct_0(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.35/2.50  tff(c_187, plain, (![B_158]: (l1_waybel_0('#skF_9'(B_158), '#skF_7') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(resolution, [status(thm)], [c_145, c_184])).
% 7.35/2.50  tff(c_190, plain, (![B_158]: (l1_waybel_0('#skF_9'(B_158), '#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_187])).
% 7.35/2.50  tff(c_191, plain, (![B_158]: (l1_waybel_0('#skF_9'(B_158), '#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(negUnitSimplification, [status(thm)], [c_74, c_190])).
% 7.35/2.50  tff(c_1244, plain, (~v7_waybel_0('#skF_6'('#skF_7')) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | v2_struct_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1184])).
% 7.35/2.50  tff(c_1246, plain, (~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7')), inference(splitLeft, [status(thm)], [c_1244])).
% 7.35/2.50  tff(c_1249, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_191, c_1246])).
% 7.35/2.50  tff(c_1252, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_1249])).
% 7.35/2.50  tff(c_1253, plain, (~v7_waybel_0('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_1252])).
% 7.35/2.50  tff(c_1256, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_1253])).
% 7.35/2.50  tff(c_1259, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1256])).
% 7.35/2.50  tff(c_1261, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1259])).
% 7.35/2.50  tff(c_1262, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1252])).
% 7.35/2.50  tff(c_1264, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1262])).
% 7.35/2.50  tff(c_1298, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_58, c_1264])).
% 7.35/2.50  tff(c_1301, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1298])).
% 7.35/2.50  tff(c_1303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1301])).
% 7.35/2.50  tff(c_1304, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1262])).
% 7.35/2.50  tff(c_64, plain, (![A_139]: (~v2_struct_0('#skF_6'(A_139)) | v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.35/2.50  tff(c_1308, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1304, c_64])).
% 7.35/2.50  tff(c_1311, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1308])).
% 7.35/2.50  tff(c_1313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1311])).
% 7.35/2.50  tff(c_1314, plain, (~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1244])).
% 7.35/2.50  tff(c_1316, plain, (~v7_waybel_0('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_1314])).
% 7.35/2.50  tff(c_1319, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_1316])).
% 7.35/2.50  tff(c_1322, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1319])).
% 7.35/2.50  tff(c_1324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1322])).
% 7.35/2.50  tff(c_1326, plain, (v7_waybel_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1314])).
% 7.35/2.50  tff(c_164, plain, (![B_158]: (v7_waybel_0('#skF_9'(B_158)) | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(splitRight, [status(thm)], [c_155])).
% 7.35/2.50  tff(c_1325, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1314])).
% 7.35/2.50  tff(c_1327, plain, (~v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))), inference(splitLeft, [status(thm)], [c_1325])).
% 7.35/2.50  tff(c_1330, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_164, c_1327])).
% 7.35/2.50  tff(c_1333, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_1326, c_1330])).
% 7.35/2.50  tff(c_1334, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1333])).
% 7.35/2.50  tff(c_1368, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_58, c_1334])).
% 7.35/2.50  tff(c_1371, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1368])).
% 7.35/2.50  tff(c_1373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1371])).
% 7.35/2.50  tff(c_1374, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1333])).
% 7.35/2.50  tff(c_1378, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1374, c_64])).
% 7.35/2.50  tff(c_1381, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1378])).
% 7.35/2.50  tff(c_1383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1381])).
% 7.35/2.50  tff(c_1384, plain, (~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1325])).
% 7.35/2.50  tff(c_1386, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_1384])).
% 7.35/2.50  tff(c_1389, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_58, c_1386])).
% 7.35/2.50  tff(c_1392, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1389])).
% 7.35/2.50  tff(c_1394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1392])).
% 7.35/2.50  tff(c_1396, plain, (l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_1384])).
% 7.35/2.50  tff(c_176, plain, (![C_193, A_194, B_195]: (v4_orders_2(C_193) | ~m2_yellow_6(C_193, A_194, B_195) | ~l1_waybel_0(B_195, A_194) | ~v7_waybel_0(B_195) | ~v4_orders_2(B_195) | v2_struct_0(B_195) | ~l1_struct_0(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.35/2.50  tff(c_179, plain, (![B_158]: (v4_orders_2('#skF_9'(B_158)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(resolution, [status(thm)], [c_145, c_176])).
% 7.35/2.50  tff(c_182, plain, (![B_158]: (v4_orders_2('#skF_9'(B_158)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_179])).
% 7.35/2.50  tff(c_183, plain, (![B_158]: (v4_orders_2('#skF_9'(B_158)) | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(negUnitSimplification, [status(thm)], [c_74, c_182])).
% 7.35/2.50  tff(c_1395, plain, (~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1384])).
% 7.35/2.50  tff(c_1397, plain, (~v4_orders_2('#skF_9'('#skF_6'('#skF_7')))), inference(splitLeft, [status(thm)], [c_1395])).
% 7.35/2.50  tff(c_1400, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_183, c_1397])).
% 7.35/2.50  tff(c_1403, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_1326, c_1396, c_1400])).
% 7.35/2.50  tff(c_1406, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1403, c_64])).
% 7.35/2.50  tff(c_1409, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1406])).
% 7.35/2.50  tff(c_1411, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1409])).
% 7.35/2.50  tff(c_1412, plain, (k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1395])).
% 7.35/2.50  tff(c_1445, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_1412])).
% 7.35/2.50  tff(c_1448, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_1445, c_64])).
% 7.35/2.50  tff(c_1451, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1448])).
% 7.35/2.50  tff(c_1453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_111, c_1451])).
% 7.35/2.50  tff(c_1455, plain, (~v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_1412])).
% 7.35/2.50  tff(c_1454, plain, (v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1412])).
% 7.35/2.50  tff(c_1456, plain, (k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1454])).
% 7.35/2.50  tff(c_98, plain, (![B_158]: (v1_compts_1('#skF_7') | v3_yellow_6('#skF_9'(B_158), '#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_142, plain, (![B_158]: (v3_yellow_6('#skF_9'(B_158), '#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(negUnitSimplification, [status(thm)], [c_111, c_98])).
% 7.35/2.50  tff(c_194, plain, (![A_201, B_202]: (k10_yellow_6(A_201, B_202)!=k1_xboole_0 | ~v3_yellow_6(B_202, A_201) | ~l1_waybel_0(B_202, A_201) | ~v7_waybel_0(B_202) | ~v4_orders_2(B_202) | v2_struct_0(B_202) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.35/2.50  tff(c_197, plain, (![B_158]: (k10_yellow_6('#skF_7', '#skF_9'(B_158))!=k1_xboole_0 | ~l1_waybel_0('#skF_9'(B_158), '#skF_7') | ~v7_waybel_0('#skF_9'(B_158)) | ~v4_orders_2('#skF_9'(B_158)) | v2_struct_0('#skF_9'(B_158)) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(resolution, [status(thm)], [c_142, c_194])).
% 7.35/2.50  tff(c_200, plain, (![B_158]: (k10_yellow_6('#skF_7', '#skF_9'(B_158))!=k1_xboole_0 | ~l1_waybel_0('#skF_9'(B_158), '#skF_7') | ~v7_waybel_0('#skF_9'(B_158)) | ~v4_orders_2('#skF_9'(B_158)) | v2_struct_0('#skF_9'(B_158)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_197])).
% 7.35/2.50  tff(c_225, plain, (![B_219]: (k10_yellow_6('#skF_7', '#skF_9'(B_219))!=k1_xboole_0 | ~l1_waybel_0('#skF_9'(B_219), '#skF_7') | ~v7_waybel_0('#skF_9'(B_219)) | ~v4_orders_2('#skF_9'(B_219)) | v2_struct_0('#skF_9'(B_219)) | ~l1_waybel_0(B_219, '#skF_7') | ~v7_waybel_0(B_219) | ~v4_orders_2(B_219) | v2_struct_0(B_219))), inference(negUnitSimplification, [status(thm)], [c_74, c_200])).
% 7.35/2.50  tff(c_230, plain, (![B_220]: (k10_yellow_6('#skF_7', '#skF_9'(B_220))!=k1_xboole_0 | ~v7_waybel_0('#skF_9'(B_220)) | ~v4_orders_2('#skF_9'(B_220)) | v2_struct_0('#skF_9'(B_220)) | ~l1_waybel_0(B_220, '#skF_7') | ~v7_waybel_0(B_220) | ~v4_orders_2(B_220) | v2_struct_0(B_220))), inference(resolution, [status(thm)], [c_191, c_225])).
% 7.35/2.50  tff(c_235, plain, (![B_221]: (k10_yellow_6('#skF_7', '#skF_9'(B_221))!=k1_xboole_0 | ~v4_orders_2('#skF_9'(B_221)) | v2_struct_0('#skF_9'(B_221)) | ~l1_waybel_0(B_221, '#skF_7') | ~v7_waybel_0(B_221) | ~v4_orders_2(B_221) | v2_struct_0(B_221))), inference(resolution, [status(thm)], [c_164, c_230])).
% 7.35/2.50  tff(c_240, plain, (![B_222]: (k10_yellow_6('#skF_7', '#skF_9'(B_222))!=k1_xboole_0 | v2_struct_0('#skF_9'(B_222)) | ~l1_waybel_0(B_222, '#skF_7') | ~v7_waybel_0(B_222) | ~v4_orders_2(B_222) | v2_struct_0(B_222))), inference(resolution, [status(thm)], [c_183, c_235])).
% 7.35/2.50  tff(c_167, plain, (![C_189, A_190, B_191]: (~v2_struct_0(C_189) | ~m2_yellow_6(C_189, A_190, B_191) | ~l1_waybel_0(B_191, A_190) | ~v7_waybel_0(B_191) | ~v4_orders_2(B_191) | v2_struct_0(B_191) | ~l1_struct_0(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.35/2.50  tff(c_170, plain, (![B_158]: (~v2_struct_0('#skF_9'(B_158)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(resolution, [status(thm)], [c_145, c_167])).
% 7.35/2.50  tff(c_173, plain, (![B_158]: (~v2_struct_0('#skF_9'(B_158)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_170])).
% 7.35/2.50  tff(c_174, plain, (![B_158]: (~v2_struct_0('#skF_9'(B_158)) | ~l1_waybel_0(B_158, '#skF_7') | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158))), inference(negUnitSimplification, [status(thm)], [c_74, c_173])).
% 7.35/2.50  tff(c_244, plain, (![B_222]: (k10_yellow_6('#skF_7', '#skF_9'(B_222))!=k1_xboole_0 | ~l1_waybel_0(B_222, '#skF_7') | ~v7_waybel_0(B_222) | ~v4_orders_2(B_222) | v2_struct_0(B_222))), inference(resolution, [status(thm)], [c_240, c_174])).
% 7.35/2.50  tff(c_1505, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1456, c_244])).
% 7.35/2.50  tff(c_1573, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_1326, c_1396, c_1505])).
% 7.35/2.50  tff(c_1575, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1455, c_1573])).
% 7.35/2.50  tff(c_1576, plain, (v2_struct_0('#skF_9'('#skF_6'('#skF_7')))), inference(splitRight, [status(thm)], [c_1454])).
% 7.35/2.50  tff(c_1580, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_1576, c_174])).
% 7.35/2.50  tff(c_1583, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_1326, c_1396, c_1580])).
% 7.35/2.50  tff(c_1585, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1455, c_1583])).
% 7.35/2.50  tff(c_1586, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_84])).
% 7.35/2.50  tff(c_1587, plain, (v1_compts_1('#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 7.35/2.50  tff(c_82, plain, (v4_orders_2('#skF_8') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_1589, plain, (v4_orders_2('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_82])).
% 7.35/2.50  tff(c_80, plain, (v7_waybel_0('#skF_8') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_1591, plain, (v7_waybel_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_80])).
% 7.35/2.50  tff(c_78, plain, (l1_waybel_0('#skF_8', '#skF_7') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_1595, plain, (l1_waybel_0('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_78])).
% 7.35/2.50  tff(c_66, plain, (![A_139, B_146]: (r3_waybel_9(A_139, B_146, '#skF_5'(A_139, B_146)) | ~l1_waybel_0(B_146, A_139) | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.35/2.50  tff(c_68, plain, (![A_139, B_146]: (m1_subset_1('#skF_5'(A_139, B_146), u1_struct_0(A_139)) | ~l1_waybel_0(B_146, A_139) | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_248])).
% 7.35/2.50  tff(c_1598, plain, (![A_512, B_513]: (r1_tarski(A_512, B_513) | ~m1_subset_1(A_512, k1_zfmisc_1(B_513)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.35/2.50  tff(c_1606, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_2, c_1598])).
% 7.35/2.50  tff(c_1661, plain, (![A_560, B_561, C_562]: (m2_yellow_6('#skF_4'(A_560, B_561, C_562), A_560, B_561) | ~r3_waybel_9(A_560, B_561, C_562) | ~m1_subset_1(C_562, u1_struct_0(A_560)) | ~l1_waybel_0(B_561, A_560) | ~v7_waybel_0(B_561) | ~v4_orders_2(B_561) | v2_struct_0(B_561) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(cnfTransformation, [status(thm)], [f_224])).
% 7.35/2.50  tff(c_36, plain, (![C_99, A_96, B_97]: (l1_waybel_0(C_99, A_96) | ~m2_yellow_6(C_99, A_96, B_97) | ~l1_waybel_0(B_97, A_96) | ~v7_waybel_0(B_97) | ~v4_orders_2(B_97) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.35/2.50  tff(c_1753, plain, (![A_587, B_588, C_589]: (l1_waybel_0('#skF_4'(A_587, B_588, C_589), A_587) | ~l1_struct_0(A_587) | ~r3_waybel_9(A_587, B_588, C_589) | ~m1_subset_1(C_589, u1_struct_0(A_587)) | ~l1_waybel_0(B_588, A_587) | ~v7_waybel_0(B_588) | ~v4_orders_2(B_588) | v2_struct_0(B_588) | ~l1_pre_topc(A_587) | ~v2_pre_topc(A_587) | v2_struct_0(A_587))), inference(resolution, [status(thm)], [c_1661, c_36])).
% 7.35/2.50  tff(c_1811, plain, (![A_636, B_637, B_638]: (l1_waybel_0('#skF_4'(A_636, B_637, '#skF_5'(A_636, B_638)), A_636) | ~l1_struct_0(A_636) | ~r3_waybel_9(A_636, B_637, '#skF_5'(A_636, B_638)) | ~l1_waybel_0(B_637, A_636) | ~v7_waybel_0(B_637) | ~v4_orders_2(B_637) | v2_struct_0(B_637) | ~l1_waybel_0(B_638, A_636) | ~v7_waybel_0(B_638) | ~v4_orders_2(B_638) | v2_struct_0(B_638) | ~v1_compts_1(A_636) | ~l1_pre_topc(A_636) | ~v2_pre_topc(A_636) | v2_struct_0(A_636))), inference(resolution, [status(thm)], [c_68, c_1753])).
% 7.35/2.50  tff(c_44, plain, (![B_102, A_100]: (v3_yellow_6(B_102, A_100) | k10_yellow_6(A_100, B_102)=k1_xboole_0 | ~l1_waybel_0(B_102, A_100) | ~v7_waybel_0(B_102) | ~v4_orders_2(B_102) | v2_struct_0(B_102) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.35/2.50  tff(c_76, plain, (![C_157]: (~v3_yellow_6(C_157, '#skF_7') | ~m2_yellow_6(C_157, '#skF_7', '#skF_8') | ~v1_compts_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_273])).
% 7.35/2.50  tff(c_1609, plain, (![C_157]: (~v3_yellow_6(C_157, '#skF_7') | ~m2_yellow_6(C_157, '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1587, c_76])).
% 7.35/2.50  tff(c_1677, plain, (![C_562]: (~v3_yellow_6('#skF_4'('#skF_7', '#skF_8', C_562), '#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', C_562) | ~m1_subset_1(C_562, u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1661, c_1609])).
% 7.35/2.50  tff(c_1684, plain, (![C_562]: (~v3_yellow_6('#skF_4'('#skF_7', '#skF_8', C_562), '#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', C_562) | ~m1_subset_1(C_562, u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1589, c_1591, c_1595, c_1677])).
% 7.35/2.50  tff(c_1686, plain, (![C_563]: (~v3_yellow_6('#skF_4'('#skF_7', '#skF_8', C_563), '#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', C_563) | ~m1_subset_1(C_563, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_74, c_1586, c_1684])).
% 7.35/2.50  tff(c_1689, plain, (![C_563]: (~r3_waybel_9('#skF_7', '#skF_8', C_563) | ~m1_subset_1(C_563, u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', C_563))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', C_563), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', C_563)) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', C_563)) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', C_563)) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_44, c_1686])).
% 7.35/2.50  tff(c_1692, plain, (![C_563]: (~r3_waybel_9('#skF_7', '#skF_8', C_563) | ~m1_subset_1(C_563, u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', C_563))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', C_563), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', C_563)) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', C_563)) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', C_563)) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1689])).
% 7.35/2.50  tff(c_1694, plain, (![C_564]: (~r3_waybel_9('#skF_7', '#skF_8', C_564) | ~m1_subset_1(C_564, u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', C_564))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', C_564), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', C_564)) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', C_564)) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', C_564)))), inference(negUnitSimplification, [status(thm)], [c_74, c_1692])).
% 7.35/2.50  tff(c_1698, plain, (![B_146]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_1694])).
% 7.35/2.50  tff(c_1701, plain, (![B_146]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1587, c_1698])).
% 7.35/2.50  tff(c_1702, plain, (![B_146]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146))), inference(negUnitSimplification, [status(thm)], [c_74, c_1701])).
% 7.35/2.50  tff(c_1815, plain, (![B_638]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638)) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_638, '#skF_7') | ~v7_waybel_0(B_638) | ~v4_orders_2(B_638) | v2_struct_0(B_638) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1811, c_1702])).
% 7.35/2.50  tff(c_1818, plain, (![B_638]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_638, '#skF_7') | ~v7_waybel_0(B_638) | ~v4_orders_2(B_638) | v2_struct_0(B_638) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1587, c_1589, c_1591, c_1595, c_1815])).
% 7.35/2.50  tff(c_1819, plain, (![B_638]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_638)) | ~l1_waybel_0(B_638, '#skF_7') | ~v7_waybel_0(B_638) | ~v4_orders_2(B_638) | v2_struct_0(B_638))), inference(negUnitSimplification, [status(thm)], [c_74, c_1586, c_1818])).
% 7.35/2.50  tff(c_1828, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1819])).
% 7.35/2.50  tff(c_1831, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_12, c_1828])).
% 7.35/2.50  tff(c_1835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1831])).
% 7.35/2.50  tff(c_1837, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_1819])).
% 7.35/2.50  tff(c_40, plain, (![C_99, A_96, B_97]: (v4_orders_2(C_99) | ~m2_yellow_6(C_99, A_96, B_97) | ~l1_waybel_0(B_97, A_96) | ~v7_waybel_0(B_97) | ~v4_orders_2(B_97) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.35/2.50  tff(c_1703, plain, (![A_565, B_566, C_567]: (v4_orders_2('#skF_4'(A_565, B_566, C_567)) | ~l1_struct_0(A_565) | ~r3_waybel_9(A_565, B_566, C_567) | ~m1_subset_1(C_567, u1_struct_0(A_565)) | ~l1_waybel_0(B_566, A_565) | ~v7_waybel_0(B_566) | ~v4_orders_2(B_566) | v2_struct_0(B_566) | ~l1_pre_topc(A_565) | ~v2_pre_topc(A_565) | v2_struct_0(A_565))), inference(resolution, [status(thm)], [c_1661, c_40])).
% 7.35/2.50  tff(c_1706, plain, (![A_139, B_566, B_146]: (v4_orders_2('#skF_4'(A_139, B_566, '#skF_5'(A_139, B_146))) | ~l1_struct_0(A_139) | ~r3_waybel_9(A_139, B_566, '#skF_5'(A_139, B_146)) | ~l1_waybel_0(B_566, A_139) | ~v7_waybel_0(B_566) | ~v4_orders_2(B_566) | v2_struct_0(B_566) | ~l1_waybel_0(B_146, A_139) | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_68, c_1703])).
% 7.35/2.50  tff(c_38, plain, (![C_99, A_96, B_97]: (v7_waybel_0(C_99) | ~m2_yellow_6(C_99, A_96, B_97) | ~l1_waybel_0(B_97, A_96) | ~v7_waybel_0(B_97) | ~v4_orders_2(B_97) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.35/2.50  tff(c_1708, plain, (![A_571, B_572, C_573]: (v7_waybel_0('#skF_4'(A_571, B_572, C_573)) | ~l1_struct_0(A_571) | ~r3_waybel_9(A_571, B_572, C_573) | ~m1_subset_1(C_573, u1_struct_0(A_571)) | ~l1_waybel_0(B_572, A_571) | ~v7_waybel_0(B_572) | ~v4_orders_2(B_572) | v2_struct_0(B_572) | ~l1_pre_topc(A_571) | ~v2_pre_topc(A_571) | v2_struct_0(A_571))), inference(resolution, [status(thm)], [c_1661, c_38])).
% 7.35/2.50  tff(c_1711, plain, (![A_139, B_572, B_146]: (v7_waybel_0('#skF_4'(A_139, B_572, '#skF_5'(A_139, B_146))) | ~l1_struct_0(A_139) | ~r3_waybel_9(A_139, B_572, '#skF_5'(A_139, B_146)) | ~l1_waybel_0(B_572, A_139) | ~v7_waybel_0(B_572) | ~v4_orders_2(B_572) | v2_struct_0(B_572) | ~l1_waybel_0(B_146, A_139) | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~v1_compts_1(A_139) | ~l1_pre_topc(A_139) | ~v2_pre_topc(A_139) | v2_struct_0(A_139))), inference(resolution, [status(thm)], [c_68, c_1708])).
% 7.35/2.50  tff(c_1838, plain, (![B_643]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_643)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_643))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_643))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_643))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_643)) | ~l1_waybel_0(B_643, '#skF_7') | ~v7_waybel_0(B_643) | ~v4_orders_2(B_643) | v2_struct_0(B_643))), inference(splitRight, [status(thm)], [c_1819])).
% 7.35/2.50  tff(c_1842, plain, (![B_146]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1711, c_1838])).
% 7.35/2.50  tff(c_1845, plain, (![B_146]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1587, c_1589, c_1591, c_1595, c_1837, c_1842])).
% 7.35/2.50  tff(c_1847, plain, (![B_644]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_644)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_644))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_644))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_644)) | ~l1_waybel_0(B_644, '#skF_7') | ~v7_waybel_0(B_644) | ~v4_orders_2(B_644) | v2_struct_0(B_644))), inference(negUnitSimplification, [status(thm)], [c_74, c_1586, c_1845])).
% 7.35/2.50  tff(c_1851, plain, (![B_146]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1706, c_1847])).
% 7.35/2.50  tff(c_1854, plain, (![B_146]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1587, c_1589, c_1591, c_1595, c_1837, c_1851])).
% 7.35/2.50  tff(c_1856, plain, (![B_645]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_645)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_645))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_645)) | ~l1_waybel_0(B_645, '#skF_7') | ~v7_waybel_0(B_645) | ~v4_orders_2(B_645) | v2_struct_0(B_645))), inference(negUnitSimplification, [status(thm)], [c_74, c_1586, c_1854])).
% 7.35/2.50  tff(c_42, plain, (![C_99, A_96, B_97]: (~v2_struct_0(C_99) | ~m2_yellow_6(C_99, A_96, B_97) | ~l1_waybel_0(B_97, A_96) | ~v7_waybel_0(B_97) | ~v4_orders_2(B_97) | v2_struct_0(B_97) | ~l1_struct_0(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.35/2.50  tff(c_1681, plain, (![A_560, B_561, C_562]: (~v2_struct_0('#skF_4'(A_560, B_561, C_562)) | ~l1_struct_0(A_560) | ~r3_waybel_9(A_560, B_561, C_562) | ~m1_subset_1(C_562, u1_struct_0(A_560)) | ~l1_waybel_0(B_561, A_560) | ~v7_waybel_0(B_561) | ~v4_orders_2(B_561) | v2_struct_0(B_561) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(resolution, [status(thm)], [c_1661, c_42])).
% 7.35/2.50  tff(c_1858, plain, (![B_645]: (~l1_struct_0('#skF_7') | ~m1_subset_1('#skF_5'('#skF_7', B_645), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_645)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_645)) | ~l1_waybel_0(B_645, '#skF_7') | ~v7_waybel_0(B_645) | ~v4_orders_2(B_645) | v2_struct_0(B_645))), inference(resolution, [status(thm)], [c_1856, c_1681])).
% 7.35/2.50  tff(c_1861, plain, (![B_645]: (~m1_subset_1('#skF_5'('#skF_7', B_645), u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7') | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_645)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_645)) | ~l1_waybel_0(B_645, '#skF_7') | ~v7_waybel_0(B_645) | ~v4_orders_2(B_645) | v2_struct_0(B_645))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1589, c_1591, c_1595, c_1837, c_1858])).
% 7.35/2.50  tff(c_1863, plain, (![B_646]: (~m1_subset_1('#skF_5'('#skF_7', B_646), u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_646)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_646)) | ~l1_waybel_0(B_646, '#skF_7') | ~v7_waybel_0(B_646) | ~v4_orders_2(B_646) | v2_struct_0(B_646))), inference(negUnitSimplification, [status(thm)], [c_74, c_1586, c_1861])).
% 7.35/2.50  tff(c_1867, plain, (![B_146]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_1863])).
% 7.35/2.50  tff(c_1870, plain, (![B_146]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1587, c_1867])).
% 7.35/2.50  tff(c_1872, plain, (![B_647]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_647)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_647)) | ~l1_waybel_0(B_647, '#skF_7') | ~v7_waybel_0(B_647) | ~v4_orders_2(B_647) | v2_struct_0(B_647))), inference(negUnitSimplification, [status(thm)], [c_74, c_1870])).
% 7.35/2.50  tff(c_1727, plain, (![C_577, A_578, B_579]: (r2_hidden(C_577, k10_yellow_6(A_578, '#skF_4'(A_578, B_579, C_577))) | ~r3_waybel_9(A_578, B_579, C_577) | ~m1_subset_1(C_577, u1_struct_0(A_578)) | ~l1_waybel_0(B_579, A_578) | ~v7_waybel_0(B_579) | ~v4_orders_2(B_579) | v2_struct_0(B_579) | ~l1_pre_topc(A_578) | ~v2_pre_topc(A_578) | v2_struct_0(A_578))), inference(cnfTransformation, [status(thm)], [f_224])).
% 7.35/2.50  tff(c_1742, plain, (![A_578, B_579, C_577]: (~r1_tarski(k10_yellow_6(A_578, '#skF_4'(A_578, B_579, C_577)), C_577) | ~r3_waybel_9(A_578, B_579, C_577) | ~m1_subset_1(C_577, u1_struct_0(A_578)) | ~l1_waybel_0(B_579, A_578) | ~v7_waybel_0(B_579) | ~v4_orders_2(B_579) | v2_struct_0(B_579) | ~l1_pre_topc(A_578) | ~v2_pre_topc(A_578) | v2_struct_0(A_578))), inference(resolution, [status(thm)], [c_1727, c_10])).
% 7.35/2.50  tff(c_1886, plain, (![B_647]: (~r1_tarski(k1_xboole_0, '#skF_5'('#skF_7', B_647)) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_647)) | ~m1_subset_1('#skF_5'('#skF_7', B_647), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_647)) | ~l1_waybel_0(B_647, '#skF_7') | ~v7_waybel_0(B_647) | ~v4_orders_2(B_647) | v2_struct_0(B_647))), inference(superposition, [status(thm), theory('equality')], [c_1872, c_1742])).
% 7.35/2.50  tff(c_1916, plain, (![B_647]: (~m1_subset_1('#skF_5'('#skF_7', B_647), u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_647)) | ~l1_waybel_0(B_647, '#skF_7') | ~v7_waybel_0(B_647) | ~v4_orders_2(B_647) | v2_struct_0(B_647))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1589, c_1591, c_1595, c_1606, c_1886])).
% 7.35/2.50  tff(c_1934, plain, (![B_648]: (~m1_subset_1('#skF_5'('#skF_7', B_648), u1_struct_0('#skF_7')) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_648)) | ~l1_waybel_0(B_648, '#skF_7') | ~v7_waybel_0(B_648) | ~v4_orders_2(B_648) | v2_struct_0(B_648))), inference(negUnitSimplification, [status(thm)], [c_74, c_1586, c_1916])).
% 7.35/2.50  tff(c_1938, plain, (![B_146]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_68, c_1934])).
% 7.35/2.50  tff(c_1941, plain, (![B_146]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_146)) | ~l1_waybel_0(B_146, '#skF_7') | ~v7_waybel_0(B_146) | ~v4_orders_2(B_146) | v2_struct_0(B_146) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1587, c_1938])).
% 7.35/2.50  tff(c_1947, plain, (![B_652]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_652)) | ~l1_waybel_0(B_652, '#skF_7') | ~v7_waybel_0(B_652) | ~v4_orders_2(B_652) | v2_struct_0(B_652))), inference(negUnitSimplification, [status(thm)], [c_74, c_1941])).
% 7.35/2.50  tff(c_1955, plain, (~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_66, c_1947])).
% 7.35/2.50  tff(c_1962, plain, (v2_struct_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1587, c_1589, c_1591, c_1595, c_1955])).
% 7.35/2.50  tff(c_1964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_1586, c_1962])).
% 7.35/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.35/2.50  
% 7.35/2.50  Inference rules
% 7.35/2.50  ----------------------
% 7.35/2.50  #Ref     : 0
% 7.35/2.50  #Sup     : 360
% 7.35/2.50  #Fact    : 2
% 7.35/2.50  #Define  : 0
% 7.35/2.50  #Split   : 17
% 7.35/2.50  #Chain   : 0
% 7.35/2.50  #Close   : 0
% 7.35/2.50  
% 7.35/2.50  Ordering : KBO
% 7.35/2.50  
% 7.35/2.50  Simplification rules
% 7.35/2.50  ----------------------
% 7.35/2.50  #Subsume      : 84
% 7.35/2.50  #Demod        : 300
% 7.35/2.50  #Tautology    : 49
% 7.35/2.50  #SimpNegUnit  : 59
% 7.35/2.50  #BackRed      : 0
% 7.35/2.50  
% 7.35/2.50  #Partial instantiations: 0
% 7.35/2.50  #Strategies tried      : 1
% 7.35/2.50  
% 7.35/2.50  Timing (in seconds)
% 7.35/2.50  ----------------------
% 7.42/2.50  Preprocessing        : 0.47
% 7.42/2.50  Parsing              : 0.24
% 7.42/2.50  CNF conversion       : 0.04
% 7.42/2.50  Main loop            : 1.09
% 7.42/2.50  Inferencing          : 0.43
% 7.42/2.50  Reduction            : 0.26
% 7.42/2.50  Demodulation         : 0.16
% 7.42/2.50  BG Simplification    : 0.06
% 7.42/2.50  Subsumption          : 0.29
% 7.42/2.50  Abstraction          : 0.05
% 7.42/2.50  MUC search           : 0.00
% 7.42/2.50  Cooper               : 0.00
% 7.42/2.50  Total                : 1.64
% 7.42/2.50  Index Insertion      : 0.00
% 7.42/2.50  Index Deletion       : 0.00
% 7.42/2.50  Index Matching       : 0.00
% 7.42/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
