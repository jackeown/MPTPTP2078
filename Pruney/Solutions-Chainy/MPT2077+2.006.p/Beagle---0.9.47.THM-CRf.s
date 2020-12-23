%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:40 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.67s
% Verified   : 
% Statistics : Number of formulae       :  255 (3360 expanded)
%              Number of leaves         :   46 (1102 expanded)
%              Depth                    :   37
%              Number of atoms          : 1236 (23068 expanded)
%              Number of equality atoms :   36 (  81 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > m2_yellow_6 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k6_yellow_6 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_8 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k6_yellow_6,type,(
    k6_yellow_6: $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_287,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow19)).

tff(f_262,axiom,(
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
           => ~ ( r2_hidden(B,k6_yellow_6(A))
                & ! [C] :
                    ( m1_subset_1(C,u1_struct_0(A))
                   => ~ r3_waybel_9(A,B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_yellow19)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k10_yellow_6(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_154,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_waybel_9)).

tff(f_181,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_9)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_yellow_6)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_130,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_yellow_6)).

tff(f_234,axiom,(
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

tff(f_210,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_9)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_80,plain,
    ( ~ v2_struct_0('#skF_7')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_110,plain,(
    ~ v1_compts_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_68,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_66,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_58,plain,(
    ! [A_69] :
      ( v4_orders_2('#skF_5'(A_69))
      | v1_compts_1(A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_106,plain,(
    ! [B_88] :
      ( v1_compts_1('#skF_6')
      | m2_yellow_6('#skF_8'(B_88),'#skF_6',B_88)
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_154,plain,(
    ! [B_88] :
      ( m2_yellow_6('#skF_8'(B_88),'#skF_6',B_88)
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_106])).

tff(c_14,plain,(
    ! [A_5,B_6,C_10] :
      ( r2_hidden('#skF_1'(A_5,B_6,C_10),B_6)
      | r1_tarski(B_6,C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_234,plain,(
    ! [A_144,B_145] :
      ( m1_subset_1(k10_yellow_6(A_144,B_145),k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_waybel_0(B_145,A_144)
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_263,plain,(
    ! [A_156,A_157,B_158] :
      ( m1_subset_1(A_156,u1_struct_0(A_157))
      | ~ r2_hidden(A_156,k10_yellow_6(A_157,B_158))
      | ~ l1_waybel_0(B_158,A_157)
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(resolution,[status(thm)],[c_234,c_18])).

tff(c_268,plain,(
    ! [A_5,A_157,B_158,C_10] :
      ( m1_subset_1('#skF_1'(A_5,k10_yellow_6(A_157,B_158),C_10),u1_struct_0(A_157))
      | ~ l1_waybel_0(B_158,A_157)
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157)
      | r1_tarski(k10_yellow_6(A_157,B_158),C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(k10_yellow_6(A_157,B_158),k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_14,c_263])).

tff(c_297,plain,(
    ! [A_168,B_169,C_170] :
      ( r3_waybel_9(A_168,B_169,C_170)
      | ~ r2_hidden(C_170,k10_yellow_6(A_168,B_169))
      | ~ m1_subset_1(C_170,u1_struct_0(A_168))
      | ~ l1_waybel_0(B_169,A_168)
      | ~ v7_waybel_0(B_169)
      | ~ v4_orders_2(B_169)
      | v2_struct_0(B_169)
      | ~ l1_pre_topc(A_168)
      | ~ v2_pre_topc(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_424,plain,(
    ! [A_229,B_230,A_231,C_232] :
      ( r3_waybel_9(A_229,B_230,'#skF_1'(A_231,k10_yellow_6(A_229,B_230),C_232))
      | ~ m1_subset_1('#skF_1'(A_231,k10_yellow_6(A_229,B_230),C_232),u1_struct_0(A_229))
      | ~ l1_waybel_0(B_230,A_229)
      | ~ v7_waybel_0(B_230)
      | ~ v4_orders_2(B_230)
      | v2_struct_0(B_230)
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229)
      | r1_tarski(k10_yellow_6(A_229,B_230),C_232)
      | ~ m1_subset_1(C_232,k1_zfmisc_1(A_231))
      | ~ m1_subset_1(k10_yellow_6(A_229,B_230),k1_zfmisc_1(A_231)) ) ),
    inference(resolution,[status(thm)],[c_14,c_297])).

tff(c_432,plain,(
    ! [A_233,B_234,A_235,C_236] :
      ( r3_waybel_9(A_233,B_234,'#skF_1'(A_235,k10_yellow_6(A_233,B_234),C_236))
      | ~ l1_waybel_0(B_234,A_233)
      | ~ v7_waybel_0(B_234)
      | ~ v4_orders_2(B_234)
      | v2_struct_0(B_234)
      | ~ l1_pre_topc(A_233)
      | ~ v2_pre_topc(A_233)
      | v2_struct_0(A_233)
      | r1_tarski(k10_yellow_6(A_233,B_234),C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(A_235))
      | ~ m1_subset_1(k10_yellow_6(A_233,B_234),k1_zfmisc_1(A_235)) ) ),
    inference(resolution,[status(thm)],[c_268,c_424])).

tff(c_40,plain,(
    ! [A_34,B_42,D_48,C_46] :
      ( r3_waybel_9(A_34,B_42,D_48)
      | ~ r3_waybel_9(A_34,C_46,D_48)
      | ~ m1_subset_1(D_48,u1_struct_0(A_34))
      | ~ m2_yellow_6(C_46,A_34,B_42)
      | ~ l1_waybel_0(B_42,A_34)
      | ~ v7_waybel_0(B_42)
      | ~ v4_orders_2(B_42)
      | v2_struct_0(B_42)
      | ~ l1_pre_topc(A_34)
      | ~ v2_pre_topc(A_34)
      | v2_struct_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_4198,plain,(
    ! [A_2393,C_2395,B_2396,B_2392,A_2394] :
      ( r3_waybel_9(A_2394,B_2396,'#skF_1'(A_2393,k10_yellow_6(A_2394,B_2392),C_2395))
      | ~ m1_subset_1('#skF_1'(A_2393,k10_yellow_6(A_2394,B_2392),C_2395),u1_struct_0(A_2394))
      | ~ m2_yellow_6(B_2392,A_2394,B_2396)
      | ~ l1_waybel_0(B_2396,A_2394)
      | ~ v7_waybel_0(B_2396)
      | ~ v4_orders_2(B_2396)
      | v2_struct_0(B_2396)
      | ~ l1_waybel_0(B_2392,A_2394)
      | ~ v7_waybel_0(B_2392)
      | ~ v4_orders_2(B_2392)
      | v2_struct_0(B_2392)
      | ~ l1_pre_topc(A_2394)
      | ~ v2_pre_topc(A_2394)
      | v2_struct_0(A_2394)
      | r1_tarski(k10_yellow_6(A_2394,B_2392),C_2395)
      | ~ m1_subset_1(C_2395,k1_zfmisc_1(A_2393))
      | ~ m1_subset_1(k10_yellow_6(A_2394,B_2392),k1_zfmisc_1(A_2393)) ) ),
    inference(resolution,[status(thm)],[c_432,c_40])).

tff(c_4337,plain,(
    ! [B_2436,A_2432,C_2435,B_2434,A_2433] :
      ( r3_waybel_9(A_2432,B_2436,'#skF_1'(A_2433,k10_yellow_6(A_2432,B_2434),C_2435))
      | ~ m2_yellow_6(B_2434,A_2432,B_2436)
      | ~ l1_waybel_0(B_2436,A_2432)
      | ~ v7_waybel_0(B_2436)
      | ~ v4_orders_2(B_2436)
      | v2_struct_0(B_2436)
      | ~ l1_waybel_0(B_2434,A_2432)
      | ~ v7_waybel_0(B_2434)
      | ~ v4_orders_2(B_2434)
      | v2_struct_0(B_2434)
      | ~ l1_pre_topc(A_2432)
      | ~ v2_pre_topc(A_2432)
      | v2_struct_0(A_2432)
      | r1_tarski(k10_yellow_6(A_2432,B_2434),C_2435)
      | ~ m1_subset_1(C_2435,k1_zfmisc_1(A_2433))
      | ~ m1_subset_1(k10_yellow_6(A_2432,B_2434),k1_zfmisc_1(A_2433)) ) ),
    inference(resolution,[status(thm)],[c_268,c_4198])).

tff(c_50,plain,(
    ! [A_69,C_79] :
      ( ~ r3_waybel_9(A_69,'#skF_5'(A_69),C_79)
      | ~ m1_subset_1(C_79,u1_struct_0(A_69))
      | v1_compts_1(A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_5628,plain,(
    ! [A_3085,A_3086,B_3087,C_3088] :
      ( ~ m1_subset_1('#skF_1'(A_3085,k10_yellow_6(A_3086,B_3087),C_3088),u1_struct_0(A_3086))
      | v1_compts_1(A_3086)
      | ~ m2_yellow_6(B_3087,A_3086,'#skF_5'(A_3086))
      | ~ l1_waybel_0('#skF_5'(A_3086),A_3086)
      | ~ v7_waybel_0('#skF_5'(A_3086))
      | ~ v4_orders_2('#skF_5'(A_3086))
      | v2_struct_0('#skF_5'(A_3086))
      | ~ l1_waybel_0(B_3087,A_3086)
      | ~ v7_waybel_0(B_3087)
      | ~ v4_orders_2(B_3087)
      | v2_struct_0(B_3087)
      | ~ l1_pre_topc(A_3086)
      | ~ v2_pre_topc(A_3086)
      | v2_struct_0(A_3086)
      | r1_tarski(k10_yellow_6(A_3086,B_3087),C_3088)
      | ~ m1_subset_1(C_3088,k1_zfmisc_1(A_3085))
      | ~ m1_subset_1(k10_yellow_6(A_3086,B_3087),k1_zfmisc_1(A_3085)) ) ),
    inference(resolution,[status(thm)],[c_4337,c_50])).

tff(c_5677,plain,(
    ! [A_3106,B_3107,C_3108,A_3109] :
      ( v1_compts_1(A_3106)
      | ~ m2_yellow_6(B_3107,A_3106,'#skF_5'(A_3106))
      | ~ l1_waybel_0('#skF_5'(A_3106),A_3106)
      | ~ v7_waybel_0('#skF_5'(A_3106))
      | ~ v4_orders_2('#skF_5'(A_3106))
      | v2_struct_0('#skF_5'(A_3106))
      | ~ l1_waybel_0(B_3107,A_3106)
      | ~ v7_waybel_0(B_3107)
      | ~ v4_orders_2(B_3107)
      | v2_struct_0(B_3107)
      | ~ l1_pre_topc(A_3106)
      | ~ v2_pre_topc(A_3106)
      | v2_struct_0(A_3106)
      | r1_tarski(k10_yellow_6(A_3106,B_3107),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6(A_3106,B_3107),k1_zfmisc_1(A_3109)) ) ),
    inference(resolution,[status(thm)],[c_268,c_5628])).

tff(c_5699,plain,(
    ! [C_3108,A_3109] :
      ( v1_compts_1('#skF_6')
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_5'('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_154,c_5677])).

tff(c_5703,plain,(
    ! [C_3108,A_3109] :
      ( v1_compts_1('#skF_6')
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_5'('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5699])).

tff(c_5704,plain,(
    ! [C_3108,A_3109] :
      ( ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_5'('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5703])).

tff(c_5705,plain,(
    ~ v4_orders_2('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5704])).

tff(c_5708,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_5705])).

tff(c_5711,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5708])).

tff(c_5713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5711])).

tff(c_5715,plain,(
    v4_orders_2('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5704])).

tff(c_56,plain,(
    ! [A_69] :
      ( v7_waybel_0('#skF_5'(A_69))
      | v1_compts_1(A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_54,plain,(
    ! [A_69] :
      ( l1_waybel_0('#skF_5'(A_69),A_69)
      | v1_compts_1(A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_22,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_188,plain,(
    ! [C_126,A_127,B_128] :
      ( ~ v2_struct_0(C_126)
      | ~ m2_yellow_6(C_126,A_127,B_128)
      | ~ l1_waybel_0(B_128,A_127)
      | ~ v7_waybel_0(B_128)
      | ~ v4_orders_2(B_128)
      | v2_struct_0(B_128)
      | ~ l1_struct_0(A_127)
      | v2_struct_0(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_191,plain,(
    ! [B_88] :
      ( ~ v2_struct_0('#skF_8'(B_88))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(resolution,[status(thm)],[c_154,c_188])).

tff(c_194,plain,(
    ! [B_88] :
      ( ~ v2_struct_0('#skF_8'(B_88))
      | ~ l1_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_191])).

tff(c_195,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_198,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_198])).

tff(c_204,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_224,plain,(
    ! [C_138,A_139,B_140] :
      ( l1_waybel_0(C_138,A_139)
      | ~ m2_yellow_6(C_138,A_139,B_140)
      | ~ l1_waybel_0(B_140,A_139)
      | ~ v7_waybel_0(B_140)
      | ~ v4_orders_2(B_140)
      | v2_struct_0(B_140)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_227,plain,(
    ! [B_88] :
      ( l1_waybel_0('#skF_8'(B_88),'#skF_6')
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(resolution,[status(thm)],[c_154,c_224])).

tff(c_230,plain,(
    ! [B_88] :
      ( l1_waybel_0('#skF_8'(B_88),'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_227])).

tff(c_231,plain,(
    ! [B_88] :
      ( l1_waybel_0('#skF_8'(B_88),'#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_230])).

tff(c_5714,plain,(
    ! [C_3108,A_3109] :
      ( ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | v2_struct_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109)) ) ),
    inference(splitRight,[status(thm)],[c_5704])).

tff(c_5716,plain,(
    ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5714])).

tff(c_5719,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_231,c_5716])).

tff(c_5722,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5715,c_5719])).

tff(c_5723,plain,(
    ~ v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5722])).

tff(c_5726,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_5723])).

tff(c_5729,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5726])).

tff(c_5731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5729])).

tff(c_5732,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5722])).

tff(c_5789,plain,(
    ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5732])).

tff(c_5792,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_5789])).

tff(c_5795,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5792])).

tff(c_5797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5795])).

tff(c_5798,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5732])).

tff(c_60,plain,(
    ! [A_69] :
      ( ~ v2_struct_0('#skF_5'(A_69))
      | v1_compts_1(A_69)
      | ~ l1_pre_topc(A_69)
      | ~ v2_pre_topc(A_69)
      | v2_struct_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_262])).

tff(c_5802,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_5798,c_60])).

tff(c_5805,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5802])).

tff(c_5807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5805])).

tff(c_5808,plain,(
    ! [C_3108,A_3109] :
      ( ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109)) ) ),
    inference(splitRight,[status(thm)],[c_5714])).

tff(c_5810,plain,(
    ~ v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5808])).

tff(c_5813,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_5810])).

tff(c_5816,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5813])).

tff(c_5818,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5816])).

tff(c_5820,plain,(
    v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5808])).

tff(c_215,plain,(
    ! [C_134,A_135,B_136] :
      ( v7_waybel_0(C_134)
      | ~ m2_yellow_6(C_134,A_135,B_136)
      | ~ l1_waybel_0(B_136,A_135)
      | ~ v7_waybel_0(B_136)
      | ~ v4_orders_2(B_136)
      | v2_struct_0(B_136)
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_218,plain,(
    ! [B_88] :
      ( v7_waybel_0('#skF_8'(B_88))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(resolution,[status(thm)],[c_154,c_215])).

tff(c_221,plain,(
    ! [B_88] :
      ( v7_waybel_0('#skF_8'(B_88))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_218])).

tff(c_222,plain,(
    ! [B_88] :
      ( v7_waybel_0('#skF_8'(B_88))
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_221])).

tff(c_5819,plain,(
    ! [C_3108,A_3109] :
      ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109)) ) ),
    inference(splitRight,[status(thm)],[c_5808])).

tff(c_5821,plain,(
    ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_5819])).

tff(c_5879,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_222,c_5821])).

tff(c_5882,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5715,c_5820,c_5879])).

tff(c_5883,plain,(
    ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5882])).

tff(c_5886,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_5883])).

tff(c_5889,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5886])).

tff(c_5891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5889])).

tff(c_5892,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5882])).

tff(c_5896,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_5892,c_60])).

tff(c_5899,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5896])).

tff(c_5901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5899])).

tff(c_5902,plain,(
    ! [C_3108,A_3109] :
      ( ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109)) ) ),
    inference(splitRight,[status(thm)],[c_5819])).

tff(c_5904,plain,(
    ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_5902])).

tff(c_5907,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_5904])).

tff(c_5910,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5907])).

tff(c_5912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5910])).

tff(c_5914,plain,(
    l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_5902])).

tff(c_206,plain,(
    ! [C_130,A_131,B_132] :
      ( v4_orders_2(C_130)
      | ~ m2_yellow_6(C_130,A_131,B_132)
      | ~ l1_waybel_0(B_132,A_131)
      | ~ v7_waybel_0(B_132)
      | ~ v4_orders_2(B_132)
      | v2_struct_0(B_132)
      | ~ l1_struct_0(A_131)
      | v2_struct_0(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_209,plain,(
    ! [B_88] :
      ( v4_orders_2('#skF_8'(B_88))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(resolution,[status(thm)],[c_154,c_206])).

tff(c_212,plain,(
    ! [B_88] :
      ( v4_orders_2('#skF_8'(B_88))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_209])).

tff(c_213,plain,(
    ! [B_88] :
      ( v4_orders_2('#skF_8'(B_88))
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_212])).

tff(c_5913,plain,(
    ! [C_3108,A_3109] :
      ( ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109)) ) ),
    inference(splitRight,[status(thm)],[c_5902])).

tff(c_5970,plain,(
    ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_5913])).

tff(c_5973,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_213,c_5970])).

tff(c_5976,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5715,c_5820,c_5914,c_5973])).

tff(c_5979,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_5976,c_60])).

tff(c_5982,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5979])).

tff(c_5984,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5982])).

tff(c_5985,plain,(
    ! [C_3108,A_3109] :
      ( v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109)) ) ),
    inference(splitRight,[status(thm)],[c_5913])).

tff(c_5987,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_5985])).

tff(c_5990,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_5987,c_60])).

tff(c_5993,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5990])).

tff(c_5995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_110,c_5993])).

tff(c_5997,plain,(
    ~ v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5985])).

tff(c_5996,plain,(
    ! [C_3108,A_3109] :
      ( v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3108)
      | ~ m1_subset_1(C_3108,k1_zfmisc_1(A_3109))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3109)) ) ),
    inference(splitRight,[status(thm)],[c_5985])).

tff(c_5998,plain,(
    v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_5996])).

tff(c_203,plain,(
    ! [B_88] :
      ( ~ v2_struct_0('#skF_8'(B_88))
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_6100,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_5998,c_203])).

tff(c_6103,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5715,c_5820,c_5914,c_6100])).

tff(c_6105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5997,c_6103])).

tff(c_6107,plain,(
    ~ v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_5996])).

tff(c_5986,plain,(
    v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_5913])).

tff(c_5903,plain,(
    v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_5819])).

tff(c_5809,plain,(
    l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_5714])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k10_yellow_6(A_18,B_19),k1_zfmisc_1(u1_struct_0(A_18)))
      | ~ l1_waybel_0(B_19,A_18)
      | ~ v7_waybel_0(B_19)
      | ~ v4_orders_2(B_19)
      | v2_struct_0(B_19)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6108,plain,(
    ! [C_3610,A_3611] :
      ( r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),C_3610)
      | ~ m1_subset_1(C_3610,k1_zfmisc_1(A_3611))
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3611)) ) ),
    inference(splitRight,[status(thm)],[c_5996])).

tff(c_6145,plain,(
    ! [A_4] :
      ( r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_xboole_0)
      | ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_4)) ) ),
    inference(resolution,[status(thm)],[c_10,c_6108])).

tff(c_6148,plain,(
    ! [A_3629] : ~ m1_subset_1(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_zfmisc_1(A_3629)) ),
    inference(splitLeft,[status(thm)],[c_6145])).

tff(c_6158,plain,
    ( ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
    | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
    | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
    | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_6148])).

tff(c_6161,plain,
    ( v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_5986,c_5903,c_5809,c_6158])).

tff(c_6163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6107,c_6161])).

tff(c_6164,plain,(
    r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_6145])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [B_96,A_97] :
      ( B_96 = A_97
      | ~ r1_tarski(B_96,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_123,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_114])).

tff(c_6204,plain,(
    k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6164,c_123])).

tff(c_94,plain,(
    ! [B_88] :
      ( v1_compts_1('#skF_6')
      | v3_yellow_6('#skF_8'(B_88),'#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_143,plain,(
    ! [B_88] :
      ( v3_yellow_6('#skF_8'(B_88),'#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_94])).

tff(c_238,plain,(
    ! [A_146,B_147] :
      ( k10_yellow_6(A_146,B_147) != k1_xboole_0
      | ~ v3_yellow_6(B_147,A_146)
      | ~ l1_waybel_0(B_147,A_146)
      | ~ v7_waybel_0(B_147)
      | ~ v4_orders_2(B_147)
      | v2_struct_0(B_147)
      | ~ l1_pre_topc(A_146)
      | ~ v2_pre_topc(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_244,plain,(
    ! [B_88] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_88)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(B_88),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_88))
      | ~ v4_orders_2('#skF_8'(B_88))
      | v2_struct_0('#skF_8'(B_88))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(resolution,[status(thm)],[c_143,c_238])).

tff(c_248,plain,(
    ! [B_88] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_88)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(B_88),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_88))
      | ~ v4_orders_2('#skF_8'(B_88))
      | v2_struct_0('#skF_8'(B_88))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_88,'#skF_6')
      | ~ v7_waybel_0(B_88)
      | ~ v4_orders_2(B_88)
      | v2_struct_0(B_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_244])).

tff(c_269,plain,(
    ! [B_159] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_159)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(B_159),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_159))
      | ~ v4_orders_2('#skF_8'(B_159))
      | v2_struct_0('#skF_8'(B_159))
      | ~ l1_waybel_0(B_159,'#skF_6')
      | ~ v7_waybel_0(B_159)
      | ~ v4_orders_2(B_159)
      | v2_struct_0(B_159) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_248])).

tff(c_274,plain,(
    ! [B_160] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_160)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_8'(B_160))
      | ~ v4_orders_2('#skF_8'(B_160))
      | v2_struct_0('#skF_8'(B_160))
      | ~ l1_waybel_0(B_160,'#skF_6')
      | ~ v7_waybel_0(B_160)
      | ~ v4_orders_2(B_160)
      | v2_struct_0(B_160) ) ),
    inference(resolution,[status(thm)],[c_231,c_269])).

tff(c_279,plain,(
    ! [B_161] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_161)) != k1_xboole_0
      | ~ v4_orders_2('#skF_8'(B_161))
      | v2_struct_0('#skF_8'(B_161))
      | ~ l1_waybel_0(B_161,'#skF_6')
      | ~ v7_waybel_0(B_161)
      | ~ v4_orders_2(B_161)
      | v2_struct_0(B_161) ) ),
    inference(resolution,[status(thm)],[c_222,c_274])).

tff(c_284,plain,(
    ! [B_162] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_162)) != k1_xboole_0
      | v2_struct_0('#skF_8'(B_162))
      | ~ l1_waybel_0(B_162,'#skF_6')
      | ~ v7_waybel_0(B_162)
      | ~ v4_orders_2(B_162)
      | v2_struct_0(B_162) ) ),
    inference(resolution,[status(thm)],[c_213,c_279])).

tff(c_288,plain,(
    ! [B_162] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_162)) != k1_xboole_0
      | ~ l1_waybel_0(B_162,'#skF_6')
      | ~ v7_waybel_0(B_162)
      | ~ v4_orders_2(B_162)
      | v2_struct_0(B_162) ) ),
    inference(resolution,[status(thm)],[c_284,c_203])).

tff(c_6267,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6204,c_288])).

tff(c_6348,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5715,c_5820,c_5914,c_6267])).

tff(c_6350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5997,c_6348])).

tff(c_6351,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_6352,plain,(
    v1_compts_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_78,plain,
    ( v4_orders_2('#skF_7')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_6354,plain,(
    v4_orders_2('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6352,c_78])).

tff(c_76,plain,
    ( v7_waybel_0('#skF_7')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_6357,plain,(
    v7_waybel_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6352,c_76])).

tff(c_74,plain,
    ( l1_waybel_0('#skF_7','#skF_6')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_6359,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6352,c_74])).

tff(c_46,plain,(
    ! [A_63,B_67] :
      ( r3_waybel_9(A_63,B_67,'#skF_3'(A_63,B_67))
      | ~ l1_waybel_0(B_67,A_63)
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1(A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_48,plain,(
    ! [A_63,B_67] :
      ( m1_subset_1('#skF_3'(A_63,B_67),u1_struct_0(A_63))
      | ~ l1_waybel_0(B_67,A_63)
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1(A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_234])).

tff(c_6489,plain,(
    ! [A_3750,B_3751,C_3752] :
      ( m2_yellow_6('#skF_2'(A_3750,B_3751,C_3752),A_3750,B_3751)
      | ~ r3_waybel_9(A_3750,B_3751,C_3752)
      | ~ m1_subset_1(C_3752,u1_struct_0(A_3750))
      | ~ l1_waybel_0(B_3751,A_3750)
      | ~ v7_waybel_0(B_3751)
      | ~ v4_orders_2(B_3751)
      | v2_struct_0(B_3751)
      | ~ l1_pre_topc(A_3750)
      | ~ v2_pre_topc(A_3750)
      | v2_struct_0(A_3750) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_26,plain,(
    ! [C_23,A_20,B_21] :
      ( l1_waybel_0(C_23,A_20)
      | ~ m2_yellow_6(C_23,A_20,B_21)
      | ~ l1_waybel_0(B_21,A_20)
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21)
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6587,plain,(
    ! [A_3771,B_3772,C_3773] :
      ( l1_waybel_0('#skF_2'(A_3771,B_3772,C_3773),A_3771)
      | ~ l1_struct_0(A_3771)
      | ~ r3_waybel_9(A_3771,B_3772,C_3773)
      | ~ m1_subset_1(C_3773,u1_struct_0(A_3771))
      | ~ l1_waybel_0(B_3772,A_3771)
      | ~ v7_waybel_0(B_3772)
      | ~ v4_orders_2(B_3772)
      | v2_struct_0(B_3772)
      | ~ l1_pre_topc(A_3771)
      | ~ v2_pre_topc(A_3771)
      | v2_struct_0(A_3771) ) ),
    inference(resolution,[status(thm)],[c_6489,c_26])).

tff(c_6633,plain,(
    ! [A_3794,B_3795,B_3796] :
      ( l1_waybel_0('#skF_2'(A_3794,B_3795,'#skF_3'(A_3794,B_3796)),A_3794)
      | ~ l1_struct_0(A_3794)
      | ~ r3_waybel_9(A_3794,B_3795,'#skF_3'(A_3794,B_3796))
      | ~ l1_waybel_0(B_3795,A_3794)
      | ~ v7_waybel_0(B_3795)
      | ~ v4_orders_2(B_3795)
      | v2_struct_0(B_3795)
      | ~ l1_waybel_0(B_3796,A_3794)
      | ~ v7_waybel_0(B_3796)
      | ~ v4_orders_2(B_3796)
      | v2_struct_0(B_3796)
      | ~ v1_compts_1(A_3794)
      | ~ l1_pre_topc(A_3794)
      | ~ v2_pre_topc(A_3794)
      | v2_struct_0(A_3794) ) ),
    inference(resolution,[status(thm)],[c_48,c_6587])).

tff(c_34,plain,(
    ! [B_26,A_24] :
      ( v3_yellow_6(B_26,A_24)
      | k10_yellow_6(A_24,B_26) = k1_xboole_0
      | ~ l1_waybel_0(B_26,A_24)
      | ~ v7_waybel_0(B_26)
      | ~ v4_orders_2(B_26)
      | v2_struct_0(B_26)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_72,plain,(
    ! [C_87] :
      ( ~ v3_yellow_6(C_87,'#skF_6')
      | ~ m2_yellow_6(C_87,'#skF_6','#skF_7')
      | ~ v1_compts_1('#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_287])).

tff(c_6386,plain,(
    ! [C_87] :
      ( ~ v3_yellow_6(C_87,'#skF_6')
      | ~ m2_yellow_6(C_87,'#skF_6','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6352,c_72])).

tff(c_6505,plain,(
    ! [C_3752] :
      ( ~ v3_yellow_6('#skF_2'('#skF_6','#skF_7',C_3752),'#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7',C_3752)
      | ~ m1_subset_1(C_3752,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6489,c_6386])).

tff(c_6512,plain,(
    ! [C_3752] :
      ( ~ v3_yellow_6('#skF_2'('#skF_6','#skF_7',C_3752),'#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7',C_3752)
      | ~ m1_subset_1(C_3752,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6354,c_6357,c_6359,c_6505])).

tff(c_6521,plain,(
    ! [C_3757] :
      ( ~ v3_yellow_6('#skF_2'('#skF_6','#skF_7',C_3757),'#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7',C_3757)
      | ~ m1_subset_1(C_3757,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6351,c_6512])).

tff(c_6524,plain,(
    ! [C_3757] :
      ( ~ r3_waybel_9('#skF_6','#skF_7',C_3757)
      | ~ m1_subset_1(C_3757,u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7',C_3757)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7',C_3757),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7',C_3757))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7',C_3757))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7',C_3757))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_6521])).

tff(c_6527,plain,(
    ! [C_3757] :
      ( ~ r3_waybel_9('#skF_6','#skF_7',C_3757)
      | ~ m1_subset_1(C_3757,u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7',C_3757)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7',C_3757),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7',C_3757))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7',C_3757))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7',C_3757))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6524])).

tff(c_6541,plain,(
    ! [C_3764] :
      ( ~ r3_waybel_9('#skF_6','#skF_7',C_3764)
      | ~ m1_subset_1(C_3764,u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7',C_3764)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7',C_3764),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7',C_3764))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7',C_3764))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7',C_3764)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6527])).

tff(c_6549,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_6541])).

tff(c_6560,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6352,c_6549])).

tff(c_6561,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6560])).

tff(c_6637,plain,(
    ! [B_3796] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_3796,'#skF_6')
      | ~ v7_waybel_0(B_3796)
      | ~ v4_orders_2(B_3796)
      | v2_struct_0(B_3796)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6633,c_6561])).

tff(c_6640,plain,(
    ! [B_3796] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_3796,'#skF_6')
      | ~ v7_waybel_0(B_3796)
      | ~ v4_orders_2(B_3796)
      | v2_struct_0(B_3796)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6352,c_6354,c_6357,c_6359,c_6637])).

tff(c_6641,plain,(
    ! [B_3796] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3796))
      | ~ l1_waybel_0(B_3796,'#skF_6')
      | ~ v7_waybel_0(B_3796)
      | ~ v4_orders_2(B_3796)
      | v2_struct_0(B_3796) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6351,c_6640])).

tff(c_6696,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6641])).

tff(c_6699,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_22,c_6696])).

tff(c_6703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6699])).

tff(c_6705,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_6641])).

tff(c_30,plain,(
    ! [C_23,A_20,B_21] :
      ( v4_orders_2(C_23)
      | ~ m2_yellow_6(C_23,A_20,B_21)
      | ~ l1_waybel_0(B_21,A_20)
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21)
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6529,plain,(
    ! [A_3758,B_3759,C_3760] :
      ( v4_orders_2('#skF_2'(A_3758,B_3759,C_3760))
      | ~ l1_struct_0(A_3758)
      | ~ r3_waybel_9(A_3758,B_3759,C_3760)
      | ~ m1_subset_1(C_3760,u1_struct_0(A_3758))
      | ~ l1_waybel_0(B_3759,A_3758)
      | ~ v7_waybel_0(B_3759)
      | ~ v4_orders_2(B_3759)
      | v2_struct_0(B_3759)
      | ~ l1_pre_topc(A_3758)
      | ~ v2_pre_topc(A_3758)
      | v2_struct_0(A_3758) ) ),
    inference(resolution,[status(thm)],[c_6489,c_30])).

tff(c_6538,plain,(
    ! [A_63,B_3759,B_67] :
      ( v4_orders_2('#skF_2'(A_63,B_3759,'#skF_3'(A_63,B_67)))
      | ~ l1_struct_0(A_63)
      | ~ r3_waybel_9(A_63,B_3759,'#skF_3'(A_63,B_67))
      | ~ l1_waybel_0(B_3759,A_63)
      | ~ v7_waybel_0(B_3759)
      | ~ v4_orders_2(B_3759)
      | v2_struct_0(B_3759)
      | ~ l1_waybel_0(B_67,A_63)
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1(A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_48,c_6529])).

tff(c_28,plain,(
    ! [C_23,A_20,B_21] :
      ( v7_waybel_0(C_23)
      | ~ m2_yellow_6(C_23,A_20,B_21)
      | ~ l1_waybel_0(B_21,A_20)
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21)
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6563,plain,(
    ! [A_3765,B_3766,C_3767] :
      ( v7_waybel_0('#skF_2'(A_3765,B_3766,C_3767))
      | ~ l1_struct_0(A_3765)
      | ~ r3_waybel_9(A_3765,B_3766,C_3767)
      | ~ m1_subset_1(C_3767,u1_struct_0(A_3765))
      | ~ l1_waybel_0(B_3766,A_3765)
      | ~ v7_waybel_0(B_3766)
      | ~ v4_orders_2(B_3766)
      | v2_struct_0(B_3766)
      | ~ l1_pre_topc(A_3765)
      | ~ v2_pre_topc(A_3765)
      | v2_struct_0(A_3765) ) ),
    inference(resolution,[status(thm)],[c_6489,c_28])).

tff(c_6572,plain,(
    ! [A_63,B_3766,B_67] :
      ( v7_waybel_0('#skF_2'(A_63,B_3766,'#skF_3'(A_63,B_67)))
      | ~ l1_struct_0(A_63)
      | ~ r3_waybel_9(A_63,B_3766,'#skF_3'(A_63,B_67))
      | ~ l1_waybel_0(B_3766,A_63)
      | ~ v7_waybel_0(B_3766)
      | ~ v4_orders_2(B_3766)
      | v2_struct_0(B_3766)
      | ~ l1_waybel_0(B_67,A_63)
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1(A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63)
      | v2_struct_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_48,c_6563])).

tff(c_6706,plain,(
    ! [B_3822] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3822))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3822)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3822)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3822)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3822))
      | ~ l1_waybel_0(B_3822,'#skF_6')
      | ~ v7_waybel_0(B_3822)
      | ~ v4_orders_2(B_3822)
      | v2_struct_0(B_3822) ) ),
    inference(splitRight,[status(thm)],[c_6641])).

tff(c_6710,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6572,c_6706])).

tff(c_6713,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6352,c_6354,c_6357,c_6359,c_6705,c_6710])).

tff(c_6715,plain,(
    ! [B_3823] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3823))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3823)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3823)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3823))
      | ~ l1_waybel_0(B_3823,'#skF_6')
      | ~ v7_waybel_0(B_3823)
      | ~ v4_orders_2(B_3823)
      | v2_struct_0(B_3823) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6351,c_6713])).

tff(c_6719,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_6538,c_6715])).

tff(c_6722,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6352,c_6354,c_6357,c_6359,c_6705,c_6719])).

tff(c_6724,plain,(
    ! [B_3824] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3824))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3824)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3824))
      | ~ l1_waybel_0(B_3824,'#skF_6')
      | ~ v7_waybel_0(B_3824)
      | ~ v4_orders_2(B_3824)
      | v2_struct_0(B_3824) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6351,c_6722])).

tff(c_32,plain,(
    ! [C_23,A_20,B_21] :
      ( ~ v2_struct_0(C_23)
      | ~ m2_yellow_6(C_23,A_20,B_21)
      | ~ l1_waybel_0(B_21,A_20)
      | ~ v7_waybel_0(B_21)
      | ~ v4_orders_2(B_21)
      | v2_struct_0(B_21)
      | ~ l1_struct_0(A_20)
      | v2_struct_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6507,plain,(
    ! [A_3750,B_3751,C_3752] :
      ( ~ v2_struct_0('#skF_2'(A_3750,B_3751,C_3752))
      | ~ l1_struct_0(A_3750)
      | ~ r3_waybel_9(A_3750,B_3751,C_3752)
      | ~ m1_subset_1(C_3752,u1_struct_0(A_3750))
      | ~ l1_waybel_0(B_3751,A_3750)
      | ~ v7_waybel_0(B_3751)
      | ~ v4_orders_2(B_3751)
      | v2_struct_0(B_3751)
      | ~ l1_pre_topc(A_3750)
      | ~ v2_pre_topc(A_3750)
      | v2_struct_0(A_3750) ) ),
    inference(resolution,[status(thm)],[c_6489,c_32])).

tff(c_6726,plain,(
    ! [B_3824] :
      ( ~ l1_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_3'('#skF_6',B_3824),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3824))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3824))
      | ~ l1_waybel_0(B_3824,'#skF_6')
      | ~ v7_waybel_0(B_3824)
      | ~ v4_orders_2(B_3824)
      | v2_struct_0(B_3824) ) ),
    inference(resolution,[status(thm)],[c_6724,c_6507])).

tff(c_6729,plain,(
    ! [B_3824] :
      ( ~ m1_subset_1('#skF_3'('#skF_6',B_3824),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6')
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3824))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3824))
      | ~ l1_waybel_0(B_3824,'#skF_6')
      | ~ v7_waybel_0(B_3824)
      | ~ v4_orders_2(B_3824)
      | v2_struct_0(B_3824) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6354,c_6357,c_6359,c_6705,c_6726])).

tff(c_6735,plain,(
    ! [B_3828] :
      ( ~ m1_subset_1('#skF_3'('#skF_6',B_3828),u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3828))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3828))
      | ~ l1_waybel_0(B_3828,'#skF_6')
      | ~ v7_waybel_0(B_3828)
      | ~ v4_orders_2(B_3828)
      | v2_struct_0(B_3828) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6351,c_6729])).

tff(c_6739,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_6735])).

tff(c_6742,plain,(
    ! [B_67] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6352,c_6739])).

tff(c_6744,plain,(
    ! [B_3829] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_3829))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3829))
      | ~ l1_waybel_0(B_3829,'#skF_6')
      | ~ v7_waybel_0(B_3829)
      | ~ v4_orders_2(B_3829)
      | v2_struct_0(B_3829) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6742])).

tff(c_6574,plain,(
    ! [C_3768,A_3769,B_3770] :
      ( r2_hidden(C_3768,k10_yellow_6(A_3769,'#skF_2'(A_3769,B_3770,C_3768)))
      | ~ r3_waybel_9(A_3769,B_3770,C_3768)
      | ~ m1_subset_1(C_3768,u1_struct_0(A_3769))
      | ~ l1_waybel_0(B_3770,A_3769)
      | ~ v7_waybel_0(B_3770)
      | ~ v4_orders_2(B_3770)
      | v2_struct_0(B_3770)
      | ~ l1_pre_topc(A_3769)
      | ~ v2_pre_topc(A_3769)
      | v2_struct_0(A_3769) ) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6586,plain,(
    ! [A_3769,B_3770,C_3768] :
      ( ~ r1_tarski(k10_yellow_6(A_3769,'#skF_2'(A_3769,B_3770,C_3768)),C_3768)
      | ~ r3_waybel_9(A_3769,B_3770,C_3768)
      | ~ m1_subset_1(C_3768,u1_struct_0(A_3769))
      | ~ l1_waybel_0(B_3770,A_3769)
      | ~ v7_waybel_0(B_3770)
      | ~ v4_orders_2(B_3770)
      | v2_struct_0(B_3770)
      | ~ l1_pre_topc(A_3769)
      | ~ v2_pre_topc(A_3769)
      | v2_struct_0(A_3769) ) ),
    inference(resolution,[status(thm)],[c_6574,c_20])).

tff(c_6756,plain,(
    ! [B_3829] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'('#skF_6',B_3829))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3829))
      | ~ m1_subset_1('#skF_3'('#skF_6',B_3829),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3829))
      | ~ l1_waybel_0(B_3829,'#skF_6')
      | ~ v7_waybel_0(B_3829)
      | ~ v4_orders_2(B_3829)
      | v2_struct_0(B_3829) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6744,c_6586])).

tff(c_6780,plain,(
    ! [B_3829] :
      ( ~ m1_subset_1('#skF_3'('#skF_6',B_3829),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3829))
      | ~ l1_waybel_0(B_3829,'#skF_6')
      | ~ v7_waybel_0(B_3829)
      | ~ v4_orders_2(B_3829)
      | v2_struct_0(B_3829) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6354,c_6357,c_6359,c_8,c_6756])).

tff(c_6795,plain,(
    ! [B_3830] :
      ( ~ m1_subset_1('#skF_3'('#skF_6',B_3830),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3830))
      | ~ l1_waybel_0(B_3830,'#skF_6')
      | ~ v7_waybel_0(B_3830)
      | ~ v4_orders_2(B_3830)
      | v2_struct_0(B_3830) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6351,c_6780])).

tff(c_6799,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_6795])).

tff(c_6802,plain,(
    ! [B_67] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_67))
      | ~ l1_waybel_0(B_67,'#skF_6')
      | ~ v7_waybel_0(B_67)
      | ~ v4_orders_2(B_67)
      | v2_struct_0(B_67)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6352,c_6799])).

tff(c_6804,plain,(
    ! [B_3831] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_3831))
      | ~ l1_waybel_0(B_3831,'#skF_6')
      | ~ v7_waybel_0(B_3831)
      | ~ v4_orders_2(B_3831)
      | v2_struct_0(B_3831) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6802])).

tff(c_6812,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ v7_waybel_0('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_6804])).

tff(c_6819,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_6352,c_6354,c_6357,c_6359,c_6812])).

tff(c_6821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_6351,c_6819])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.41/4.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/4.27  
% 11.67/4.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/4.28  %$ r3_waybel_9 > m2_yellow_6 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k6_yellow_6 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_8 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4
% 11.67/4.28  
% 11.67/4.28  %Foreground sorts:
% 11.67/4.28  
% 11.67/4.28  
% 11.67/4.28  %Background operators:
% 11.67/4.28  
% 11.67/4.28  
% 11.67/4.28  %Foreground operators:
% 11.67/4.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 11.67/4.28  tff('#skF_5', type, '#skF_5': $i > $i).
% 11.67/4.28  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 11.67/4.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 11.67/4.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.67/4.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.67/4.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.67/4.28  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 11.67/4.28  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 11.67/4.28  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 11.67/4.28  tff('#skF_8', type, '#skF_8': $i > $i).
% 11.67/4.28  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 11.67/4.28  tff('#skF_7', type, '#skF_7': $i).
% 11.67/4.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 11.67/4.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.67/4.28  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 11.67/4.28  tff('#skF_6', type, '#skF_6': $i).
% 11.67/4.28  tff(k6_yellow_6, type, k6_yellow_6: $i > $i).
% 11.67/4.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.67/4.28  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 11.67/4.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.67/4.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 11.67/4.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.67/4.28  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 11.67/4.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.67/4.28  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 11.67/4.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 11.67/4.28  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 11.67/4.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 11.67/4.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.67/4.28  
% 11.67/4.31  tff(f_287, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 11.67/4.31  tff(f_262, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ~(r2_hidden(B, k6_yellow_6(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~r3_waybel_9(A, B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_yellow19)).
% 11.67/4.31  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_subset_1)).
% 11.67/4.31  tff(f_82, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 11.67/4.31  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 11.67/4.31  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 11.67/4.31  tff(f_181, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 11.67/4.31  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 11.67/4.31  tff(f_108, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 11.67/4.31  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 11.67/4.31  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 11.67/4.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.67/4.31  tff(f_130, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 11.67/4.31  tff(f_234, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l37_yellow19)).
% 11.67/4.31  tff(f_210, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 11.67/4.31  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.67/4.31  tff(c_70, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_80, plain, (~v2_struct_0('#skF_7') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_110, plain, (~v1_compts_1('#skF_6')), inference(splitLeft, [status(thm)], [c_80])).
% 11.67/4.31  tff(c_68, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_66, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_58, plain, (![A_69]: (v4_orders_2('#skF_5'(A_69)) | v1_compts_1(A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_262])).
% 11.67/4.31  tff(c_106, plain, (![B_88]: (v1_compts_1('#skF_6') | m2_yellow_6('#skF_8'(B_88), '#skF_6', B_88) | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_154, plain, (![B_88]: (m2_yellow_6('#skF_8'(B_88), '#skF_6', B_88) | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(negUnitSimplification, [status(thm)], [c_110, c_106])).
% 11.67/4.31  tff(c_14, plain, (![A_5, B_6, C_10]: (r2_hidden('#skF_1'(A_5, B_6, C_10), B_6) | r1_tarski(B_6, C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 11.67/4.31  tff(c_234, plain, (![A_144, B_145]: (m1_subset_1(k10_yellow_6(A_144, B_145), k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_waybel_0(B_145, A_144) | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.67/4.31  tff(c_18, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 11.67/4.31  tff(c_263, plain, (![A_156, A_157, B_158]: (m1_subset_1(A_156, u1_struct_0(A_157)) | ~r2_hidden(A_156, k10_yellow_6(A_157, B_158)) | ~l1_waybel_0(B_158, A_157) | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(resolution, [status(thm)], [c_234, c_18])).
% 11.67/4.31  tff(c_268, plain, (![A_5, A_157, B_158, C_10]: (m1_subset_1('#skF_1'(A_5, k10_yellow_6(A_157, B_158), C_10), u1_struct_0(A_157)) | ~l1_waybel_0(B_158, A_157) | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157) | r1_tarski(k10_yellow_6(A_157, B_158), C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(A_5)) | ~m1_subset_1(k10_yellow_6(A_157, B_158), k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_14, c_263])).
% 11.67/4.31  tff(c_297, plain, (![A_168, B_169, C_170]: (r3_waybel_9(A_168, B_169, C_170) | ~r2_hidden(C_170, k10_yellow_6(A_168, B_169)) | ~m1_subset_1(C_170, u1_struct_0(A_168)) | ~l1_waybel_0(B_169, A_168) | ~v7_waybel_0(B_169) | ~v4_orders_2(B_169) | v2_struct_0(B_169) | ~l1_pre_topc(A_168) | ~v2_pre_topc(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_154])).
% 11.67/4.31  tff(c_424, plain, (![A_229, B_230, A_231, C_232]: (r3_waybel_9(A_229, B_230, '#skF_1'(A_231, k10_yellow_6(A_229, B_230), C_232)) | ~m1_subset_1('#skF_1'(A_231, k10_yellow_6(A_229, B_230), C_232), u1_struct_0(A_229)) | ~l1_waybel_0(B_230, A_229) | ~v7_waybel_0(B_230) | ~v4_orders_2(B_230) | v2_struct_0(B_230) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229) | r1_tarski(k10_yellow_6(A_229, B_230), C_232) | ~m1_subset_1(C_232, k1_zfmisc_1(A_231)) | ~m1_subset_1(k10_yellow_6(A_229, B_230), k1_zfmisc_1(A_231)))), inference(resolution, [status(thm)], [c_14, c_297])).
% 11.67/4.31  tff(c_432, plain, (![A_233, B_234, A_235, C_236]: (r3_waybel_9(A_233, B_234, '#skF_1'(A_235, k10_yellow_6(A_233, B_234), C_236)) | ~l1_waybel_0(B_234, A_233) | ~v7_waybel_0(B_234) | ~v4_orders_2(B_234) | v2_struct_0(B_234) | ~l1_pre_topc(A_233) | ~v2_pre_topc(A_233) | v2_struct_0(A_233) | r1_tarski(k10_yellow_6(A_233, B_234), C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(A_235)) | ~m1_subset_1(k10_yellow_6(A_233, B_234), k1_zfmisc_1(A_235)))), inference(resolution, [status(thm)], [c_268, c_424])).
% 11.67/4.31  tff(c_40, plain, (![A_34, B_42, D_48, C_46]: (r3_waybel_9(A_34, B_42, D_48) | ~r3_waybel_9(A_34, C_46, D_48) | ~m1_subset_1(D_48, u1_struct_0(A_34)) | ~m2_yellow_6(C_46, A_34, B_42) | ~l1_waybel_0(B_42, A_34) | ~v7_waybel_0(B_42) | ~v4_orders_2(B_42) | v2_struct_0(B_42) | ~l1_pre_topc(A_34) | ~v2_pre_topc(A_34) | v2_struct_0(A_34))), inference(cnfTransformation, [status(thm)], [f_181])).
% 11.67/4.31  tff(c_4198, plain, (![A_2393, C_2395, B_2396, B_2392, A_2394]: (r3_waybel_9(A_2394, B_2396, '#skF_1'(A_2393, k10_yellow_6(A_2394, B_2392), C_2395)) | ~m1_subset_1('#skF_1'(A_2393, k10_yellow_6(A_2394, B_2392), C_2395), u1_struct_0(A_2394)) | ~m2_yellow_6(B_2392, A_2394, B_2396) | ~l1_waybel_0(B_2396, A_2394) | ~v7_waybel_0(B_2396) | ~v4_orders_2(B_2396) | v2_struct_0(B_2396) | ~l1_waybel_0(B_2392, A_2394) | ~v7_waybel_0(B_2392) | ~v4_orders_2(B_2392) | v2_struct_0(B_2392) | ~l1_pre_topc(A_2394) | ~v2_pre_topc(A_2394) | v2_struct_0(A_2394) | r1_tarski(k10_yellow_6(A_2394, B_2392), C_2395) | ~m1_subset_1(C_2395, k1_zfmisc_1(A_2393)) | ~m1_subset_1(k10_yellow_6(A_2394, B_2392), k1_zfmisc_1(A_2393)))), inference(resolution, [status(thm)], [c_432, c_40])).
% 11.67/4.31  tff(c_4337, plain, (![B_2436, A_2432, C_2435, B_2434, A_2433]: (r3_waybel_9(A_2432, B_2436, '#skF_1'(A_2433, k10_yellow_6(A_2432, B_2434), C_2435)) | ~m2_yellow_6(B_2434, A_2432, B_2436) | ~l1_waybel_0(B_2436, A_2432) | ~v7_waybel_0(B_2436) | ~v4_orders_2(B_2436) | v2_struct_0(B_2436) | ~l1_waybel_0(B_2434, A_2432) | ~v7_waybel_0(B_2434) | ~v4_orders_2(B_2434) | v2_struct_0(B_2434) | ~l1_pre_topc(A_2432) | ~v2_pre_topc(A_2432) | v2_struct_0(A_2432) | r1_tarski(k10_yellow_6(A_2432, B_2434), C_2435) | ~m1_subset_1(C_2435, k1_zfmisc_1(A_2433)) | ~m1_subset_1(k10_yellow_6(A_2432, B_2434), k1_zfmisc_1(A_2433)))), inference(resolution, [status(thm)], [c_268, c_4198])).
% 11.67/4.31  tff(c_50, plain, (![A_69, C_79]: (~r3_waybel_9(A_69, '#skF_5'(A_69), C_79) | ~m1_subset_1(C_79, u1_struct_0(A_69)) | v1_compts_1(A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_262])).
% 11.67/4.31  tff(c_5628, plain, (![A_3085, A_3086, B_3087, C_3088]: (~m1_subset_1('#skF_1'(A_3085, k10_yellow_6(A_3086, B_3087), C_3088), u1_struct_0(A_3086)) | v1_compts_1(A_3086) | ~m2_yellow_6(B_3087, A_3086, '#skF_5'(A_3086)) | ~l1_waybel_0('#skF_5'(A_3086), A_3086) | ~v7_waybel_0('#skF_5'(A_3086)) | ~v4_orders_2('#skF_5'(A_3086)) | v2_struct_0('#skF_5'(A_3086)) | ~l1_waybel_0(B_3087, A_3086) | ~v7_waybel_0(B_3087) | ~v4_orders_2(B_3087) | v2_struct_0(B_3087) | ~l1_pre_topc(A_3086) | ~v2_pre_topc(A_3086) | v2_struct_0(A_3086) | r1_tarski(k10_yellow_6(A_3086, B_3087), C_3088) | ~m1_subset_1(C_3088, k1_zfmisc_1(A_3085)) | ~m1_subset_1(k10_yellow_6(A_3086, B_3087), k1_zfmisc_1(A_3085)))), inference(resolution, [status(thm)], [c_4337, c_50])).
% 11.67/4.31  tff(c_5677, plain, (![A_3106, B_3107, C_3108, A_3109]: (v1_compts_1(A_3106) | ~m2_yellow_6(B_3107, A_3106, '#skF_5'(A_3106)) | ~l1_waybel_0('#skF_5'(A_3106), A_3106) | ~v7_waybel_0('#skF_5'(A_3106)) | ~v4_orders_2('#skF_5'(A_3106)) | v2_struct_0('#skF_5'(A_3106)) | ~l1_waybel_0(B_3107, A_3106) | ~v7_waybel_0(B_3107) | ~v4_orders_2(B_3107) | v2_struct_0(B_3107) | ~l1_pre_topc(A_3106) | ~v2_pre_topc(A_3106) | v2_struct_0(A_3106) | r1_tarski(k10_yellow_6(A_3106, B_3107), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6(A_3106, B_3107), k1_zfmisc_1(A_3109)))), inference(resolution, [status(thm)], [c_268, c_5628])).
% 11.67/4.31  tff(c_5699, plain, (![C_3108, A_3109]: (v1_compts_1('#skF_6') | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6')))), inference(resolution, [status(thm)], [c_154, c_5677])).
% 11.67/4.31  tff(c_5703, plain, (![C_3108, A_3109]: (v1_compts_1('#skF_6') | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5699])).
% 11.67/4.31  tff(c_5704, plain, (![C_3108, A_3109]: (~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5703])).
% 11.67/4.31  tff(c_5705, plain, (~v4_orders_2('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_5704])).
% 11.67/4.31  tff(c_5708, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_58, c_5705])).
% 11.67/4.31  tff(c_5711, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5708])).
% 11.67/4.31  tff(c_5713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5711])).
% 11.67/4.31  tff(c_5715, plain, (v4_orders_2('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_5704])).
% 11.67/4.31  tff(c_56, plain, (![A_69]: (v7_waybel_0('#skF_5'(A_69)) | v1_compts_1(A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_262])).
% 11.67/4.31  tff(c_54, plain, (![A_69]: (l1_waybel_0('#skF_5'(A_69), A_69) | v1_compts_1(A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_262])).
% 11.67/4.31  tff(c_22, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.67/4.31  tff(c_188, plain, (![C_126, A_127, B_128]: (~v2_struct_0(C_126) | ~m2_yellow_6(C_126, A_127, B_128) | ~l1_waybel_0(B_128, A_127) | ~v7_waybel_0(B_128) | ~v4_orders_2(B_128) | v2_struct_0(B_128) | ~l1_struct_0(A_127) | v2_struct_0(A_127))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.67/4.31  tff(c_191, plain, (![B_88]: (~v2_struct_0('#skF_8'(B_88)) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(resolution, [status(thm)], [c_154, c_188])).
% 11.67/4.31  tff(c_194, plain, (![B_88]: (~v2_struct_0('#skF_8'(B_88)) | ~l1_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(negUnitSimplification, [status(thm)], [c_70, c_191])).
% 11.67/4.31  tff(c_195, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_194])).
% 11.67/4.31  tff(c_198, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_22, c_195])).
% 11.67/4.31  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_198])).
% 11.67/4.31  tff(c_204, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_194])).
% 11.67/4.31  tff(c_224, plain, (![C_138, A_139, B_140]: (l1_waybel_0(C_138, A_139) | ~m2_yellow_6(C_138, A_139, B_140) | ~l1_waybel_0(B_140, A_139) | ~v7_waybel_0(B_140) | ~v4_orders_2(B_140) | v2_struct_0(B_140) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.67/4.31  tff(c_227, plain, (![B_88]: (l1_waybel_0('#skF_8'(B_88), '#skF_6') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(resolution, [status(thm)], [c_154, c_224])).
% 11.67/4.31  tff(c_230, plain, (![B_88]: (l1_waybel_0('#skF_8'(B_88), '#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_227])).
% 11.67/4.31  tff(c_231, plain, (![B_88]: (l1_waybel_0('#skF_8'(B_88), '#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(negUnitSimplification, [status(thm)], [c_70, c_230])).
% 11.67/4.31  tff(c_5714, plain, (![C_3108, A_3109]: (~v7_waybel_0('#skF_5'('#skF_6')) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | v2_struct_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)))), inference(splitRight, [status(thm)], [c_5704])).
% 11.67/4.31  tff(c_5716, plain, (~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6')), inference(splitLeft, [status(thm)], [c_5714])).
% 11.67/4.31  tff(c_5719, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_231, c_5716])).
% 11.67/4.31  tff(c_5722, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5715, c_5719])).
% 11.67/4.31  tff(c_5723, plain, (~v7_waybel_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_5722])).
% 11.67/4.31  tff(c_5726, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_5723])).
% 11.67/4.31  tff(c_5729, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5726])).
% 11.67/4.31  tff(c_5731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5729])).
% 11.67/4.31  tff(c_5732, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_5722])).
% 11.67/4.31  tff(c_5789, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_5732])).
% 11.67/4.31  tff(c_5792, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_5789])).
% 11.67/4.31  tff(c_5795, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5792])).
% 11.67/4.31  tff(c_5797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5795])).
% 11.67/4.31  tff(c_5798, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_5732])).
% 11.67/4.31  tff(c_60, plain, (![A_69]: (~v2_struct_0('#skF_5'(A_69)) | v1_compts_1(A_69) | ~l1_pre_topc(A_69) | ~v2_pre_topc(A_69) | v2_struct_0(A_69))), inference(cnfTransformation, [status(thm)], [f_262])).
% 11.67/4.31  tff(c_5802, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_5798, c_60])).
% 11.67/4.31  tff(c_5805, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5802])).
% 11.67/4.31  tff(c_5807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5805])).
% 11.67/4.31  tff(c_5808, plain, (![C_3108, A_3109]: (~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)))), inference(splitRight, [status(thm)], [c_5714])).
% 11.67/4.31  tff(c_5810, plain, (~v7_waybel_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_5808])).
% 11.67/4.31  tff(c_5813, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_5810])).
% 11.67/4.31  tff(c_5816, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5813])).
% 11.67/4.31  tff(c_5818, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5816])).
% 11.67/4.31  tff(c_5820, plain, (v7_waybel_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_5808])).
% 11.67/4.31  tff(c_215, plain, (![C_134, A_135, B_136]: (v7_waybel_0(C_134) | ~m2_yellow_6(C_134, A_135, B_136) | ~l1_waybel_0(B_136, A_135) | ~v7_waybel_0(B_136) | ~v4_orders_2(B_136) | v2_struct_0(B_136) | ~l1_struct_0(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.67/4.31  tff(c_218, plain, (![B_88]: (v7_waybel_0('#skF_8'(B_88)) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(resolution, [status(thm)], [c_154, c_215])).
% 11.67/4.31  tff(c_221, plain, (![B_88]: (v7_waybel_0('#skF_8'(B_88)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_218])).
% 11.67/4.31  tff(c_222, plain, (![B_88]: (v7_waybel_0('#skF_8'(B_88)) | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(negUnitSimplification, [status(thm)], [c_70, c_221])).
% 11.67/4.31  tff(c_5819, plain, (![C_3108, A_3109]: (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)))), inference(splitRight, [status(thm)], [c_5808])).
% 11.67/4.31  tff(c_5821, plain, (~v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitLeft, [status(thm)], [c_5819])).
% 11.67/4.31  tff(c_5879, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_222, c_5821])).
% 11.67/4.31  tff(c_5882, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5715, c_5820, c_5879])).
% 11.67/4.31  tff(c_5883, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_5882])).
% 11.67/4.31  tff(c_5886, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_5883])).
% 11.67/4.31  tff(c_5889, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5886])).
% 11.67/4.31  tff(c_5891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5889])).
% 11.67/4.31  tff(c_5892, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_5882])).
% 11.67/4.31  tff(c_5896, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_5892, c_60])).
% 11.67/4.31  tff(c_5899, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5896])).
% 11.67/4.31  tff(c_5901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5899])).
% 11.67/4.31  tff(c_5902, plain, (![C_3108, A_3109]: (~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)))), inference(splitRight, [status(thm)], [c_5819])).
% 11.67/4.31  tff(c_5904, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_5902])).
% 11.67/4.31  tff(c_5907, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_5904])).
% 11.67/4.31  tff(c_5910, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5907])).
% 11.67/4.31  tff(c_5912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5910])).
% 11.67/4.31  tff(c_5914, plain, (l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_5902])).
% 11.67/4.31  tff(c_206, plain, (![C_130, A_131, B_132]: (v4_orders_2(C_130) | ~m2_yellow_6(C_130, A_131, B_132) | ~l1_waybel_0(B_132, A_131) | ~v7_waybel_0(B_132) | ~v4_orders_2(B_132) | v2_struct_0(B_132) | ~l1_struct_0(A_131) | v2_struct_0(A_131))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.67/4.31  tff(c_209, plain, (![B_88]: (v4_orders_2('#skF_8'(B_88)) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(resolution, [status(thm)], [c_154, c_206])).
% 11.67/4.31  tff(c_212, plain, (![B_88]: (v4_orders_2('#skF_8'(B_88)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_204, c_209])).
% 11.67/4.31  tff(c_213, plain, (![B_88]: (v4_orders_2('#skF_8'(B_88)) | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(negUnitSimplification, [status(thm)], [c_70, c_212])).
% 11.67/4.31  tff(c_5913, plain, (![C_3108, A_3109]: (~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)))), inference(splitRight, [status(thm)], [c_5902])).
% 11.67/4.31  tff(c_5970, plain, (~v4_orders_2('#skF_8'('#skF_5'('#skF_6')))), inference(splitLeft, [status(thm)], [c_5913])).
% 11.67/4.31  tff(c_5973, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_213, c_5970])).
% 11.67/4.31  tff(c_5976, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5715, c_5820, c_5914, c_5973])).
% 11.67/4.31  tff(c_5979, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_5976, c_60])).
% 11.67/4.31  tff(c_5982, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5979])).
% 11.67/4.31  tff(c_5984, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5982])).
% 11.67/4.31  tff(c_5985, plain, (![C_3108, A_3109]: (v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)))), inference(splitRight, [status(thm)], [c_5913])).
% 11.67/4.31  tff(c_5987, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_5985])).
% 11.67/4.31  tff(c_5990, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_5987, c_60])).
% 11.67/4.31  tff(c_5993, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5990])).
% 11.67/4.31  tff(c_5995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_110, c_5993])).
% 11.67/4.31  tff(c_5997, plain, (~v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_5985])).
% 11.67/4.31  tff(c_5996, plain, (![C_3108, A_3109]: (v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3108) | ~m1_subset_1(C_3108, k1_zfmisc_1(A_3109)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3109)))), inference(splitRight, [status(thm)], [c_5985])).
% 11.67/4.31  tff(c_5998, plain, (v2_struct_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitLeft, [status(thm)], [c_5996])).
% 11.67/4.31  tff(c_203, plain, (![B_88]: (~v2_struct_0('#skF_8'(B_88)) | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(splitRight, [status(thm)], [c_194])).
% 11.67/4.31  tff(c_6100, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_5998, c_203])).
% 11.67/4.31  tff(c_6103, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5715, c_5820, c_5914, c_6100])).
% 11.67/4.31  tff(c_6105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5997, c_6103])).
% 11.67/4.31  tff(c_6107, plain, (~v2_struct_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitRight, [status(thm)], [c_5996])).
% 11.67/4.31  tff(c_5986, plain, (v4_orders_2('#skF_8'('#skF_5'('#skF_6')))), inference(splitRight, [status(thm)], [c_5913])).
% 11.67/4.31  tff(c_5903, plain, (v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitRight, [status(thm)], [c_5819])).
% 11.67/4.31  tff(c_5809, plain, (l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6')), inference(splitRight, [status(thm)], [c_5714])).
% 11.67/4.31  tff(c_24, plain, (![A_18, B_19]: (m1_subset_1(k10_yellow_6(A_18, B_19), k1_zfmisc_1(u1_struct_0(A_18))) | ~l1_waybel_0(B_19, A_18) | ~v7_waybel_0(B_19) | ~v4_orders_2(B_19) | v2_struct_0(B_19) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.67/4.31  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.67/4.31  tff(c_6108, plain, (![C_3610, A_3611]: (r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), C_3610) | ~m1_subset_1(C_3610, k1_zfmisc_1(A_3611)) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3611)))), inference(splitRight, [status(thm)], [c_5996])).
% 11.67/4.31  tff(c_6145, plain, (![A_4]: (r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_xboole_0) | ~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_4)))), inference(resolution, [status(thm)], [c_10, c_6108])).
% 11.67/4.31  tff(c_6148, plain, (![A_3629]: (~m1_subset_1(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_zfmisc_1(A_3629)))), inference(splitLeft, [status(thm)], [c_6145])).
% 11.67/4.31  tff(c_6158, plain, (~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_24, c_6148])).
% 11.67/4.31  tff(c_6161, plain, (v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_5986, c_5903, c_5809, c_6158])).
% 11.67/4.31  tff(c_6163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_6107, c_6161])).
% 11.67/4.31  tff(c_6164, plain, (r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), k1_xboole_0)), inference(splitRight, [status(thm)], [c_6145])).
% 11.67/4.31  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 11.67/4.31  tff(c_114, plain, (![B_96, A_97]: (B_96=A_97 | ~r1_tarski(B_96, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.67/4.31  tff(c_123, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_114])).
% 11.67/4.31  tff(c_6204, plain, (k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6')))=k1_xboole_0), inference(resolution, [status(thm)], [c_6164, c_123])).
% 11.67/4.31  tff(c_94, plain, (![B_88]: (v1_compts_1('#skF_6') | v3_yellow_6('#skF_8'(B_88), '#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_143, plain, (![B_88]: (v3_yellow_6('#skF_8'(B_88), '#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(negUnitSimplification, [status(thm)], [c_110, c_94])).
% 11.67/4.31  tff(c_238, plain, (![A_146, B_147]: (k10_yellow_6(A_146, B_147)!=k1_xboole_0 | ~v3_yellow_6(B_147, A_146) | ~l1_waybel_0(B_147, A_146) | ~v7_waybel_0(B_147) | ~v4_orders_2(B_147) | v2_struct_0(B_147) | ~l1_pre_topc(A_146) | ~v2_pre_topc(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.67/4.31  tff(c_244, plain, (![B_88]: (k10_yellow_6('#skF_6', '#skF_8'(B_88))!=k1_xboole_0 | ~l1_waybel_0('#skF_8'(B_88), '#skF_6') | ~v7_waybel_0('#skF_8'(B_88)) | ~v4_orders_2('#skF_8'(B_88)) | v2_struct_0('#skF_8'(B_88)) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(resolution, [status(thm)], [c_143, c_238])).
% 11.67/4.31  tff(c_248, plain, (![B_88]: (k10_yellow_6('#skF_6', '#skF_8'(B_88))!=k1_xboole_0 | ~l1_waybel_0('#skF_8'(B_88), '#skF_6') | ~v7_waybel_0('#skF_8'(B_88)) | ~v4_orders_2('#skF_8'(B_88)) | v2_struct_0('#skF_8'(B_88)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_88, '#skF_6') | ~v7_waybel_0(B_88) | ~v4_orders_2(B_88) | v2_struct_0(B_88))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_244])).
% 11.67/4.31  tff(c_269, plain, (![B_159]: (k10_yellow_6('#skF_6', '#skF_8'(B_159))!=k1_xboole_0 | ~l1_waybel_0('#skF_8'(B_159), '#skF_6') | ~v7_waybel_0('#skF_8'(B_159)) | ~v4_orders_2('#skF_8'(B_159)) | v2_struct_0('#skF_8'(B_159)) | ~l1_waybel_0(B_159, '#skF_6') | ~v7_waybel_0(B_159) | ~v4_orders_2(B_159) | v2_struct_0(B_159))), inference(negUnitSimplification, [status(thm)], [c_70, c_248])).
% 11.67/4.31  tff(c_274, plain, (![B_160]: (k10_yellow_6('#skF_6', '#skF_8'(B_160))!=k1_xboole_0 | ~v7_waybel_0('#skF_8'(B_160)) | ~v4_orders_2('#skF_8'(B_160)) | v2_struct_0('#skF_8'(B_160)) | ~l1_waybel_0(B_160, '#skF_6') | ~v7_waybel_0(B_160) | ~v4_orders_2(B_160) | v2_struct_0(B_160))), inference(resolution, [status(thm)], [c_231, c_269])).
% 11.67/4.31  tff(c_279, plain, (![B_161]: (k10_yellow_6('#skF_6', '#skF_8'(B_161))!=k1_xboole_0 | ~v4_orders_2('#skF_8'(B_161)) | v2_struct_0('#skF_8'(B_161)) | ~l1_waybel_0(B_161, '#skF_6') | ~v7_waybel_0(B_161) | ~v4_orders_2(B_161) | v2_struct_0(B_161))), inference(resolution, [status(thm)], [c_222, c_274])).
% 11.67/4.31  tff(c_284, plain, (![B_162]: (k10_yellow_6('#skF_6', '#skF_8'(B_162))!=k1_xboole_0 | v2_struct_0('#skF_8'(B_162)) | ~l1_waybel_0(B_162, '#skF_6') | ~v7_waybel_0(B_162) | ~v4_orders_2(B_162) | v2_struct_0(B_162))), inference(resolution, [status(thm)], [c_213, c_279])).
% 11.67/4.31  tff(c_288, plain, (![B_162]: (k10_yellow_6('#skF_6', '#skF_8'(B_162))!=k1_xboole_0 | ~l1_waybel_0(B_162, '#skF_6') | ~v7_waybel_0(B_162) | ~v4_orders_2(B_162) | v2_struct_0(B_162))), inference(resolution, [status(thm)], [c_284, c_203])).
% 11.67/4.31  tff(c_6267, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6204, c_288])).
% 11.67/4.31  tff(c_6348, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5715, c_5820, c_5914, c_6267])).
% 11.67/4.31  tff(c_6350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5997, c_6348])).
% 11.67/4.31  tff(c_6351, plain, (~v2_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_80])).
% 11.67/4.31  tff(c_6352, plain, (v1_compts_1('#skF_6')), inference(splitRight, [status(thm)], [c_80])).
% 11.67/4.31  tff(c_78, plain, (v4_orders_2('#skF_7') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_6354, plain, (v4_orders_2('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6352, c_78])).
% 11.67/4.31  tff(c_76, plain, (v7_waybel_0('#skF_7') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_6357, plain, (v7_waybel_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6352, c_76])).
% 11.67/4.31  tff(c_74, plain, (l1_waybel_0('#skF_7', '#skF_6') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_6359, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6352, c_74])).
% 11.67/4.31  tff(c_46, plain, (![A_63, B_67]: (r3_waybel_9(A_63, B_67, '#skF_3'(A_63, B_67)) | ~l1_waybel_0(B_67, A_63) | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1(A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_234])).
% 11.67/4.31  tff(c_48, plain, (![A_63, B_67]: (m1_subset_1('#skF_3'(A_63, B_67), u1_struct_0(A_63)) | ~l1_waybel_0(B_67, A_63) | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1(A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(cnfTransformation, [status(thm)], [f_234])).
% 11.67/4.31  tff(c_6489, plain, (![A_3750, B_3751, C_3752]: (m2_yellow_6('#skF_2'(A_3750, B_3751, C_3752), A_3750, B_3751) | ~r3_waybel_9(A_3750, B_3751, C_3752) | ~m1_subset_1(C_3752, u1_struct_0(A_3750)) | ~l1_waybel_0(B_3751, A_3750) | ~v7_waybel_0(B_3751) | ~v4_orders_2(B_3751) | v2_struct_0(B_3751) | ~l1_pre_topc(A_3750) | ~v2_pre_topc(A_3750) | v2_struct_0(A_3750))), inference(cnfTransformation, [status(thm)], [f_210])).
% 11.67/4.31  tff(c_26, plain, (![C_23, A_20, B_21]: (l1_waybel_0(C_23, A_20) | ~m2_yellow_6(C_23, A_20, B_21) | ~l1_waybel_0(B_21, A_20) | ~v7_waybel_0(B_21) | ~v4_orders_2(B_21) | v2_struct_0(B_21) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.67/4.31  tff(c_6587, plain, (![A_3771, B_3772, C_3773]: (l1_waybel_0('#skF_2'(A_3771, B_3772, C_3773), A_3771) | ~l1_struct_0(A_3771) | ~r3_waybel_9(A_3771, B_3772, C_3773) | ~m1_subset_1(C_3773, u1_struct_0(A_3771)) | ~l1_waybel_0(B_3772, A_3771) | ~v7_waybel_0(B_3772) | ~v4_orders_2(B_3772) | v2_struct_0(B_3772) | ~l1_pre_topc(A_3771) | ~v2_pre_topc(A_3771) | v2_struct_0(A_3771))), inference(resolution, [status(thm)], [c_6489, c_26])).
% 11.67/4.31  tff(c_6633, plain, (![A_3794, B_3795, B_3796]: (l1_waybel_0('#skF_2'(A_3794, B_3795, '#skF_3'(A_3794, B_3796)), A_3794) | ~l1_struct_0(A_3794) | ~r3_waybel_9(A_3794, B_3795, '#skF_3'(A_3794, B_3796)) | ~l1_waybel_0(B_3795, A_3794) | ~v7_waybel_0(B_3795) | ~v4_orders_2(B_3795) | v2_struct_0(B_3795) | ~l1_waybel_0(B_3796, A_3794) | ~v7_waybel_0(B_3796) | ~v4_orders_2(B_3796) | v2_struct_0(B_3796) | ~v1_compts_1(A_3794) | ~l1_pre_topc(A_3794) | ~v2_pre_topc(A_3794) | v2_struct_0(A_3794))), inference(resolution, [status(thm)], [c_48, c_6587])).
% 11.67/4.31  tff(c_34, plain, (![B_26, A_24]: (v3_yellow_6(B_26, A_24) | k10_yellow_6(A_24, B_26)=k1_xboole_0 | ~l1_waybel_0(B_26, A_24) | ~v7_waybel_0(B_26) | ~v4_orders_2(B_26) | v2_struct_0(B_26) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_130])).
% 11.67/4.31  tff(c_72, plain, (![C_87]: (~v3_yellow_6(C_87, '#skF_6') | ~m2_yellow_6(C_87, '#skF_6', '#skF_7') | ~v1_compts_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_287])).
% 11.67/4.31  tff(c_6386, plain, (![C_87]: (~v3_yellow_6(C_87, '#skF_6') | ~m2_yellow_6(C_87, '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6352, c_72])).
% 11.67/4.31  tff(c_6505, plain, (![C_3752]: (~v3_yellow_6('#skF_2'('#skF_6', '#skF_7', C_3752), '#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', C_3752) | ~m1_subset_1(C_3752, u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_6489, c_6386])).
% 11.67/4.31  tff(c_6512, plain, (![C_3752]: (~v3_yellow_6('#skF_2'('#skF_6', '#skF_7', C_3752), '#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', C_3752) | ~m1_subset_1(C_3752, u1_struct_0('#skF_6')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6354, c_6357, c_6359, c_6505])).
% 11.67/4.31  tff(c_6521, plain, (![C_3757]: (~v3_yellow_6('#skF_2'('#skF_6', '#skF_7', C_3757), '#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', C_3757) | ~m1_subset_1(C_3757, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_70, c_6351, c_6512])).
% 11.67/4.31  tff(c_6524, plain, (![C_3757]: (~r3_waybel_9('#skF_6', '#skF_7', C_3757) | ~m1_subset_1(C_3757, u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', C_3757))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', C_3757), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', C_3757)) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', C_3757)) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', C_3757)) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_6521])).
% 11.67/4.31  tff(c_6527, plain, (![C_3757]: (~r3_waybel_9('#skF_6', '#skF_7', C_3757) | ~m1_subset_1(C_3757, u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', C_3757))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', C_3757), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', C_3757)) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', C_3757)) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', C_3757)) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6524])).
% 11.67/4.31  tff(c_6541, plain, (![C_3764]: (~r3_waybel_9('#skF_6', '#skF_7', C_3764) | ~m1_subset_1(C_3764, u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', C_3764))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', C_3764), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', C_3764)) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', C_3764)) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', C_3764)))), inference(negUnitSimplification, [status(thm)], [c_70, c_6527])).
% 11.67/4.31  tff(c_6549, plain, (![B_67]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_6541])).
% 11.67/4.31  tff(c_6560, plain, (![B_67]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6352, c_6549])).
% 11.67/4.31  tff(c_6561, plain, (![B_67]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67))), inference(negUnitSimplification, [status(thm)], [c_70, c_6560])).
% 11.67/4.31  tff(c_6637, plain, (![B_3796]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796)) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_3796, '#skF_6') | ~v7_waybel_0(B_3796) | ~v4_orders_2(B_3796) | v2_struct_0(B_3796) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_6633, c_6561])).
% 11.67/4.31  tff(c_6640, plain, (![B_3796]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_3796, '#skF_6') | ~v7_waybel_0(B_3796) | ~v4_orders_2(B_3796) | v2_struct_0(B_3796) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6352, c_6354, c_6357, c_6359, c_6637])).
% 11.67/4.31  tff(c_6641, plain, (![B_3796]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3796)) | ~l1_waybel_0(B_3796, '#skF_6') | ~v7_waybel_0(B_3796) | ~v4_orders_2(B_3796) | v2_struct_0(B_3796))), inference(negUnitSimplification, [status(thm)], [c_70, c_6351, c_6640])).
% 11.67/4.31  tff(c_6696, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_6641])).
% 11.67/4.31  tff(c_6699, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_22, c_6696])).
% 11.67/4.31  tff(c_6703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_6699])).
% 11.67/4.31  tff(c_6705, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_6641])).
% 11.67/4.31  tff(c_30, plain, (![C_23, A_20, B_21]: (v4_orders_2(C_23) | ~m2_yellow_6(C_23, A_20, B_21) | ~l1_waybel_0(B_21, A_20) | ~v7_waybel_0(B_21) | ~v4_orders_2(B_21) | v2_struct_0(B_21) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.67/4.31  tff(c_6529, plain, (![A_3758, B_3759, C_3760]: (v4_orders_2('#skF_2'(A_3758, B_3759, C_3760)) | ~l1_struct_0(A_3758) | ~r3_waybel_9(A_3758, B_3759, C_3760) | ~m1_subset_1(C_3760, u1_struct_0(A_3758)) | ~l1_waybel_0(B_3759, A_3758) | ~v7_waybel_0(B_3759) | ~v4_orders_2(B_3759) | v2_struct_0(B_3759) | ~l1_pre_topc(A_3758) | ~v2_pre_topc(A_3758) | v2_struct_0(A_3758))), inference(resolution, [status(thm)], [c_6489, c_30])).
% 11.67/4.31  tff(c_6538, plain, (![A_63, B_3759, B_67]: (v4_orders_2('#skF_2'(A_63, B_3759, '#skF_3'(A_63, B_67))) | ~l1_struct_0(A_63) | ~r3_waybel_9(A_63, B_3759, '#skF_3'(A_63, B_67)) | ~l1_waybel_0(B_3759, A_63) | ~v7_waybel_0(B_3759) | ~v4_orders_2(B_3759) | v2_struct_0(B_3759) | ~l1_waybel_0(B_67, A_63) | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1(A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_48, c_6529])).
% 11.67/4.31  tff(c_28, plain, (![C_23, A_20, B_21]: (v7_waybel_0(C_23) | ~m2_yellow_6(C_23, A_20, B_21) | ~l1_waybel_0(B_21, A_20) | ~v7_waybel_0(B_21) | ~v4_orders_2(B_21) | v2_struct_0(B_21) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.67/4.31  tff(c_6563, plain, (![A_3765, B_3766, C_3767]: (v7_waybel_0('#skF_2'(A_3765, B_3766, C_3767)) | ~l1_struct_0(A_3765) | ~r3_waybel_9(A_3765, B_3766, C_3767) | ~m1_subset_1(C_3767, u1_struct_0(A_3765)) | ~l1_waybel_0(B_3766, A_3765) | ~v7_waybel_0(B_3766) | ~v4_orders_2(B_3766) | v2_struct_0(B_3766) | ~l1_pre_topc(A_3765) | ~v2_pre_topc(A_3765) | v2_struct_0(A_3765))), inference(resolution, [status(thm)], [c_6489, c_28])).
% 11.67/4.31  tff(c_6572, plain, (![A_63, B_3766, B_67]: (v7_waybel_0('#skF_2'(A_63, B_3766, '#skF_3'(A_63, B_67))) | ~l1_struct_0(A_63) | ~r3_waybel_9(A_63, B_3766, '#skF_3'(A_63, B_67)) | ~l1_waybel_0(B_3766, A_63) | ~v7_waybel_0(B_3766) | ~v4_orders_2(B_3766) | v2_struct_0(B_3766) | ~l1_waybel_0(B_67, A_63) | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1(A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63) | v2_struct_0(A_63))), inference(resolution, [status(thm)], [c_48, c_6563])).
% 11.67/4.31  tff(c_6706, plain, (![B_3822]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3822)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3822))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3822))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3822))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3822)) | ~l1_waybel_0(B_3822, '#skF_6') | ~v7_waybel_0(B_3822) | ~v4_orders_2(B_3822) | v2_struct_0(B_3822))), inference(splitRight, [status(thm)], [c_6641])).
% 11.67/4.31  tff(c_6710, plain, (![B_67]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)))=k1_xboole_0 | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_6572, c_6706])).
% 11.67/4.31  tff(c_6713, plain, (![B_67]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)))=k1_xboole_0 | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6352, c_6354, c_6357, c_6359, c_6705, c_6710])).
% 11.67/4.31  tff(c_6715, plain, (![B_3823]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3823)))=k1_xboole_0 | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3823))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3823))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3823)) | ~l1_waybel_0(B_3823, '#skF_6') | ~v7_waybel_0(B_3823) | ~v4_orders_2(B_3823) | v2_struct_0(B_3823))), inference(negUnitSimplification, [status(thm)], [c_70, c_6351, c_6713])).
% 11.67/4.31  tff(c_6719, plain, (![B_67]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)))=k1_xboole_0 | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_6538, c_6715])).
% 11.67/4.31  tff(c_6722, plain, (![B_67]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)))=k1_xboole_0 | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6352, c_6354, c_6357, c_6359, c_6705, c_6719])).
% 11.67/4.31  tff(c_6724, plain, (![B_3824]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3824)))=k1_xboole_0 | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3824))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3824)) | ~l1_waybel_0(B_3824, '#skF_6') | ~v7_waybel_0(B_3824) | ~v4_orders_2(B_3824) | v2_struct_0(B_3824))), inference(negUnitSimplification, [status(thm)], [c_70, c_6351, c_6722])).
% 11.67/4.31  tff(c_32, plain, (![C_23, A_20, B_21]: (~v2_struct_0(C_23) | ~m2_yellow_6(C_23, A_20, B_21) | ~l1_waybel_0(B_21, A_20) | ~v7_waybel_0(B_21) | ~v4_orders_2(B_21) | v2_struct_0(B_21) | ~l1_struct_0(A_20) | v2_struct_0(A_20))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.67/4.31  tff(c_6507, plain, (![A_3750, B_3751, C_3752]: (~v2_struct_0('#skF_2'(A_3750, B_3751, C_3752)) | ~l1_struct_0(A_3750) | ~r3_waybel_9(A_3750, B_3751, C_3752) | ~m1_subset_1(C_3752, u1_struct_0(A_3750)) | ~l1_waybel_0(B_3751, A_3750) | ~v7_waybel_0(B_3751) | ~v4_orders_2(B_3751) | v2_struct_0(B_3751) | ~l1_pre_topc(A_3750) | ~v2_pre_topc(A_3750) | v2_struct_0(A_3750))), inference(resolution, [status(thm)], [c_6489, c_32])).
% 11.67/4.31  tff(c_6726, plain, (![B_3824]: (~l1_struct_0('#skF_6') | ~m1_subset_1('#skF_3'('#skF_6', B_3824), u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3824)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3824)) | ~l1_waybel_0(B_3824, '#skF_6') | ~v7_waybel_0(B_3824) | ~v4_orders_2(B_3824) | v2_struct_0(B_3824))), inference(resolution, [status(thm)], [c_6724, c_6507])).
% 11.67/4.31  tff(c_6729, plain, (![B_3824]: (~m1_subset_1('#skF_3'('#skF_6', B_3824), u1_struct_0('#skF_6')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3824)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3824)) | ~l1_waybel_0(B_3824, '#skF_6') | ~v7_waybel_0(B_3824) | ~v4_orders_2(B_3824) | v2_struct_0(B_3824))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6354, c_6357, c_6359, c_6705, c_6726])).
% 11.67/4.31  tff(c_6735, plain, (![B_3828]: (~m1_subset_1('#skF_3'('#skF_6', B_3828), u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3828)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3828)) | ~l1_waybel_0(B_3828, '#skF_6') | ~v7_waybel_0(B_3828) | ~v4_orders_2(B_3828) | v2_struct_0(B_3828))), inference(negUnitSimplification, [status(thm)], [c_70, c_6351, c_6729])).
% 11.67/4.31  tff(c_6739, plain, (![B_67]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_6735])).
% 11.67/4.31  tff(c_6742, plain, (![B_67]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6352, c_6739])).
% 11.67/4.31  tff(c_6744, plain, (![B_3829]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3829)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3829)) | ~l1_waybel_0(B_3829, '#skF_6') | ~v7_waybel_0(B_3829) | ~v4_orders_2(B_3829) | v2_struct_0(B_3829))), inference(negUnitSimplification, [status(thm)], [c_70, c_6742])).
% 11.67/4.31  tff(c_6574, plain, (![C_3768, A_3769, B_3770]: (r2_hidden(C_3768, k10_yellow_6(A_3769, '#skF_2'(A_3769, B_3770, C_3768))) | ~r3_waybel_9(A_3769, B_3770, C_3768) | ~m1_subset_1(C_3768, u1_struct_0(A_3769)) | ~l1_waybel_0(B_3770, A_3769) | ~v7_waybel_0(B_3770) | ~v4_orders_2(B_3770) | v2_struct_0(B_3770) | ~l1_pre_topc(A_3769) | ~v2_pre_topc(A_3769) | v2_struct_0(A_3769))), inference(cnfTransformation, [status(thm)], [f_210])).
% 11.67/4.31  tff(c_20, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.67/4.31  tff(c_6586, plain, (![A_3769, B_3770, C_3768]: (~r1_tarski(k10_yellow_6(A_3769, '#skF_2'(A_3769, B_3770, C_3768)), C_3768) | ~r3_waybel_9(A_3769, B_3770, C_3768) | ~m1_subset_1(C_3768, u1_struct_0(A_3769)) | ~l1_waybel_0(B_3770, A_3769) | ~v7_waybel_0(B_3770) | ~v4_orders_2(B_3770) | v2_struct_0(B_3770) | ~l1_pre_topc(A_3769) | ~v2_pre_topc(A_3769) | v2_struct_0(A_3769))), inference(resolution, [status(thm)], [c_6574, c_20])).
% 11.67/4.31  tff(c_6756, plain, (![B_3829]: (~r1_tarski(k1_xboole_0, '#skF_3'('#skF_6', B_3829)) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3829)) | ~m1_subset_1('#skF_3'('#skF_6', B_3829), u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3829)) | ~l1_waybel_0(B_3829, '#skF_6') | ~v7_waybel_0(B_3829) | ~v4_orders_2(B_3829) | v2_struct_0(B_3829))), inference(superposition, [status(thm), theory('equality')], [c_6744, c_6586])).
% 11.67/4.31  tff(c_6780, plain, (![B_3829]: (~m1_subset_1('#skF_3'('#skF_6', B_3829), u1_struct_0('#skF_6')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3829)) | ~l1_waybel_0(B_3829, '#skF_6') | ~v7_waybel_0(B_3829) | ~v4_orders_2(B_3829) | v2_struct_0(B_3829))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6354, c_6357, c_6359, c_8, c_6756])).
% 11.67/4.31  tff(c_6795, plain, (![B_3830]: (~m1_subset_1('#skF_3'('#skF_6', B_3830), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3830)) | ~l1_waybel_0(B_3830, '#skF_6') | ~v7_waybel_0(B_3830) | ~v4_orders_2(B_3830) | v2_struct_0(B_3830))), inference(negUnitSimplification, [status(thm)], [c_70, c_6351, c_6780])).
% 11.67/4.31  tff(c_6799, plain, (![B_67]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_6795])).
% 11.67/4.31  tff(c_6802, plain, (![B_67]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_67)) | ~l1_waybel_0(B_67, '#skF_6') | ~v7_waybel_0(B_67) | ~v4_orders_2(B_67) | v2_struct_0(B_67) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6352, c_6799])).
% 11.67/4.31  tff(c_6804, plain, (![B_3831]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_3831)) | ~l1_waybel_0(B_3831, '#skF_6') | ~v7_waybel_0(B_3831) | ~v4_orders_2(B_3831) | v2_struct_0(B_3831))), inference(negUnitSimplification, [status(thm)], [c_70, c_6802])).
% 11.67/4.31  tff(c_6812, plain, (~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_46, c_6804])).
% 11.67/4.31  tff(c_6819, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_6352, c_6354, c_6357, c_6359, c_6812])).
% 11.67/4.31  tff(c_6821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_6351, c_6819])).
% 11.67/4.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.67/4.31  
% 11.67/4.31  Inference rules
% 11.67/4.31  ----------------------
% 11.67/4.31  #Ref     : 0
% 11.91/4.31  #Sup     : 1406
% 11.91/4.31  #Fact    : 8
% 11.91/4.31  #Define  : 0
% 11.91/4.31  #Split   : 44
% 11.91/4.31  #Chain   : 0
% 11.91/4.31  #Close   : 0
% 11.91/4.31  
% 11.91/4.31  Ordering : KBO
% 11.91/4.31  
% 11.91/4.31  Simplification rules
% 11.91/4.31  ----------------------
% 11.91/4.31  #Subsume      : 608
% 11.91/4.31  #Demod        : 494
% 11.91/4.31  #Tautology    : 120
% 11.91/4.31  #SimpNegUnit  : 75
% 11.91/4.31  #BackRed      : 2
% 11.91/4.31  
% 11.91/4.31  #Partial instantiations: 2340
% 11.91/4.31  #Strategies tried      : 1
% 11.91/4.31  
% 11.91/4.31  Timing (in seconds)
% 11.91/4.31  ----------------------
% 11.91/4.31  Preprocessing        : 0.37
% 11.91/4.31  Parsing              : 0.20
% 11.91/4.31  CNF conversion       : 0.03
% 11.91/4.31  Main loop            : 3.12
% 11.91/4.31  Inferencing          : 0.78
% 11.91/4.31  Reduction            : 0.50
% 11.91/4.31  Demodulation         : 0.34
% 11.91/4.31  BG Simplification    : 0.08
% 11.91/4.32  Subsumption          : 1.67
% 11.91/4.32  Abstraction          : 0.09
% 11.91/4.32  MUC search           : 0.00
% 11.91/4.32  Cooper               : 0.00
% 11.91/4.32  Total                : 3.57
% 11.91/4.32  Index Insertion      : 0.00
% 11.91/4.32  Index Deletion       : 0.00
% 11.91/4.32  Index Matching       : 0.00
% 11.91/4.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
