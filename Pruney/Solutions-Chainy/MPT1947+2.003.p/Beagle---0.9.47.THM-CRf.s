%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:54 EST 2020

% Result     : Theorem 9.85s
% Output     : CNFRefutation 9.85s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 352 expanded)
%              Number of leaves         :   40 ( 148 expanded)
%              Depth                    :   18
%              Number of atoms          :  335 (1705 expanded)
%              Number of equality atoms :   22 ( 146 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_yellow_6 > v1_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_waybel_0 > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_waybel_0,type,(
    k2_waybel_0: ( $i * $i * $i ) > $i )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v1_yellow_6,type,(
    v1_yellow_6: ( $i * $i ) > $o )).

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

tff(k11_yellow_6,type,(
    k11_yellow_6: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_206,negated_conjecture,(
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

tff(f_111,axiom,(
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

tff(f_69,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_161,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & l1_waybel_0(B,A)
        & m1_subset_1(C,u1_struct_0(B)) )
     => m1_subset_1(k2_waybel_0(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_waybel_0)).

tff(f_182,axiom,(
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

tff(f_139,axiom,(
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

tff(f_46,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_65,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_62,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_48,plain,(
    l1_waybel_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_54,plain,(
    v4_orders_2('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_52,plain,(
    v7_waybel_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_50,plain,(
    v1_yellow_6('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_30,plain,(
    ! [B_23,A_21] :
      ( v3_yellow_6(B_23,A_21)
      | ~ v1_yellow_6(B_23,A_21)
      | ~ v7_waybel_0(B_23)
      | ~ v4_orders_2(B_23)
      | v2_struct_0(B_23)
      | ~ l1_waybel_0(B_23,A_21)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_46,plain,(
    k4_yellow_6('#skF_2','#skF_3') != k11_yellow_6('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_60,plain,(
    v8_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_26,plain,(
    ! [A_17] :
      ( l1_struct_0(A_17)
      | ~ l1_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_341,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_waybel_0(A_101,B_102,C_103) = k4_yellow_6(A_101,B_102)
      | ~ m1_subset_1(C_103,u1_struct_0(B_102))
      | ~ l1_waybel_0(B_102,A_101)
      | ~ v1_yellow_6(B_102,A_101)
      | ~ v7_waybel_0(B_102)
      | ~ v4_orders_2(B_102)
      | v2_struct_0(B_102)
      | ~ l1_struct_0(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1159,plain,(
    ! [A_179,B_180,B_181] :
      ( k2_waybel_0(A_179,B_180,B_181) = k4_yellow_6(A_179,B_180)
      | ~ l1_waybel_0(B_180,A_179)
      | ~ v1_yellow_6(B_180,A_179)
      | ~ v7_waybel_0(B_180)
      | ~ v4_orders_2(B_180)
      | v2_struct_0(B_180)
      | ~ l1_struct_0(A_179)
      | v2_struct_0(A_179)
      | ~ v1_xboole_0(B_181)
      | ~ v1_xboole_0(u1_struct_0(B_180)) ) ),
    inference(resolution,[status(thm)],[c_10,c_341])).

tff(c_1161,plain,(
    ! [B_181] :
      ( k2_waybel_0('#skF_2','#skF_3',B_181) = k4_yellow_6('#skF_2','#skF_3')
      | ~ l1_waybel_0('#skF_3','#skF_2')
      | ~ v7_waybel_0('#skF_3')
      | ~ v4_orders_2('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_xboole_0(B_181)
      | ~ v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_50,c_1159])).

tff(c_1164,plain,(
    ! [B_181] :
      ( k2_waybel_0('#skF_2','#skF_3',B_181) = k4_yellow_6('#skF_2','#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_struct_0('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ v1_xboole_0(B_181)
      | ~ v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_48,c_1161])).

tff(c_1165,plain,(
    ! [B_181] :
      ( k2_waybel_0('#skF_2','#skF_3',B_181) = k4_yellow_6('#skF_2','#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ v1_xboole_0(B_181)
      | ~ v1_xboole_0(u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_1164])).

tff(c_1166,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1165])).

tff(c_70,plain,(
    ! [A_50] :
      ( v1_xboole_0(A_50)
      | r2_hidden('#skF_1'(A_50),A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_80,plain,(
    ! [A_50] :
      ( m1_subset_1('#skF_1'(A_50),A_50)
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_70,c_16])).

tff(c_1461,plain,(
    ! [A_211,B_212] :
      ( k2_waybel_0(A_211,B_212,'#skF_1'(u1_struct_0(B_212))) = k4_yellow_6(A_211,B_212)
      | ~ l1_waybel_0(B_212,A_211)
      | ~ v1_yellow_6(B_212,A_211)
      | ~ v7_waybel_0(B_212)
      | ~ v4_orders_2(B_212)
      | v2_struct_0(B_212)
      | ~ l1_struct_0(A_211)
      | v2_struct_0(A_211)
      | v1_xboole_0(u1_struct_0(B_212)) ) ),
    inference(resolution,[status(thm)],[c_80,c_341])).

tff(c_28,plain,(
    ! [A_18,B_19,C_20] :
      ( m1_subset_1(k2_waybel_0(A_18,B_19,C_20),u1_struct_0(A_18))
      | ~ m1_subset_1(C_20,u1_struct_0(B_19))
      | ~ l1_waybel_0(B_19,A_18)
      | v2_struct_0(B_19)
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6185,plain,(
    ! [A_418,B_419] :
      ( m1_subset_1(k4_yellow_6(A_418,B_419),u1_struct_0(A_418))
      | ~ m1_subset_1('#skF_1'(u1_struct_0(B_419)),u1_struct_0(B_419))
      | ~ l1_waybel_0(B_419,A_418)
      | v2_struct_0(B_419)
      | ~ l1_struct_0(A_418)
      | v2_struct_0(A_418)
      | ~ l1_waybel_0(B_419,A_418)
      | ~ v1_yellow_6(B_419,A_418)
      | ~ v7_waybel_0(B_419)
      | ~ v4_orders_2(B_419)
      | v2_struct_0(B_419)
      | ~ l1_struct_0(A_418)
      | v2_struct_0(A_418)
      | v1_xboole_0(u1_struct_0(B_419)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1461,c_28])).

tff(c_6198,plain,(
    ! [A_420,B_421] :
      ( m1_subset_1(k4_yellow_6(A_420,B_421),u1_struct_0(A_420))
      | ~ l1_waybel_0(B_421,A_420)
      | ~ v1_yellow_6(B_421,A_420)
      | ~ v7_waybel_0(B_421)
      | ~ v4_orders_2(B_421)
      | v2_struct_0(B_421)
      | ~ l1_struct_0(A_420)
      | v2_struct_0(A_420)
      | v1_xboole_0(u1_struct_0(B_421)) ) ),
    inference(resolution,[status(thm)],[c_80,c_6185])).

tff(c_44,plain,(
    ! [A_38,B_40] :
      ( r2_hidden(k4_yellow_6(A_38,B_40),k10_yellow_6(A_38,B_40))
      | ~ l1_waybel_0(B_40,A_38)
      | ~ v1_yellow_6(B_40,A_38)
      | ~ v7_waybel_0(B_40)
      | ~ v4_orders_2(B_40)
      | v2_struct_0(B_40)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_450,plain,(
    ! [A_114,B_115,C_116] :
      ( k11_yellow_6(A_114,B_115) = C_116
      | ~ r2_hidden(C_116,k10_yellow_6(A_114,B_115))
      | ~ m1_subset_1(C_116,u1_struct_0(A_114))
      | ~ l1_waybel_0(B_115,A_114)
      | ~ v3_yellow_6(B_115,A_114)
      | ~ v7_waybel_0(B_115)
      | ~ v4_orders_2(B_115)
      | v2_struct_0(B_115)
      | ~ l1_pre_topc(A_114)
      | ~ v8_pre_topc(A_114)
      | ~ v2_pre_topc(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_462,plain,(
    ! [A_38,B_40] :
      ( k4_yellow_6(A_38,B_40) = k11_yellow_6(A_38,B_40)
      | ~ m1_subset_1(k4_yellow_6(A_38,B_40),u1_struct_0(A_38))
      | ~ v3_yellow_6(B_40,A_38)
      | ~ v8_pre_topc(A_38)
      | ~ l1_waybel_0(B_40,A_38)
      | ~ v1_yellow_6(B_40,A_38)
      | ~ v7_waybel_0(B_40)
      | ~ v4_orders_2(B_40)
      | v2_struct_0(B_40)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_44,c_450])).

tff(c_6299,plain,(
    ! [A_426,B_427] :
      ( k4_yellow_6(A_426,B_427) = k11_yellow_6(A_426,B_427)
      | ~ v3_yellow_6(B_427,A_426)
      | ~ v8_pre_topc(A_426)
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | ~ l1_waybel_0(B_427,A_426)
      | ~ v1_yellow_6(B_427,A_426)
      | ~ v7_waybel_0(B_427)
      | ~ v4_orders_2(B_427)
      | v2_struct_0(B_427)
      | ~ l1_struct_0(A_426)
      | v2_struct_0(A_426)
      | v1_xboole_0(u1_struct_0(B_427)) ) ),
    inference(resolution,[status(thm)],[c_6198,c_462])).

tff(c_6303,plain,(
    ! [A_428,B_429] :
      ( k4_yellow_6(A_428,B_429) = k11_yellow_6(A_428,B_429)
      | ~ v8_pre_topc(A_428)
      | ~ l1_struct_0(A_428)
      | v1_xboole_0(u1_struct_0(B_429))
      | ~ v1_yellow_6(B_429,A_428)
      | ~ v7_waybel_0(B_429)
      | ~ v4_orders_2(B_429)
      | v2_struct_0(B_429)
      | ~ l1_waybel_0(B_429,A_428)
      | ~ l1_pre_topc(A_428)
      | ~ v2_pre_topc(A_428)
      | v2_struct_0(A_428) ) ),
    inference(resolution,[status(thm)],[c_30,c_6299])).

tff(c_6305,plain,
    ( k4_yellow_6('#skF_2','#skF_3') = k11_yellow_6('#skF_2','#skF_3')
    | ~ v8_pre_topc('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_6303])).

tff(c_6308,plain,
    ( k4_yellow_6('#skF_2','#skF_3') = k11_yellow_6('#skF_2','#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_48,c_54,c_52,c_60,c_6305])).

tff(c_6309,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_1166,c_46,c_6308])).

tff(c_6312,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_6309])).

tff(c_6316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6312])).

tff(c_6318,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1165])).

tff(c_14,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_101,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_117,plain,(
    ! [A_60] : r1_tarski(k1_xboole_0,A_60) ),
    inference(resolution,[status(thm)],[c_14,c_101])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( ~ r1_tarski(B_16,A_15)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_81,plain,(
    ! [A_50] :
      ( ~ r1_tarski(A_50,'#skF_1'(A_50))
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_70,c_24])).

tff(c_122,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_117,c_81])).

tff(c_6317,plain,(
    ! [B_181] :
      ( ~ l1_struct_0('#skF_2')
      | k2_waybel_0('#skF_2','#skF_3',B_181) = k4_yellow_6('#skF_2','#skF_3')
      | ~ v1_xboole_0(B_181) ) ),
    inference(splitRight,[status(thm)],[c_1165])).

tff(c_6319,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_6317])).

tff(c_6327,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_6319])).

tff(c_6331,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6327])).

tff(c_6333,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6317])).

tff(c_6334,plain,(
    ! [B_432] :
      ( k2_waybel_0('#skF_2','#skF_3',B_432) = k4_yellow_6('#skF_2','#skF_3')
      | ~ v1_xboole_0(B_432) ) ),
    inference(splitRight,[status(thm)],[c_6317])).

tff(c_6366,plain,(
    k2_waybel_0('#skF_2','#skF_3',k1_xboole_0) = k4_yellow_6('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_122,c_6334])).

tff(c_6389,plain,
    ( m1_subset_1(k4_yellow_6('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_3'))
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6366,c_28])).

tff(c_6396,plain,
    ( m1_subset_1(k4_yellow_6('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6333,c_48,c_6389])).

tff(c_6397,plain,
    ( m1_subset_1(k4_yellow_6('#skF_2','#skF_3'),u1_struct_0('#skF_2'))
    | ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_6396])).

tff(c_6400,plain,(
    ~ m1_subset_1(k1_xboole_0,u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6397])).

tff(c_6408,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_6400])).

tff(c_6412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6318,c_122,c_6408])).

tff(c_6413,plain,(
    m1_subset_1(k4_yellow_6('#skF_2','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6397])).

tff(c_6925,plain,(
    ! [A_476,B_477] :
      ( k4_yellow_6(A_476,B_477) = k11_yellow_6(A_476,B_477)
      | ~ m1_subset_1(k4_yellow_6(A_476,B_477),u1_struct_0(A_476))
      | ~ v3_yellow_6(B_477,A_476)
      | ~ v8_pre_topc(A_476)
      | ~ l1_waybel_0(B_477,A_476)
      | ~ v1_yellow_6(B_477,A_476)
      | ~ v7_waybel_0(B_477)
      | ~ v4_orders_2(B_477)
      | v2_struct_0(B_477)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(resolution,[status(thm)],[c_44,c_450])).

tff(c_6928,plain,
    ( k4_yellow_6('#skF_2','#skF_3') = k11_yellow_6('#skF_2','#skF_3')
    | ~ v3_yellow_6('#skF_3','#skF_2')
    | ~ v8_pre_topc('#skF_2')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ v1_yellow_6('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_6413,c_6925])).

tff(c_6934,plain,
    ( k4_yellow_6('#skF_2','#skF_3') = k11_yellow_6('#skF_2','#skF_3')
    | ~ v3_yellow_6('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_54,c_52,c_50,c_48,c_60,c_6928])).

tff(c_6935,plain,(
    ~ v3_yellow_6('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_46,c_6934])).

tff(c_6939,plain,
    ( ~ v1_yellow_6('#skF_3','#skF_2')
    | ~ v7_waybel_0('#skF_3')
    | ~ v4_orders_2('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_waybel_0('#skF_3','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_6935])).

tff(c_6942,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_58,c_48,c_54,c_52,c_50,c_6939])).

tff(c_6944,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_56,c_6942])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.85/3.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.85/3.75  
% 9.85/3.75  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.85/3.75  %$ v3_yellow_6 > v1_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v8_pre_topc > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k2_waybel_0 > k4_yellow_6 > k11_yellow_6 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 9.85/3.75  
% 9.85/3.75  %Foreground sorts:
% 9.85/3.75  
% 9.85/3.75  
% 9.85/3.75  %Background operators:
% 9.85/3.75  
% 9.85/3.75  
% 9.85/3.75  %Foreground operators:
% 9.85/3.75  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 9.85/3.75  tff(v8_pre_topc, type, v8_pre_topc: $i > $o).
% 9.85/3.75  tff(k4_yellow_6, type, k4_yellow_6: ($i * $i) > $i).
% 9.85/3.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.85/3.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.85/3.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 9.85/3.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.85/3.75  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 9.85/3.75  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 9.85/3.75  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 9.85/3.75  tff(k2_waybel_0, type, k2_waybel_0: ($i * $i * $i) > $i).
% 9.85/3.75  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 9.85/3.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.85/3.75  tff('#skF_2', type, '#skF_2': $i).
% 9.85/3.75  tff('#skF_3', type, '#skF_3': $i).
% 9.85/3.75  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 9.85/3.75  tff(v1_yellow_6, type, v1_yellow_6: ($i * $i) > $o).
% 9.85/3.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.85/3.75  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 9.85/3.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.85/3.75  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 9.85/3.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.85/3.75  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 9.85/3.75  tff(k11_yellow_6, type, k11_yellow_6: ($i * $i) > $i).
% 9.85/3.75  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 9.85/3.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.85/3.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.85/3.75  
% 9.85/3.77  tff(f_206, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (k11_yellow_6(A, B) = k4_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_yellow_6)).
% 9.85/3.77  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (l1_waybel_0(B, A) => ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) => (((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_yellow_6)).
% 9.85/3.77  tff(f_69, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 9.85/3.77  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 9.85/3.77  tff(f_161, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(B)) => (k2_waybel_0(A, B, C) = k4_yellow_6(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_6)).
% 9.85/3.77  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 9.85/3.77  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 9.85/3.77  tff(f_83, axiom, (![A, B, C]: (((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & l1_waybel_0(B, A)) & m1_subset_1(C, u1_struct_0(B))) => m1_subset_1(k2_waybel_0(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_waybel_0)).
% 9.85/3.77  tff(f_182, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v1_yellow_6(B, A)) & l1_waybel_0(B, A)) => r2_hidden(k4_yellow_6(A, B), k10_yellow_6(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_yellow_6)).
% 9.85/3.77  tff(f_139, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v8_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & v3_yellow_6(B, A)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((C = k11_yellow_6(A, B)) <=> r2_hidden(C, k10_yellow_6(A, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_yellow_6)).
% 9.85/3.77  tff(f_46, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.85/3.77  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.85/3.77  tff(f_65, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.85/3.77  tff(c_64, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_62, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_48, plain, (l1_waybel_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_54, plain, (v4_orders_2('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_52, plain, (v7_waybel_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_50, plain, (v1_yellow_6('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_30, plain, (![B_23, A_21]: (v3_yellow_6(B_23, A_21) | ~v1_yellow_6(B_23, A_21) | ~v7_waybel_0(B_23) | ~v4_orders_2(B_23) | v2_struct_0(B_23) | ~l1_waybel_0(B_23, A_21) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_111])).
% 9.85/3.77  tff(c_46, plain, (k4_yellow_6('#skF_2', '#skF_3')!=k11_yellow_6('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_60, plain, (v8_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_206])).
% 9.85/3.77  tff(c_26, plain, (![A_17]: (l1_struct_0(A_17) | ~l1_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.85/3.77  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.85/3.77  tff(c_341, plain, (![A_101, B_102, C_103]: (k2_waybel_0(A_101, B_102, C_103)=k4_yellow_6(A_101, B_102) | ~m1_subset_1(C_103, u1_struct_0(B_102)) | ~l1_waybel_0(B_102, A_101) | ~v1_yellow_6(B_102, A_101) | ~v7_waybel_0(B_102) | ~v4_orders_2(B_102) | v2_struct_0(B_102) | ~l1_struct_0(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_161])).
% 9.85/3.77  tff(c_1159, plain, (![A_179, B_180, B_181]: (k2_waybel_0(A_179, B_180, B_181)=k4_yellow_6(A_179, B_180) | ~l1_waybel_0(B_180, A_179) | ~v1_yellow_6(B_180, A_179) | ~v7_waybel_0(B_180) | ~v4_orders_2(B_180) | v2_struct_0(B_180) | ~l1_struct_0(A_179) | v2_struct_0(A_179) | ~v1_xboole_0(B_181) | ~v1_xboole_0(u1_struct_0(B_180)))), inference(resolution, [status(thm)], [c_10, c_341])).
% 9.85/3.77  tff(c_1161, plain, (![B_181]: (k2_waybel_0('#skF_2', '#skF_3', B_181)=k4_yellow_6('#skF_2', '#skF_3') | ~l1_waybel_0('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~v1_xboole_0(B_181) | ~v1_xboole_0(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_50, c_1159])).
% 9.85/3.77  tff(c_1164, plain, (![B_181]: (k2_waybel_0('#skF_2', '#skF_3', B_181)=k4_yellow_6('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~v1_xboole_0(B_181) | ~v1_xboole_0(u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_48, c_1161])).
% 9.85/3.77  tff(c_1165, plain, (![B_181]: (k2_waybel_0('#skF_2', '#skF_3', B_181)=k4_yellow_6('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~v1_xboole_0(B_181) | ~v1_xboole_0(u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_1164])).
% 9.85/3.77  tff(c_1166, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_1165])).
% 9.85/3.77  tff(c_70, plain, (![A_50]: (v1_xboole_0(A_50) | r2_hidden('#skF_1'(A_50), A_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.85/3.77  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(A_8, B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.85/3.77  tff(c_80, plain, (![A_50]: (m1_subset_1('#skF_1'(A_50), A_50) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_70, c_16])).
% 9.85/3.77  tff(c_1461, plain, (![A_211, B_212]: (k2_waybel_0(A_211, B_212, '#skF_1'(u1_struct_0(B_212)))=k4_yellow_6(A_211, B_212) | ~l1_waybel_0(B_212, A_211) | ~v1_yellow_6(B_212, A_211) | ~v7_waybel_0(B_212) | ~v4_orders_2(B_212) | v2_struct_0(B_212) | ~l1_struct_0(A_211) | v2_struct_0(A_211) | v1_xboole_0(u1_struct_0(B_212)))), inference(resolution, [status(thm)], [c_80, c_341])).
% 9.85/3.77  tff(c_28, plain, (![A_18, B_19, C_20]: (m1_subset_1(k2_waybel_0(A_18, B_19, C_20), u1_struct_0(A_18)) | ~m1_subset_1(C_20, u1_struct_0(B_19)) | ~l1_waybel_0(B_19, A_18) | v2_struct_0(B_19) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.85/3.77  tff(c_6185, plain, (![A_418, B_419]: (m1_subset_1(k4_yellow_6(A_418, B_419), u1_struct_0(A_418)) | ~m1_subset_1('#skF_1'(u1_struct_0(B_419)), u1_struct_0(B_419)) | ~l1_waybel_0(B_419, A_418) | v2_struct_0(B_419) | ~l1_struct_0(A_418) | v2_struct_0(A_418) | ~l1_waybel_0(B_419, A_418) | ~v1_yellow_6(B_419, A_418) | ~v7_waybel_0(B_419) | ~v4_orders_2(B_419) | v2_struct_0(B_419) | ~l1_struct_0(A_418) | v2_struct_0(A_418) | v1_xboole_0(u1_struct_0(B_419)))), inference(superposition, [status(thm), theory('equality')], [c_1461, c_28])).
% 9.85/3.77  tff(c_6198, plain, (![A_420, B_421]: (m1_subset_1(k4_yellow_6(A_420, B_421), u1_struct_0(A_420)) | ~l1_waybel_0(B_421, A_420) | ~v1_yellow_6(B_421, A_420) | ~v7_waybel_0(B_421) | ~v4_orders_2(B_421) | v2_struct_0(B_421) | ~l1_struct_0(A_420) | v2_struct_0(A_420) | v1_xboole_0(u1_struct_0(B_421)))), inference(resolution, [status(thm)], [c_80, c_6185])).
% 9.85/3.77  tff(c_44, plain, (![A_38, B_40]: (r2_hidden(k4_yellow_6(A_38, B_40), k10_yellow_6(A_38, B_40)) | ~l1_waybel_0(B_40, A_38) | ~v1_yellow_6(B_40, A_38) | ~v7_waybel_0(B_40) | ~v4_orders_2(B_40) | v2_struct_0(B_40) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_182])).
% 9.85/3.77  tff(c_450, plain, (![A_114, B_115, C_116]: (k11_yellow_6(A_114, B_115)=C_116 | ~r2_hidden(C_116, k10_yellow_6(A_114, B_115)) | ~m1_subset_1(C_116, u1_struct_0(A_114)) | ~l1_waybel_0(B_115, A_114) | ~v3_yellow_6(B_115, A_114) | ~v7_waybel_0(B_115) | ~v4_orders_2(B_115) | v2_struct_0(B_115) | ~l1_pre_topc(A_114) | ~v8_pre_topc(A_114) | ~v2_pre_topc(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_139])).
% 9.85/3.77  tff(c_462, plain, (![A_38, B_40]: (k4_yellow_6(A_38, B_40)=k11_yellow_6(A_38, B_40) | ~m1_subset_1(k4_yellow_6(A_38, B_40), u1_struct_0(A_38)) | ~v3_yellow_6(B_40, A_38) | ~v8_pre_topc(A_38) | ~l1_waybel_0(B_40, A_38) | ~v1_yellow_6(B_40, A_38) | ~v7_waybel_0(B_40) | ~v4_orders_2(B_40) | v2_struct_0(B_40) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(resolution, [status(thm)], [c_44, c_450])).
% 9.85/3.77  tff(c_6299, plain, (![A_426, B_427]: (k4_yellow_6(A_426, B_427)=k11_yellow_6(A_426, B_427) | ~v3_yellow_6(B_427, A_426) | ~v8_pre_topc(A_426) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | ~l1_waybel_0(B_427, A_426) | ~v1_yellow_6(B_427, A_426) | ~v7_waybel_0(B_427) | ~v4_orders_2(B_427) | v2_struct_0(B_427) | ~l1_struct_0(A_426) | v2_struct_0(A_426) | v1_xboole_0(u1_struct_0(B_427)))), inference(resolution, [status(thm)], [c_6198, c_462])).
% 9.85/3.77  tff(c_6303, plain, (![A_428, B_429]: (k4_yellow_6(A_428, B_429)=k11_yellow_6(A_428, B_429) | ~v8_pre_topc(A_428) | ~l1_struct_0(A_428) | v1_xboole_0(u1_struct_0(B_429)) | ~v1_yellow_6(B_429, A_428) | ~v7_waybel_0(B_429) | ~v4_orders_2(B_429) | v2_struct_0(B_429) | ~l1_waybel_0(B_429, A_428) | ~l1_pre_topc(A_428) | ~v2_pre_topc(A_428) | v2_struct_0(A_428))), inference(resolution, [status(thm)], [c_30, c_6299])).
% 9.85/3.77  tff(c_6305, plain, (k4_yellow_6('#skF_2', '#skF_3')=k11_yellow_6('#skF_2', '#skF_3') | ~v8_pre_topc('#skF_2') | ~l1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_3')) | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_50, c_6303])).
% 9.85/3.77  tff(c_6308, plain, (k4_yellow_6('#skF_2', '#skF_3')=k11_yellow_6('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_48, c_54, c_52, c_60, c_6305])).
% 9.85/3.77  tff(c_6309, plain, (~l1_struct_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_1166, c_46, c_6308])).
% 9.85/3.77  tff(c_6312, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_6309])).
% 9.85/3.77  tff(c_6316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_6312])).
% 9.85/3.77  tff(c_6318, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_1165])).
% 9.85/3.77  tff(c_14, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 9.85/3.77  tff(c_101, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.85/3.77  tff(c_117, plain, (![A_60]: (r1_tarski(k1_xboole_0, A_60))), inference(resolution, [status(thm)], [c_14, c_101])).
% 9.85/3.77  tff(c_24, plain, (![B_16, A_15]: (~r1_tarski(B_16, A_15) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.85/3.77  tff(c_81, plain, (![A_50]: (~r1_tarski(A_50, '#skF_1'(A_50)) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_70, c_24])).
% 9.85/3.77  tff(c_122, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_117, c_81])).
% 9.85/3.77  tff(c_6317, plain, (![B_181]: (~l1_struct_0('#skF_2') | k2_waybel_0('#skF_2', '#skF_3', B_181)=k4_yellow_6('#skF_2', '#skF_3') | ~v1_xboole_0(B_181))), inference(splitRight, [status(thm)], [c_1165])).
% 9.85/3.77  tff(c_6319, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_6317])).
% 9.85/3.77  tff(c_6327, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_26, c_6319])).
% 9.85/3.77  tff(c_6331, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_6327])).
% 9.85/3.77  tff(c_6333, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_6317])).
% 9.85/3.77  tff(c_6334, plain, (![B_432]: (k2_waybel_0('#skF_2', '#skF_3', B_432)=k4_yellow_6('#skF_2', '#skF_3') | ~v1_xboole_0(B_432))), inference(splitRight, [status(thm)], [c_6317])).
% 9.85/3.77  tff(c_6366, plain, (k2_waybel_0('#skF_2', '#skF_3', k1_xboole_0)=k4_yellow_6('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_122, c_6334])).
% 9.85/3.77  tff(c_6389, plain, (m1_subset_1(k4_yellow_6('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_3')) | ~l1_waybel_0('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6366, c_28])).
% 9.85/3.77  tff(c_6396, plain, (m1_subset_1(k4_yellow_6('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6333, c_48, c_6389])).
% 9.85/3.77  tff(c_6397, plain, (m1_subset_1(k4_yellow_6('#skF_2', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_6396])).
% 9.85/3.77  tff(c_6400, plain, (~m1_subset_1(k1_xboole_0, u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_6397])).
% 9.85/3.77  tff(c_6408, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_6400])).
% 9.85/3.77  tff(c_6412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6318, c_122, c_6408])).
% 9.85/3.77  tff(c_6413, plain, (m1_subset_1(k4_yellow_6('#skF_2', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_6397])).
% 9.85/3.77  tff(c_6925, plain, (![A_476, B_477]: (k4_yellow_6(A_476, B_477)=k11_yellow_6(A_476, B_477) | ~m1_subset_1(k4_yellow_6(A_476, B_477), u1_struct_0(A_476)) | ~v3_yellow_6(B_477, A_476) | ~v8_pre_topc(A_476) | ~l1_waybel_0(B_477, A_476) | ~v1_yellow_6(B_477, A_476) | ~v7_waybel_0(B_477) | ~v4_orders_2(B_477) | v2_struct_0(B_477) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(resolution, [status(thm)], [c_44, c_450])).
% 9.85/3.77  tff(c_6928, plain, (k4_yellow_6('#skF_2', '#skF_3')=k11_yellow_6('#skF_2', '#skF_3') | ~v3_yellow_6('#skF_3', '#skF_2') | ~v8_pre_topc('#skF_2') | ~l1_waybel_0('#skF_3', '#skF_2') | ~v1_yellow_6('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_6413, c_6925])).
% 9.85/3.77  tff(c_6934, plain, (k4_yellow_6('#skF_2', '#skF_3')=k11_yellow_6('#skF_2', '#skF_3') | ~v3_yellow_6('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_54, c_52, c_50, c_48, c_60, c_6928])).
% 9.85/3.77  tff(c_6935, plain, (~v3_yellow_6('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_46, c_6934])).
% 9.85/3.77  tff(c_6939, plain, (~v1_yellow_6('#skF_3', '#skF_2') | ~v7_waybel_0('#skF_3') | ~v4_orders_2('#skF_3') | v2_struct_0('#skF_3') | ~l1_waybel_0('#skF_3', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_6935])).
% 9.85/3.77  tff(c_6942, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_58, c_48, c_54, c_52, c_50, c_6939])).
% 9.85/3.77  tff(c_6944, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_56, c_6942])).
% 9.85/3.77  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.85/3.77  
% 9.85/3.77  Inference rules
% 9.85/3.77  ----------------------
% 9.85/3.77  #Ref     : 0
% 9.85/3.77  #Sup     : 1488
% 9.85/3.77  #Fact    : 0
% 9.85/3.77  #Define  : 0
% 9.85/3.77  #Split   : 7
% 9.85/3.77  #Chain   : 0
% 9.85/3.77  #Close   : 0
% 9.85/3.77  
% 9.85/3.77  Ordering : KBO
% 9.85/3.77  
% 9.85/3.77  Simplification rules
% 9.85/3.77  ----------------------
% 9.85/3.77  #Subsume      : 138
% 9.85/3.77  #Demod        : 150
% 9.85/3.77  #Tautology    : 126
% 9.85/3.77  #SimpNegUnit  : 33
% 9.85/3.77  #BackRed      : 0
% 9.85/3.77  
% 9.85/3.77  #Partial instantiations: 0
% 9.85/3.77  #Strategies tried      : 1
% 9.85/3.77  
% 9.85/3.77  Timing (in seconds)
% 9.85/3.77  ----------------------
% 9.85/3.78  Preprocessing        : 0.38
% 9.85/3.78  Parsing              : 0.21
% 9.85/3.78  CNF conversion       : 0.03
% 9.85/3.78  Main loop            : 2.56
% 9.85/3.78  Inferencing          : 0.52
% 9.85/3.78  Reduction            : 0.48
% 9.85/3.78  Demodulation         : 0.31
% 9.85/3.78  BG Simplification    : 0.08
% 9.85/3.78  Subsumption          : 1.33
% 9.85/3.78  Abstraction          : 0.10
% 9.85/3.78  MUC search           : 0.00
% 9.85/3.78  Cooper               : 0.00
% 9.85/3.78  Total                : 2.98
% 9.85/3.78  Index Insertion      : 0.00
% 9.85/3.78  Index Deletion       : 0.00
% 9.85/3.78  Index Matching       : 0.00
% 9.85/3.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
