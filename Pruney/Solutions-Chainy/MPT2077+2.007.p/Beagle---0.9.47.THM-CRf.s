%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:40 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 8.31s
% Verified   : 
% Statistics : Number of formulae       :  321 (10409 expanded)
%              Number of leaves         :   51 (3475 expanded)
%              Depth                    :   43
%              Number of atoms          : 1677 (72759 expanded)
%              Number of equality atoms :   62 ( 250 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_8 > #skF_4 > #skF_10 > #skF_2 > #skF_5 > #skF_9 > #skF_11 > #skF_3 > #skF_7 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_297,negated_conjecture,(
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

tff(f_272,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_127,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_101,axiom,(
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

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_219,axiom,(
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

tff(f_195,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r3_waybel_9(A,B,C)
              <=> ! [D] :
                    ( m1_connsp_2(D,A,C)
                   => r2_waybel_0(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_waybel_9)).

tff(f_150,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m2_yellow_6(C,A,B)
             => ! [D] :
                  ( r2_waybel_0(A,C,D)
                 => r2_waybel_0(A,B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_83,axiom,(
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

tff(f_47,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_172,axiom,(
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

tff(f_248,axiom,(
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

tff(c_84,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_94,plain,
    ( ~ v2_struct_0('#skF_10')
    | ~ v1_compts_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_122,plain,(
    ~ v1_compts_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_82,plain,(
    v2_pre_topc('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_80,plain,(
    l1_pre_topc('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_72,plain,(
    ! [A_165] :
      ( v4_orders_2('#skF_8'(A_165))
      | v1_compts_1(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_70,plain,(
    ! [A_165] :
      ( v7_waybel_0('#skF_8'(A_165))
      | v1_compts_1(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_68,plain,(
    ! [A_165] :
      ( l1_waybel_0('#skF_8'(A_165),A_165)
      | v1_compts_1(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_16,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_pre_topc(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,(
    ! [B_184] :
      ( v1_compts_1('#skF_9')
      | m2_yellow_6('#skF_11'(B_184),'#skF_9',B_184)
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_219,plain,(
    ! [B_184] :
      ( m2_yellow_6('#skF_11'(B_184),'#skF_9',B_184)
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_120])).

tff(c_223,plain,(
    ! [C_229,A_230,B_231] :
      ( v7_waybel_0(C_229)
      | ~ m2_yellow_6(C_229,A_230,B_231)
      | ~ l1_waybel_0(B_231,A_230)
      | ~ v7_waybel_0(B_231)
      | ~ v4_orders_2(B_231)
      | v2_struct_0(B_231)
      | ~ l1_struct_0(A_230)
      | v2_struct_0(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_226,plain,(
    ! [B_184] :
      ( v7_waybel_0('#skF_11'(B_184))
      | ~ l1_struct_0('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(resolution,[status(thm)],[c_219,c_223])).

tff(c_229,plain,(
    ! [B_184] :
      ( v7_waybel_0('#skF_11'(B_184))
      | ~ l1_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_226])).

tff(c_230,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_240,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_16,c_230])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_240])).

tff(c_246,plain,(
    l1_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_248,plain,(
    ! [C_236,A_237,B_238] :
      ( v4_orders_2(C_236)
      | ~ m2_yellow_6(C_236,A_237,B_238)
      | ~ l1_waybel_0(B_238,A_237)
      | ~ v7_waybel_0(B_238)
      | ~ v4_orders_2(B_238)
      | v2_struct_0(B_238)
      | ~ l1_struct_0(A_237)
      | v2_struct_0(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_251,plain,(
    ! [B_184] :
      ( v4_orders_2('#skF_11'(B_184))
      | ~ l1_struct_0('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(resolution,[status(thm)],[c_219,c_248])).

tff(c_254,plain,(
    ! [B_184] :
      ( v4_orders_2('#skF_11'(B_184))
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_251])).

tff(c_255,plain,(
    ! [B_184] :
      ( v4_orders_2('#skF_11'(B_184))
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_254])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_275,plain,(
    ! [A_248,B_249] :
      ( m1_subset_1(k10_yellow_6(A_248,B_249),k1_zfmisc_1(u1_struct_0(A_248)))
      | ~ l1_waybel_0(B_249,A_248)
      | ~ v7_waybel_0(B_249)
      | ~ v4_orders_2(B_249)
      | v2_struct_0(B_249)
      | ~ l1_pre_topc(A_248)
      | ~ v2_pre_topc(A_248)
      | v2_struct_0(A_248) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_321,plain,(
    ! [A_267,A_268,B_269] :
      ( m1_subset_1(A_267,u1_struct_0(A_268))
      | ~ r2_hidden(A_267,k10_yellow_6(A_268,B_269))
      | ~ l1_waybel_0(B_269,A_268)
      | ~ v7_waybel_0(B_269)
      | ~ v4_orders_2(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268) ) ),
    inference(resolution,[status(thm)],[c_275,c_12])).

tff(c_331,plain,(
    ! [A_268,B_269,B_2] :
      ( m1_subset_1('#skF_1'(k10_yellow_6(A_268,B_269),B_2),u1_struct_0(A_268))
      | ~ l1_waybel_0(B_269,A_268)
      | ~ v7_waybel_0(B_269)
      | ~ v4_orders_2(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268)
      | r1_tarski(k10_yellow_6(A_268,B_269),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_321])).

tff(c_338,plain,(
    ! [A_280,B_281,C_282] :
      ( r3_waybel_9(A_280,B_281,C_282)
      | ~ r2_hidden(C_282,k10_yellow_6(A_280,B_281))
      | ~ m1_subset_1(C_282,u1_struct_0(A_280))
      | ~ l1_waybel_0(B_281,A_280)
      | ~ v7_waybel_0(B_281)
      | ~ v4_orders_2(B_281)
      | v2_struct_0(B_281)
      | ~ l1_pre_topc(A_280)
      | ~ v2_pre_topc(A_280)
      | v2_struct_0(A_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_446,plain,(
    ! [A_329,B_330,B_331] :
      ( r3_waybel_9(A_329,B_330,'#skF_1'(k10_yellow_6(A_329,B_330),B_331))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6(A_329,B_330),B_331),u1_struct_0(A_329))
      | ~ l1_waybel_0(B_330,A_329)
      | ~ v7_waybel_0(B_330)
      | ~ v4_orders_2(B_330)
      | v2_struct_0(B_330)
      | ~ l1_pre_topc(A_329)
      | ~ v2_pre_topc(A_329)
      | v2_struct_0(A_329)
      | r1_tarski(k10_yellow_6(A_329,B_330),B_331) ) ),
    inference(resolution,[status(thm)],[c_6,c_338])).

tff(c_449,plain,(
    ! [A_268,B_269,B_2] :
      ( r3_waybel_9(A_268,B_269,'#skF_1'(k10_yellow_6(A_268,B_269),B_2))
      | ~ l1_waybel_0(B_269,A_268)
      | ~ v7_waybel_0(B_269)
      | ~ v4_orders_2(B_269)
      | v2_struct_0(B_269)
      | ~ l1_pre_topc(A_268)
      | ~ v2_pre_topc(A_268)
      | v2_struct_0(A_268)
      | r1_tarski(k10_yellow_6(A_268,B_269),B_2) ) ),
    inference(resolution,[status(thm)],[c_331,c_446])).

tff(c_58,plain,(
    ! [A_122,B_134,C_140] :
      ( m1_connsp_2('#skF_5'(A_122,B_134,C_140),A_122,C_140)
      | r3_waybel_9(A_122,B_134,C_140)
      | ~ m1_subset_1(C_140,u1_struct_0(A_122))
      | ~ l1_waybel_0(B_134,A_122)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_334,plain,(
    ! [A_276,B_277,D_278,C_279] :
      ( r2_waybel_0(A_276,B_277,D_278)
      | ~ m1_connsp_2(D_278,A_276,C_279)
      | ~ r3_waybel_9(A_276,B_277,C_279)
      | ~ m1_subset_1(C_279,u1_struct_0(A_276))
      | ~ l1_waybel_0(B_277,A_276)
      | v2_struct_0(B_277)
      | ~ l1_pre_topc(A_276)
      | ~ v2_pre_topc(A_276)
      | v2_struct_0(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_432,plain,(
    ! [A_318,B_319,B_320,C_321] :
      ( r2_waybel_0(A_318,B_319,'#skF_5'(A_318,B_320,C_321))
      | ~ r3_waybel_9(A_318,B_319,C_321)
      | ~ l1_waybel_0(B_319,A_318)
      | v2_struct_0(B_319)
      | r3_waybel_9(A_318,B_320,C_321)
      | ~ m1_subset_1(C_321,u1_struct_0(A_318))
      | ~ l1_waybel_0(B_320,A_318)
      | v2_struct_0(B_320)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318) ) ),
    inference(resolution,[status(thm)],[c_58,c_334])).

tff(c_48,plain,(
    ! [A_104,B_112,D_118,C_116] :
      ( r2_waybel_0(A_104,B_112,D_118)
      | ~ r2_waybel_0(A_104,C_116,D_118)
      | ~ m2_yellow_6(C_116,A_104,B_112)
      | ~ l1_waybel_0(B_112,A_104)
      | ~ v7_waybel_0(B_112)
      | ~ v4_orders_2(B_112)
      | v2_struct_0(B_112)
      | ~ l1_struct_0(A_104)
      | v2_struct_0(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_565,plain,(
    ! [B_403,B_402,C_400,A_399,B_401] :
      ( r2_waybel_0(A_399,B_402,'#skF_5'(A_399,B_403,C_400))
      | ~ m2_yellow_6(B_401,A_399,B_402)
      | ~ l1_waybel_0(B_402,A_399)
      | ~ v7_waybel_0(B_402)
      | ~ v4_orders_2(B_402)
      | v2_struct_0(B_402)
      | ~ l1_struct_0(A_399)
      | ~ r3_waybel_9(A_399,B_401,C_400)
      | ~ l1_waybel_0(B_401,A_399)
      | v2_struct_0(B_401)
      | r3_waybel_9(A_399,B_403,C_400)
      | ~ m1_subset_1(C_400,u1_struct_0(A_399))
      | ~ l1_waybel_0(B_403,A_399)
      | v2_struct_0(B_403)
      | ~ l1_pre_topc(A_399)
      | ~ v2_pre_topc(A_399)
      | v2_struct_0(A_399) ) ),
    inference(resolution,[status(thm)],[c_432,c_48])).

tff(c_569,plain,(
    ! [B_184,B_403,C_400] :
      ( r2_waybel_0('#skF_9',B_184,'#skF_5'('#skF_9',B_403,C_400))
      | ~ l1_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_11'(B_184),C_400)
      | ~ l1_waybel_0('#skF_11'(B_184),'#skF_9')
      | v2_struct_0('#skF_11'(B_184))
      | r3_waybel_9('#skF_9',B_403,C_400)
      | ~ m1_subset_1(C_400,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_403,'#skF_9')
      | v2_struct_0(B_403)
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(resolution,[status(thm)],[c_219,c_565])).

tff(c_573,plain,(
    ! [B_184,B_403,C_400] :
      ( r2_waybel_0('#skF_9',B_184,'#skF_5'('#skF_9',B_403,C_400))
      | ~ r3_waybel_9('#skF_9','#skF_11'(B_184),C_400)
      | ~ l1_waybel_0('#skF_11'(B_184),'#skF_9')
      | v2_struct_0('#skF_11'(B_184))
      | r3_waybel_9('#skF_9',B_403,C_400)
      | ~ m1_subset_1(C_400,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_403,'#skF_9')
      | v2_struct_0(B_403)
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_246,c_569])).

tff(c_575,plain,(
    ! [B_404,B_405,C_406] :
      ( r2_waybel_0('#skF_9',B_404,'#skF_5'('#skF_9',B_405,C_406))
      | ~ r3_waybel_9('#skF_9','#skF_11'(B_404),C_406)
      | ~ l1_waybel_0('#skF_11'(B_404),'#skF_9')
      | v2_struct_0('#skF_11'(B_404))
      | r3_waybel_9('#skF_9',B_405,C_406)
      | ~ m1_subset_1(C_406,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_405,'#skF_9')
      | v2_struct_0(B_405)
      | ~ l1_waybel_0(B_404,'#skF_9')
      | ~ v7_waybel_0(B_404)
      | ~ v4_orders_2(B_404)
      | v2_struct_0(B_404) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_573])).

tff(c_581,plain,(
    ! [B_404,B_405,B_2] :
      ( r2_waybel_0('#skF_9',B_404,'#skF_5'('#skF_9',B_405,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_404)),B_2)))
      | r3_waybel_9('#skF_9',B_405,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_404)),B_2))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_404)),B_2),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_405,'#skF_9')
      | v2_struct_0(B_405)
      | ~ l1_waybel_0(B_404,'#skF_9')
      | ~ v7_waybel_0(B_404)
      | ~ v4_orders_2(B_404)
      | v2_struct_0(B_404)
      | ~ l1_waybel_0('#skF_11'(B_404),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_404))
      | ~ v4_orders_2('#skF_11'(B_404))
      | v2_struct_0('#skF_11'(B_404))
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9')
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'(B_404)),B_2) ) ),
    inference(resolution,[status(thm)],[c_449,c_575])).

tff(c_591,plain,(
    ! [B_404,B_405,B_2] :
      ( r2_waybel_0('#skF_9',B_404,'#skF_5'('#skF_9',B_405,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_404)),B_2)))
      | r3_waybel_9('#skF_9',B_405,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_404)),B_2))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_404)),B_2),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_405,'#skF_9')
      | v2_struct_0(B_405)
      | ~ l1_waybel_0(B_404,'#skF_9')
      | ~ v7_waybel_0(B_404)
      | ~ v4_orders_2(B_404)
      | v2_struct_0(B_404)
      | ~ l1_waybel_0('#skF_11'(B_404),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_404))
      | ~ v4_orders_2('#skF_11'(B_404))
      | v2_struct_0('#skF_11'(B_404))
      | v2_struct_0('#skF_9')
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'(B_404)),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_581])).

tff(c_626,plain,(
    ! [B_436,B_437,B_438] :
      ( r2_waybel_0('#skF_9',B_436,'#skF_5'('#skF_9',B_437,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_436)),B_438)))
      | r3_waybel_9('#skF_9',B_437,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_436)),B_438))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_436)),B_438),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_437,'#skF_9')
      | v2_struct_0(B_437)
      | ~ l1_waybel_0(B_436,'#skF_9')
      | ~ v7_waybel_0(B_436)
      | ~ v4_orders_2(B_436)
      | v2_struct_0(B_436)
      | ~ l1_waybel_0('#skF_11'(B_436),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_436))
      | ~ v4_orders_2('#skF_11'(B_436))
      | v2_struct_0('#skF_11'(B_436))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'(B_436)),B_438) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_591])).

tff(c_56,plain,(
    ! [A_122,B_134,C_140] :
      ( ~ r2_waybel_0(A_122,B_134,'#skF_5'(A_122,B_134,C_140))
      | r3_waybel_9(A_122,B_134,C_140)
      | ~ m1_subset_1(C_140,u1_struct_0(A_122))
      | ~ l1_waybel_0(B_134,A_122)
      | v2_struct_0(B_134)
      | ~ l1_pre_topc(A_122)
      | ~ v2_pre_topc(A_122)
      | v2_struct_0(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_195])).

tff(c_630,plain,(
    ! [B_437,B_438] :
      ( ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9')
      | r3_waybel_9('#skF_9',B_437,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_437)),B_438))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_437)),B_438),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_437,'#skF_9')
      | ~ v7_waybel_0(B_437)
      | ~ v4_orders_2(B_437)
      | v2_struct_0(B_437)
      | ~ l1_waybel_0('#skF_11'(B_437),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_437))
      | ~ v4_orders_2('#skF_11'(B_437))
      | v2_struct_0('#skF_11'(B_437))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'(B_437)),B_438) ) ),
    inference(resolution,[status(thm)],[c_626,c_56])).

tff(c_635,plain,(
    ! [B_437,B_438] :
      ( v2_struct_0('#skF_9')
      | r3_waybel_9('#skF_9',B_437,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_437)),B_438))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_437)),B_438),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_437,'#skF_9')
      | ~ v7_waybel_0(B_437)
      | ~ v4_orders_2(B_437)
      | v2_struct_0(B_437)
      | ~ l1_waybel_0('#skF_11'(B_437),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_437))
      | ~ v4_orders_2('#skF_11'(B_437))
      | v2_struct_0('#skF_11'(B_437))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'(B_437)),B_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_630])).

tff(c_642,plain,(
    ! [B_442,B_443] :
      ( r3_waybel_9('#skF_9',B_442,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_442)),B_443))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_442)),B_443),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0(B_442,'#skF_9')
      | ~ v7_waybel_0(B_442)
      | ~ v4_orders_2(B_442)
      | v2_struct_0(B_442)
      | ~ l1_waybel_0('#skF_11'(B_442),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_442))
      | ~ v4_orders_2('#skF_11'(B_442))
      | v2_struct_0('#skF_11'(B_442))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'(B_442)),B_443) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_635])).

tff(c_645,plain,(
    ! [B_442,B_2] :
      ( r3_waybel_9('#skF_9',B_442,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_442)),B_2))
      | ~ l1_waybel_0(B_442,'#skF_9')
      | ~ v7_waybel_0(B_442)
      | ~ v4_orders_2(B_442)
      | v2_struct_0(B_442)
      | ~ l1_waybel_0('#skF_11'(B_442),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_442))
      | ~ v4_orders_2('#skF_11'(B_442))
      | v2_struct_0('#skF_11'(B_442))
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9')
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'(B_442)),B_2) ) ),
    inference(resolution,[status(thm)],[c_331,c_642])).

tff(c_648,plain,(
    ! [B_442,B_2] :
      ( r3_waybel_9('#skF_9',B_442,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_442)),B_2))
      | ~ l1_waybel_0(B_442,'#skF_9')
      | ~ v7_waybel_0(B_442)
      | ~ v4_orders_2(B_442)
      | v2_struct_0(B_442)
      | ~ l1_waybel_0('#skF_11'(B_442),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_442))
      | ~ v4_orders_2('#skF_11'(B_442))
      | v2_struct_0('#skF_11'(B_442))
      | v2_struct_0('#skF_9')
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'(B_442)),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_645])).

tff(c_650,plain,(
    ! [B_444,B_445] :
      ( r3_waybel_9('#skF_9',B_444,'#skF_1'(k10_yellow_6('#skF_9','#skF_11'(B_444)),B_445))
      | ~ l1_waybel_0(B_444,'#skF_9')
      | ~ v7_waybel_0(B_444)
      | ~ v4_orders_2(B_444)
      | v2_struct_0(B_444)
      | ~ l1_waybel_0('#skF_11'(B_444),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_444))
      | ~ v4_orders_2('#skF_11'(B_444))
      | v2_struct_0('#skF_11'(B_444))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'(B_444)),B_445) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_648])).

tff(c_66,plain,(
    ! [A_165,C_175] :
      ( ~ r3_waybel_9(A_165,'#skF_8'(A_165),C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(A_165))
      | v1_compts_1(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_657,plain,(
    ! [B_445] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | v1_compts_1('#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
      | ~ v7_waybel_0('#skF_8'('#skF_9'))
      | ~ v4_orders_2('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_8'('#skF_9'))
      | ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9')
      | ~ v7_waybel_0('#skF_11'('#skF_8'('#skF_9')))
      | ~ v4_orders_2('#skF_11'('#skF_8'('#skF_9')))
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(resolution,[status(thm)],[c_650,c_66])).

tff(c_661,plain,(
    ! [B_445] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | v1_compts_1('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
      | ~ v7_waybel_0('#skF_8'('#skF_9'))
      | ~ v4_orders_2('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_8'('#skF_9'))
      | ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9')
      | ~ v7_waybel_0('#skF_11'('#skF_8'('#skF_9')))
      | ~ v4_orders_2('#skF_11'('#skF_8'('#skF_9')))
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_657])).

tff(c_662,plain,(
    ! [B_445] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
      | ~ v7_waybel_0('#skF_8'('#skF_9'))
      | ~ v4_orders_2('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_8'('#skF_9'))
      | ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9')
      | ~ v7_waybel_0('#skF_11'('#skF_8'('#skF_9')))
      | ~ v4_orders_2('#skF_11'('#skF_8'('#skF_9')))
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_661])).

tff(c_663,plain,(
    ~ v4_orders_2('#skF_11'('#skF_8'('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_662])).

tff(c_667,plain,
    ( ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
    | ~ v7_waybel_0('#skF_8'('#skF_9'))
    | ~ v4_orders_2('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(resolution,[status(thm)],[c_255,c_663])).

tff(c_673,plain,(
    ~ v4_orders_2('#skF_8'('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_676,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_673])).

tff(c_679,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_676])).

tff(c_681,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_679])).

tff(c_682,plain,
    ( ~ v7_waybel_0('#skF_8'('#skF_9'))
    | ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_699,plain,(
    ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_682])).

tff(c_702,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_699])).

tff(c_705,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_702])).

tff(c_707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_705])).

tff(c_708,plain,
    ( ~ v7_waybel_0('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_682])).

tff(c_710,plain,(
    ~ v7_waybel_0('#skF_8'('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_713,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_710])).

tff(c_716,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_713])).

tff(c_718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_716])).

tff(c_719,plain,(
    v2_struct_0('#skF_8'('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_74,plain,(
    ! [A_165] :
      ( ~ v2_struct_0('#skF_8'(A_165))
      | v1_compts_1(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_742,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_719,c_74])).

tff(c_745,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_742])).

tff(c_747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_745])).

tff(c_748,plain,(
    ! [B_445] :
      ( ~ v7_waybel_0('#skF_11'('#skF_8'('#skF_9')))
      | ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9')
      | ~ v4_orders_2('#skF_8'('#skF_9'))
      | ~ v7_waybel_0('#skF_8'('#skF_9'))
      | ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | v2_struct_0('#skF_8'('#skF_9'))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_765,plain,(
    ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_748])).

tff(c_768,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_765])).

tff(c_771,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_768])).

tff(c_773,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_771])).

tff(c_775,plain,(
    l1_waybel_0('#skF_8'('#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_245,plain,(
    ! [B_184] :
      ( v7_waybel_0('#skF_11'(B_184))
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_774,plain,(
    ! [B_445] :
      ( ~ v7_waybel_0('#skF_8'('#skF_9'))
      | ~ v4_orders_2('#skF_8'('#skF_9'))
      | ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9')
      | ~ v7_waybel_0('#skF_11'('#skF_8'('#skF_9')))
      | v2_struct_0('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(splitRight,[status(thm)],[c_748])).

tff(c_776,plain,(
    ~ v7_waybel_0('#skF_11'('#skF_8'('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_774])).

tff(c_779,plain,
    ( ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
    | ~ v7_waybel_0('#skF_8'('#skF_9'))
    | ~ v4_orders_2('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(resolution,[status(thm)],[c_245,c_776])).

tff(c_782,plain,
    ( ~ v7_waybel_0('#skF_8'('#skF_9'))
    | ~ v4_orders_2('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_779])).

tff(c_788,plain,(
    ~ v4_orders_2('#skF_8'('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_782])).

tff(c_791,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_788])).

tff(c_794,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_791])).

tff(c_796,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_794])).

tff(c_797,plain,
    ( ~ v7_waybel_0('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_782])).

tff(c_807,plain,(
    ~ v7_waybel_0('#skF_8'('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_797])).

tff(c_810,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_807])).

tff(c_813,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_810])).

tff(c_815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_813])).

tff(c_816,plain,(
    v2_struct_0('#skF_8'('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_797])).

tff(c_820,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_816,c_74])).

tff(c_823,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_820])).

tff(c_825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_823])).

tff(c_826,plain,(
    ! [B_445] :
      ( ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9')
      | ~ v4_orders_2('#skF_8'('#skF_9'))
      | ~ v7_waybel_0('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | v2_struct_0('#skF_8'('#skF_9'))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(splitRight,[status(thm)],[c_774])).

tff(c_833,plain,(
    ~ v7_waybel_0('#skF_8'('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_826])).

tff(c_836,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_833])).

tff(c_839,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_836])).

tff(c_841,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_839])).

tff(c_843,plain,(
    v7_waybel_0('#skF_8'('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_266,plain,(
    ! [C_244,A_245,B_246] :
      ( l1_waybel_0(C_244,A_245)
      | ~ m2_yellow_6(C_244,A_245,B_246)
      | ~ l1_waybel_0(B_246,A_245)
      | ~ v7_waybel_0(B_246)
      | ~ v4_orders_2(B_246)
      | v2_struct_0(B_246)
      | ~ l1_struct_0(A_245)
      | v2_struct_0(A_245) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_269,plain,(
    ! [B_184] :
      ( l1_waybel_0('#skF_11'(B_184),'#skF_9')
      | ~ l1_struct_0('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(resolution,[status(thm)],[c_219,c_266])).

tff(c_272,plain,(
    ! [B_184] :
      ( l1_waybel_0('#skF_11'(B_184),'#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_269])).

tff(c_273,plain,(
    ! [B_184] :
      ( l1_waybel_0('#skF_11'(B_184),'#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_272])).

tff(c_842,plain,(
    ! [B_445] :
      ( ~ v4_orders_2('#skF_8'('#skF_9'))
      | ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9')
      | v2_struct_0('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(splitRight,[status(thm)],[c_826])).

tff(c_852,plain,(
    ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_842])).

tff(c_855,plain,
    ( ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
    | ~ v7_waybel_0('#skF_8'('#skF_9'))
    | ~ v4_orders_2('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(resolution,[status(thm)],[c_273,c_852])).

tff(c_858,plain,
    ( ~ v4_orders_2('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_775,c_855])).

tff(c_859,plain,(
    ~ v4_orders_2('#skF_8'('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_858])).

tff(c_862,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_859])).

tff(c_865,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_862])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_865])).

tff(c_868,plain,(
    v2_struct_0('#skF_8'('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_858])).

tff(c_891,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_868,c_74])).

tff(c_894,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_891])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_894])).

tff(c_897,plain,(
    ! [B_445] :
      ( ~ v4_orders_2('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | v2_struct_0('#skF_8'('#skF_9'))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_899,plain,(
    ~ v4_orders_2('#skF_8'('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_914,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_899])).

tff(c_917,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_914])).

tff(c_919,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_917])).

tff(c_921,plain,(
    v4_orders_2('#skF_8'('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_920,plain,(
    ! [B_445] :
      ( v2_struct_0('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_922,plain,(
    v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_920])).

tff(c_257,plain,(
    ! [C_240,A_241,B_242] :
      ( ~ v2_struct_0(C_240)
      | ~ m2_yellow_6(C_240,A_241,B_242)
      | ~ l1_waybel_0(B_242,A_241)
      | ~ v7_waybel_0(B_242)
      | ~ v4_orders_2(B_242)
      | v2_struct_0(B_242)
      | ~ l1_struct_0(A_241)
      | v2_struct_0(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_260,plain,(
    ! [B_184] :
      ( ~ v2_struct_0('#skF_11'(B_184))
      | ~ l1_struct_0('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(resolution,[status(thm)],[c_219,c_257])).

tff(c_263,plain,(
    ! [B_184] :
      ( ~ v2_struct_0('#skF_11'(B_184))
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_260])).

tff(c_264,plain,(
    ! [B_184] :
      ( ~ v2_struct_0('#skF_11'(B_184))
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_263])).

tff(c_925,plain,
    ( ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
    | ~ v7_waybel_0('#skF_8'('#skF_9'))
    | ~ v4_orders_2('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(resolution,[status(thm)],[c_922,c_264])).

tff(c_928,plain,(
    v2_struct_0('#skF_8'('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_843,c_775,c_925])).

tff(c_931,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_928,c_74])).

tff(c_934,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_931])).

tff(c_936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_934])).

tff(c_937,plain,(
    ! [B_445] :
      ( v2_struct_0('#skF_8'('#skF_9'))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445),u1_struct_0('#skF_9'))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_445) ) ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_958,plain,(
    v2_struct_0('#skF_8'('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_937])).

tff(c_961,plain,
    ( v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_958,c_74])).

tff(c_964,plain,
    ( v1_compts_1('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_961])).

tff(c_966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_122,c_964])).

tff(c_968,plain,(
    ~ v2_struct_0('#skF_8'('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_937])).

tff(c_938,plain,(
    ~ v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_920])).

tff(c_749,plain,(
    v4_orders_2('#skF_11'('#skF_8'('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_662])).

tff(c_827,plain,(
    v7_waybel_0('#skF_11'('#skF_8'('#skF_9'))) ),
    inference(splitRight,[status(thm)],[c_774])).

tff(c_898,plain,(
    l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_38,plain,(
    ! [A_98,B_99] :
      ( m1_subset_1(k10_yellow_6(A_98,B_99),k1_zfmisc_1(u1_struct_0(A_98)))
      | ~ l1_waybel_0(B_99,A_98)
      | ~ v7_waybel_0(B_99)
      | ~ v4_orders_2(B_99)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_981,plain,(
    ! [B_490] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_490),u1_struct_0('#skF_9'))
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_490) ) ),
    inference(splitRight,[status(thm)],[c_937])).

tff(c_985,plain,(
    ! [B_2] :
      ( ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9')
      | ~ v7_waybel_0('#skF_11'('#skF_8'('#skF_9')))
      | ~ v4_orders_2('#skF_11'('#skF_8'('#skF_9')))
      | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9')
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_2) ) ),
    inference(resolution,[status(thm)],[c_331,c_981])).

tff(c_988,plain,(
    ! [B_2] :
      ( v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
      | v2_struct_0('#skF_9')
      | r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_749,c_827,c_898,c_985])).

tff(c_989,plain,(
    ! [B_2] : r1_tarski(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),B_2) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_938,c_988])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_14,B_58,C_80] :
      ( m1_subset_1('#skF_3'(A_14,B_58,C_80),u1_struct_0(A_14))
      | k10_yellow_6(A_14,B_58) = C_80
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_waybel_0(B_58,A_14)
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_517,plain,(
    ! [A_353,B_354,D_355] :
      ( m1_connsp_2('#skF_2'(A_353,B_354,k10_yellow_6(A_353,B_354),D_355),A_353,D_355)
      | r2_hidden(D_355,k10_yellow_6(A_353,B_354))
      | ~ m1_subset_1(D_355,u1_struct_0(A_353))
      | ~ m1_subset_1(k10_yellow_6(A_353,B_354),k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ l1_waybel_0(B_354,A_353)
      | ~ v7_waybel_0(B_354)
      | ~ v4_orders_2(B_354)
      | v2_struct_0(B_354)
      | ~ l1_pre_topc(A_353)
      | ~ v2_pre_topc(A_353)
      | v2_struct_0(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_521,plain,(
    ! [A_356,B_357,D_358] :
      ( m1_connsp_2('#skF_2'(A_356,B_357,k10_yellow_6(A_356,B_357),D_358),A_356,D_358)
      | r2_hidden(D_358,k10_yellow_6(A_356,B_357))
      | ~ m1_subset_1(D_358,u1_struct_0(A_356))
      | ~ l1_waybel_0(B_357,A_356)
      | ~ v7_waybel_0(B_357)
      | ~ v4_orders_2(B_357)
      | v2_struct_0(B_357)
      | ~ l1_pre_topc(A_356)
      | ~ v2_pre_topc(A_356)
      | v2_struct_0(A_356) ) ),
    inference(resolution,[status(thm)],[c_38,c_517])).

tff(c_30,plain,(
    ! [A_14,B_58,C_80,E_97] :
      ( r2_hidden('#skF_3'(A_14,B_58,C_80),C_80)
      | r1_waybel_0(A_14,B_58,E_97)
      | ~ m1_connsp_2(E_97,A_14,'#skF_3'(A_14,B_58,C_80))
      | k10_yellow_6(A_14,B_58) = C_80
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_waybel_0(B_58,A_14)
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1445,plain,(
    ! [A_591,B_592,C_593,B_594] :
      ( r2_hidden('#skF_3'(A_591,B_592,C_593),C_593)
      | r1_waybel_0(A_591,B_592,'#skF_2'(A_591,B_594,k10_yellow_6(A_591,B_594),'#skF_3'(A_591,B_592,C_593)))
      | k10_yellow_6(A_591,B_592) = C_593
      | ~ m1_subset_1(C_593,k1_zfmisc_1(u1_struct_0(A_591)))
      | ~ l1_waybel_0(B_592,A_591)
      | ~ v7_waybel_0(B_592)
      | ~ v4_orders_2(B_592)
      | v2_struct_0(B_592)
      | r2_hidden('#skF_3'(A_591,B_592,C_593),k10_yellow_6(A_591,B_594))
      | ~ m1_subset_1('#skF_3'(A_591,B_592,C_593),u1_struct_0(A_591))
      | ~ l1_waybel_0(B_594,A_591)
      | ~ v7_waybel_0(B_594)
      | ~ v4_orders_2(B_594)
      | v2_struct_0(B_594)
      | ~ l1_pre_topc(A_591)
      | ~ v2_pre_topc(A_591)
      | v2_struct_0(A_591) ) ),
    inference(resolution,[status(thm)],[c_521,c_30])).

tff(c_34,plain,(
    ! [A_14,B_58,D_91] :
      ( ~ r1_waybel_0(A_14,B_58,'#skF_2'(A_14,B_58,k10_yellow_6(A_14,B_58),D_91))
      | r2_hidden(D_91,k10_yellow_6(A_14,B_58))
      | ~ m1_subset_1(D_91,u1_struct_0(A_14))
      | ~ m1_subset_1(k10_yellow_6(A_14,B_58),k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_waybel_0(B_58,A_14)
      | ~ v7_waybel_0(B_58)
      | ~ v4_orders_2(B_58)
      | v2_struct_0(B_58)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1472,plain,(
    ! [A_595,B_596,C_597] :
      ( ~ m1_subset_1(k10_yellow_6(A_595,B_596),k1_zfmisc_1(u1_struct_0(A_595)))
      | r2_hidden('#skF_3'(A_595,B_596,C_597),C_597)
      | k10_yellow_6(A_595,B_596) = C_597
      | ~ m1_subset_1(C_597,k1_zfmisc_1(u1_struct_0(A_595)))
      | r2_hidden('#skF_3'(A_595,B_596,C_597),k10_yellow_6(A_595,B_596))
      | ~ m1_subset_1('#skF_3'(A_595,B_596,C_597),u1_struct_0(A_595))
      | ~ l1_waybel_0(B_596,A_595)
      | ~ v7_waybel_0(B_596)
      | ~ v4_orders_2(B_596)
      | v2_struct_0(B_596)
      | ~ l1_pre_topc(A_595)
      | ~ v2_pre_topc(A_595)
      | v2_struct_0(A_595) ) ),
    inference(resolution,[status(thm)],[c_1445,c_34])).

tff(c_1492,plain,(
    ! [A_598,B_599,C_600] :
      ( r2_hidden('#skF_3'(A_598,B_599,C_600),C_600)
      | k10_yellow_6(A_598,B_599) = C_600
      | ~ m1_subset_1(C_600,k1_zfmisc_1(u1_struct_0(A_598)))
      | r2_hidden('#skF_3'(A_598,B_599,C_600),k10_yellow_6(A_598,B_599))
      | ~ m1_subset_1('#skF_3'(A_598,B_599,C_600),u1_struct_0(A_598))
      | ~ l1_waybel_0(B_599,A_598)
      | ~ v7_waybel_0(B_599)
      | ~ v4_orders_2(B_599)
      | v2_struct_0(B_599)
      | ~ l1_pre_topc(A_598)
      | ~ v2_pre_topc(A_598)
      | v2_struct_0(A_598) ) ),
    inference(resolution,[status(thm)],[c_38,c_1472])).

tff(c_60,plain,(
    ! [A_144,B_148,C_150] :
      ( r3_waybel_9(A_144,B_148,C_150)
      | ~ r2_hidden(C_150,k10_yellow_6(A_144,B_148))
      | ~ m1_subset_1(C_150,u1_struct_0(A_144))
      | ~ l1_waybel_0(B_148,A_144)
      | ~ v7_waybel_0(B_148)
      | ~ v4_orders_2(B_148)
      | v2_struct_0(B_148)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_1533,plain,(
    ! [A_601,B_602,C_603] :
      ( r3_waybel_9(A_601,B_602,'#skF_3'(A_601,B_602,C_603))
      | r2_hidden('#skF_3'(A_601,B_602,C_603),C_603)
      | k10_yellow_6(A_601,B_602) = C_603
      | ~ m1_subset_1(C_603,k1_zfmisc_1(u1_struct_0(A_601)))
      | ~ m1_subset_1('#skF_3'(A_601,B_602,C_603),u1_struct_0(A_601))
      | ~ l1_waybel_0(B_602,A_601)
      | ~ v7_waybel_0(B_602)
      | ~ v4_orders_2(B_602)
      | v2_struct_0(B_602)
      | ~ l1_pre_topc(A_601)
      | ~ v2_pre_topc(A_601)
      | v2_struct_0(A_601) ) ),
    inference(resolution,[status(thm)],[c_1492,c_60])).

tff(c_1567,plain,(
    ! [A_608,B_609,C_610] :
      ( r3_waybel_9(A_608,B_609,'#skF_3'(A_608,B_609,C_610))
      | r2_hidden('#skF_3'(A_608,B_609,C_610),C_610)
      | k10_yellow_6(A_608,B_609) = C_610
      | ~ m1_subset_1(C_610,k1_zfmisc_1(u1_struct_0(A_608)))
      | ~ l1_waybel_0(B_609,A_608)
      | ~ v7_waybel_0(B_609)
      | ~ v4_orders_2(B_609)
      | v2_struct_0(B_609)
      | ~ l1_pre_topc(A_608)
      | ~ v2_pre_topc(A_608)
      | v2_struct_0(A_608) ) ),
    inference(resolution,[status(thm)],[c_18,c_1533])).

tff(c_1575,plain,(
    ! [A_611,B_612] :
      ( r3_waybel_9(A_611,B_612,'#skF_3'(A_611,B_612,k1_xboole_0))
      | r2_hidden('#skF_3'(A_611,B_612,k1_xboole_0),k1_xboole_0)
      | k10_yellow_6(A_611,B_612) = k1_xboole_0
      | ~ l1_waybel_0(B_612,A_611)
      | ~ v7_waybel_0(B_612)
      | ~ v4_orders_2(B_612)
      | v2_struct_0(B_612)
      | ~ l1_pre_topc(A_611)
      | ~ v2_pre_topc(A_611)
      | v2_struct_0(A_611) ) ),
    inference(resolution,[status(thm)],[c_10,c_1567])).

tff(c_1604,plain,(
    ! [A_613] :
      ( ~ m1_subset_1('#skF_3'(A_613,'#skF_8'(A_613),k1_xboole_0),u1_struct_0(A_613))
      | v1_compts_1(A_613)
      | r2_hidden('#skF_3'(A_613,'#skF_8'(A_613),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6(A_613,'#skF_8'(A_613)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(A_613),A_613)
      | ~ v7_waybel_0('#skF_8'(A_613))
      | ~ v4_orders_2('#skF_8'(A_613))
      | v2_struct_0('#skF_8'(A_613))
      | ~ l1_pre_topc(A_613)
      | ~ v2_pre_topc(A_613)
      | v2_struct_0(A_613) ) ),
    inference(resolution,[status(thm)],[c_1575,c_66])).

tff(c_1608,plain,(
    ! [A_14] :
      ( v1_compts_1(A_14)
      | r2_hidden('#skF_3'(A_14,'#skF_8'(A_14),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6(A_14,'#skF_8'(A_14)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_14)))
      | ~ l1_waybel_0('#skF_8'(A_14),A_14)
      | ~ v7_waybel_0('#skF_8'(A_14))
      | ~ v4_orders_2('#skF_8'(A_14))
      | v2_struct_0('#skF_8'(A_14))
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_1604])).

tff(c_1612,plain,(
    ! [A_614] :
      ( v1_compts_1(A_614)
      | r2_hidden('#skF_3'(A_614,'#skF_8'(A_614),k1_xboole_0),k1_xboole_0)
      | k10_yellow_6(A_614,'#skF_8'(A_614)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(A_614),A_614)
      | ~ v7_waybel_0('#skF_8'(A_614))
      | ~ v4_orders_2('#skF_8'(A_614))
      | v2_struct_0('#skF_8'(A_614))
      | ~ l1_pre_topc(A_614)
      | ~ v2_pre_topc(A_614)
      | v2_struct_0(A_614) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1608])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1619,plain,(
    ! [A_614] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'(A_614,'#skF_8'(A_614),k1_xboole_0))
      | v1_compts_1(A_614)
      | k10_yellow_6(A_614,'#skF_8'(A_614)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(A_614),A_614)
      | ~ v7_waybel_0('#skF_8'(A_614))
      | ~ v4_orders_2('#skF_8'(A_614))
      | v2_struct_0('#skF_8'(A_614))
      | ~ l1_pre_topc(A_614)
      | ~ v2_pre_topc(A_614)
      | v2_struct_0(A_614) ) ),
    inference(resolution,[status(thm)],[c_1612,c_14])).

tff(c_1627,plain,(
    ! [A_615] :
      ( v1_compts_1(A_615)
      | k10_yellow_6(A_615,'#skF_8'(A_615)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(A_615),A_615)
      | ~ v7_waybel_0('#skF_8'(A_615))
      | ~ v4_orders_2('#skF_8'(A_615))
      | v2_struct_0('#skF_8'(A_615))
      | ~ l1_pre_topc(A_615)
      | ~ v2_pre_topc(A_615)
      | v2_struct_0(A_615) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1619])).

tff(c_1630,plain,
    ( v1_compts_1('#skF_9')
    | k10_yellow_6('#skF_9','#skF_8'('#skF_9')) = k1_xboole_0
    | ~ v7_waybel_0('#skF_8'('#skF_9'))
    | ~ v4_orders_2('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9'))
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_775,c_1627])).

tff(c_1636,plain,
    ( v1_compts_1('#skF_9')
    | k10_yellow_6('#skF_9','#skF_8'('#skF_9')) = k1_xboole_0
    | v2_struct_0('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_921,c_843,c_1630])).

tff(c_1637,plain,(
    k10_yellow_6('#skF_9','#skF_8'('#skF_9')) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_968,c_122,c_1636])).

tff(c_1475,plain,(
    ! [A_98,B_99,C_597] :
      ( r2_hidden('#skF_3'(A_98,B_99,C_597),C_597)
      | k10_yellow_6(A_98,B_99) = C_597
      | ~ m1_subset_1(C_597,k1_zfmisc_1(u1_struct_0(A_98)))
      | r2_hidden('#skF_3'(A_98,B_99,C_597),k10_yellow_6(A_98,B_99))
      | ~ m1_subset_1('#skF_3'(A_98,B_99,C_597),u1_struct_0(A_98))
      | ~ l1_waybel_0(B_99,A_98)
      | ~ v7_waybel_0(B_99)
      | ~ v4_orders_2(B_99)
      | v2_struct_0(B_99)
      | ~ l1_pre_topc(A_98)
      | ~ v2_pre_topc(A_98)
      | v2_struct_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_38,c_1472])).

tff(c_1666,plain,(
    ! [C_597] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_597),C_597)
      | k10_yellow_6('#skF_9','#skF_8'('#skF_9')) = C_597
      | ~ m1_subset_1(C_597,k1_zfmisc_1(u1_struct_0('#skF_9')))
      | r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_597),k1_xboole_0)
      | ~ m1_subset_1('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_597),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
      | ~ v7_waybel_0('#skF_8'('#skF_9'))
      | ~ v4_orders_2('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_8'('#skF_9'))
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1637,c_1475])).

tff(c_1740,plain,(
    ! [C_597] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_597),C_597)
      | k1_xboole_0 = C_597
      | ~ m1_subset_1(C_597,k1_zfmisc_1(u1_struct_0('#skF_9')))
      | r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_597),k1_xboole_0)
      | ~ m1_subset_1('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_597),u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_921,c_843,c_775,c_1637,c_1666])).

tff(c_2150,plain,(
    ! [C_639] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_639),C_639)
      | k1_xboole_0 = C_639
      | ~ m1_subset_1(C_639,k1_zfmisc_1(u1_struct_0('#skF_9')))
      | r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_639),k1_xboole_0)
      | ~ m1_subset_1('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_639),u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_968,c_1740])).

tff(c_2153,plain,(
    ! [C_80] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_80),C_80)
      | k1_xboole_0 = C_80
      | r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_80),k1_xboole_0)
      | k10_yellow_6('#skF_9','#skF_8'('#skF_9')) = C_80
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0('#skF_9')))
      | ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
      | ~ v7_waybel_0('#skF_8'('#skF_9'))
      | ~ v4_orders_2('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_8'('#skF_9'))
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_2150])).

tff(c_2156,plain,(
    ! [C_80] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_80),C_80)
      | r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_80),k1_xboole_0)
      | k1_xboole_0 = C_80
      | ~ m1_subset_1(C_80,k1_zfmisc_1(u1_struct_0('#skF_9')))
      | v2_struct_0('#skF_8'('#skF_9'))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_921,c_843,c_775,c_1637,c_2153])).

tff(c_2178,plain,(
    ! [C_640] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_640),C_640)
      | r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_640),k1_xboole_0)
      | k1_xboole_0 = C_640
      | ~ m1_subset_1(C_640,k1_zfmisc_1(u1_struct_0('#skF_9'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_968,c_2156])).

tff(c_2205,plain,(
    ! [C_640] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'('#skF_9','#skF_8'('#skF_9'),C_640))
      | r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_640),C_640)
      | k1_xboole_0 = C_640
      | ~ m1_subset_1(C_640,k1_zfmisc_1(u1_struct_0('#skF_9'))) ) ),
    inference(resolution,[status(thm)],[c_2178,c_14])).

tff(c_2225,plain,(
    ! [C_641] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_8'('#skF_9'),C_641),C_641)
      | k1_xboole_0 = C_641
      | ~ m1_subset_1(C_641,k1_zfmisc_1(u1_struct_0('#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_2205])).

tff(c_2265,plain,(
    ! [C_642] :
      ( ~ r1_tarski(C_642,'#skF_3'('#skF_9','#skF_8'('#skF_9'),C_642))
      | k1_xboole_0 = C_642
      | ~ m1_subset_1(C_642,k1_zfmisc_1(u1_struct_0('#skF_9'))) ) ),
    inference(resolution,[status(thm)],[c_2225,c_14])).

tff(c_2283,plain,
    ( k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))) = k1_xboole_0
    | ~ m1_subset_1(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),k1_zfmisc_1(u1_struct_0('#skF_9'))) ),
    inference(resolution,[status(thm)],[c_989,c_2265])).

tff(c_2327,plain,(
    ~ m1_subset_1(k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))),k1_zfmisc_1(u1_struct_0('#skF_9'))) ),
    inference(splitLeft,[status(thm)],[c_2283])).

tff(c_2330,plain,
    ( ~ l1_waybel_0('#skF_11'('#skF_8'('#skF_9')),'#skF_9')
    | ~ v7_waybel_0('#skF_11'('#skF_8'('#skF_9')))
    | ~ v4_orders_2('#skF_11'('#skF_8'('#skF_9')))
    | v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_38,c_2327])).

tff(c_2333,plain,
    ( v2_struct_0('#skF_11'('#skF_8'('#skF_9')))
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_749,c_827,c_898,c_2330])).

tff(c_2335,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_938,c_2333])).

tff(c_2336,plain,(
    k10_yellow_6('#skF_9','#skF_11'('#skF_8'('#skF_9'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2283])).

tff(c_108,plain,(
    ! [B_184] :
      ( v1_compts_1('#skF_9')
      | v3_yellow_6('#skF_11'(B_184),'#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_216,plain,(
    ! [B_184] :
      ( v3_yellow_6('#skF_11'(B_184),'#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_108])).

tff(c_279,plain,(
    ! [A_250,B_251] :
      ( k10_yellow_6(A_250,B_251) != k1_xboole_0
      | ~ v3_yellow_6(B_251,A_250)
      | ~ l1_waybel_0(B_251,A_250)
      | ~ v7_waybel_0(B_251)
      | ~ v4_orders_2(B_251)
      | v2_struct_0(B_251)
      | ~ l1_pre_topc(A_250)
      | ~ v2_pre_topc(A_250)
      | v2_struct_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_282,plain,(
    ! [B_184] :
      ( k10_yellow_6('#skF_9','#skF_11'(B_184)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_11'(B_184),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_184))
      | ~ v4_orders_2('#skF_11'(B_184))
      | v2_struct_0('#skF_11'(B_184))
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(resolution,[status(thm)],[c_216,c_279])).

tff(c_285,plain,(
    ! [B_184] :
      ( k10_yellow_6('#skF_9','#skF_11'(B_184)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_11'(B_184),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_184))
      | ~ v4_orders_2('#skF_11'(B_184))
      | v2_struct_0('#skF_11'(B_184))
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_184,'#skF_9')
      | ~ v7_waybel_0(B_184)
      | ~ v4_orders_2(B_184)
      | v2_struct_0(B_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_282])).

tff(c_287,plain,(
    ! [B_252] :
      ( k10_yellow_6('#skF_9','#skF_11'(B_252)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_11'(B_252),'#skF_9')
      | ~ v7_waybel_0('#skF_11'(B_252))
      | ~ v4_orders_2('#skF_11'(B_252))
      | v2_struct_0('#skF_11'(B_252))
      | ~ l1_waybel_0(B_252,'#skF_9')
      | ~ v7_waybel_0(B_252)
      | ~ v4_orders_2(B_252)
      | v2_struct_0(B_252) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_285])).

tff(c_304,plain,(
    ! [B_259] :
      ( k10_yellow_6('#skF_9','#skF_11'(B_259)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_11'(B_259))
      | ~ v4_orders_2('#skF_11'(B_259))
      | v2_struct_0('#skF_11'(B_259))
      | ~ l1_waybel_0(B_259,'#skF_9')
      | ~ v7_waybel_0(B_259)
      | ~ v4_orders_2(B_259)
      | v2_struct_0(B_259) ) ),
    inference(resolution,[status(thm)],[c_273,c_287])).

tff(c_309,plain,(
    ! [B_260] :
      ( k10_yellow_6('#skF_9','#skF_11'(B_260)) != k1_xboole_0
      | ~ v4_orders_2('#skF_11'(B_260))
      | v2_struct_0('#skF_11'(B_260))
      | ~ l1_waybel_0(B_260,'#skF_9')
      | ~ v7_waybel_0(B_260)
      | ~ v4_orders_2(B_260)
      | v2_struct_0(B_260) ) ),
    inference(resolution,[status(thm)],[c_245,c_304])).

tff(c_315,plain,(
    ! [B_265] :
      ( k10_yellow_6('#skF_9','#skF_11'(B_265)) != k1_xboole_0
      | v2_struct_0('#skF_11'(B_265))
      | ~ l1_waybel_0(B_265,'#skF_9')
      | ~ v7_waybel_0(B_265)
      | ~ v4_orders_2(B_265)
      | v2_struct_0(B_265) ) ),
    inference(resolution,[status(thm)],[c_255,c_309])).

tff(c_319,plain,(
    ! [B_265] :
      ( k10_yellow_6('#skF_9','#skF_11'(B_265)) != k1_xboole_0
      | ~ l1_waybel_0(B_265,'#skF_9')
      | ~ v7_waybel_0(B_265)
      | ~ v4_orders_2(B_265)
      | v2_struct_0(B_265) ) ),
    inference(resolution,[status(thm)],[c_315,c_264])).

tff(c_2434,plain,
    ( ~ l1_waybel_0('#skF_8'('#skF_9'),'#skF_9')
    | ~ v7_waybel_0('#skF_8'('#skF_9'))
    | ~ v4_orders_2('#skF_8'('#skF_9'))
    | v2_struct_0('#skF_8'('#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2336,c_319])).

tff(c_2538,plain,(
    v2_struct_0('#skF_8'('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_843,c_775,c_2434])).

tff(c_2540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_968,c_2538])).

tff(c_2541,plain,(
    ~ v2_struct_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_2542,plain,(
    v1_compts_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_92,plain,
    ( v4_orders_2('#skF_10')
    | ~ v1_compts_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_2543,plain,(
    ~ v1_compts_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_2545,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_2543])).

tff(c_2546,plain,(
    v4_orders_2('#skF_10') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_90,plain,
    ( v7_waybel_0('#skF_10')
    | ~ v1_compts_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_2552,plain,(
    v7_waybel_0('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_90])).

tff(c_88,plain,
    ( l1_waybel_0('#skF_10','#skF_9')
    | ~ v1_compts_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_2554,plain,(
    l1_waybel_0('#skF_10','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_88])).

tff(c_76,plain,(
    ! [A_165,B_172] :
      ( r3_waybel_9(A_165,B_172,'#skF_7'(A_165,B_172))
      | ~ l1_waybel_0(B_172,A_165)
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ v1_compts_1(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_78,plain,(
    ! [A_165,B_172] :
      ( m1_subset_1('#skF_7'(A_165,B_172),u1_struct_0(A_165))
      | ~ l1_waybel_0(B_172,A_165)
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ v1_compts_1(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_2707,plain,(
    ! [A_734,B_735,C_736] :
      ( m2_yellow_6('#skF_6'(A_734,B_735,C_736),A_734,B_735)
      | ~ r3_waybel_9(A_734,B_735,C_736)
      | ~ m1_subset_1(C_736,u1_struct_0(A_734))
      | ~ l1_waybel_0(B_735,A_734)
      | ~ v7_waybel_0(B_735)
      | ~ v4_orders_2(B_735)
      | v2_struct_0(B_735)
      | ~ l1_pre_topc(A_734)
      | ~ v2_pre_topc(A_734)
      | v2_struct_0(A_734) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_40,plain,(
    ! [C_103,A_100,B_101] :
      ( l1_waybel_0(C_103,A_100)
      | ~ m2_yellow_6(C_103,A_100,B_101)
      | ~ l1_waybel_0(B_101,A_100)
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101)
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2788,plain,(
    ! [A_757,B_758,C_759] :
      ( l1_waybel_0('#skF_6'(A_757,B_758,C_759),A_757)
      | ~ l1_struct_0(A_757)
      | ~ r3_waybel_9(A_757,B_758,C_759)
      | ~ m1_subset_1(C_759,u1_struct_0(A_757))
      | ~ l1_waybel_0(B_758,A_757)
      | ~ v7_waybel_0(B_758)
      | ~ v4_orders_2(B_758)
      | v2_struct_0(B_758)
      | ~ l1_pre_topc(A_757)
      | ~ v2_pre_topc(A_757)
      | v2_struct_0(A_757) ) ),
    inference(resolution,[status(thm)],[c_2707,c_40])).

tff(c_2936,plain,(
    ! [A_825,B_826,B_827] :
      ( l1_waybel_0('#skF_6'(A_825,B_826,'#skF_7'(A_825,B_827)),A_825)
      | ~ l1_struct_0(A_825)
      | ~ r3_waybel_9(A_825,B_826,'#skF_7'(A_825,B_827))
      | ~ l1_waybel_0(B_826,A_825)
      | ~ v7_waybel_0(B_826)
      | ~ v4_orders_2(B_826)
      | v2_struct_0(B_826)
      | ~ l1_waybel_0(B_827,A_825)
      | ~ v7_waybel_0(B_827)
      | ~ v4_orders_2(B_827)
      | v2_struct_0(B_827)
      | ~ v1_compts_1(A_825)
      | ~ l1_pre_topc(A_825)
      | ~ v2_pre_topc(A_825)
      | v2_struct_0(A_825) ) ),
    inference(resolution,[status(thm)],[c_78,c_2788])).

tff(c_50,plain,(
    ! [B_121,A_119] :
      ( v3_yellow_6(B_121,A_119)
      | k10_yellow_6(A_119,B_121) = k1_xboole_0
      | ~ l1_waybel_0(B_121,A_119)
      | ~ v7_waybel_0(B_121)
      | ~ v4_orders_2(B_121)
      | v2_struct_0(B_121)
      | ~ l1_pre_topc(A_119)
      | ~ v2_pre_topc(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_86,plain,(
    ! [C_183] :
      ( ~ v3_yellow_6(C_183,'#skF_9')
      | ~ m2_yellow_6(C_183,'#skF_9','#skF_10')
      | ~ v1_compts_1('#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_297])).

tff(c_2580,plain,(
    ! [C_183] :
      ( ~ v3_yellow_6(C_183,'#skF_9')
      | ~ m2_yellow_6(C_183,'#skF_9','#skF_10') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2542,c_86])).

tff(c_2723,plain,(
    ! [C_736] :
      ( ~ v3_yellow_6('#skF_6'('#skF_9','#skF_10',C_736),'#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10',C_736)
      | ~ m1_subset_1(C_736,u1_struct_0('#skF_9'))
      | ~ l1_waybel_0('#skF_10','#skF_9')
      | ~ v7_waybel_0('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2707,c_2580])).

tff(c_2730,plain,(
    ! [C_736] :
      ( ~ v3_yellow_6('#skF_6'('#skF_9','#skF_10',C_736),'#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10',C_736)
      | ~ m1_subset_1(C_736,u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_10')
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2546,c_2552,c_2554,c_2723])).

tff(c_2732,plain,(
    ! [C_737] :
      ( ~ v3_yellow_6('#skF_6'('#skF_9','#skF_10',C_737),'#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10',C_737)
      | ~ m1_subset_1(C_737,u1_struct_0('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2541,c_2730])).

tff(c_2735,plain,(
    ! [C_737] :
      ( ~ r3_waybel_9('#skF_9','#skF_10',C_737)
      | ~ m1_subset_1(C_737,u1_struct_0('#skF_9'))
      | k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10',C_737)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_6'('#skF_9','#skF_10',C_737),'#skF_9')
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10',C_737))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10',C_737))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10',C_737))
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_2732])).

tff(c_2738,plain,(
    ! [C_737] :
      ( ~ r3_waybel_9('#skF_9','#skF_10',C_737)
      | ~ m1_subset_1(C_737,u1_struct_0('#skF_9'))
      | k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10',C_737)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_6'('#skF_9','#skF_10',C_737),'#skF_9')
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10',C_737))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10',C_737))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10',C_737))
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2735])).

tff(c_2799,plain,(
    ! [C_763] :
      ( ~ r3_waybel_9('#skF_9','#skF_10',C_763)
      | ~ m1_subset_1(C_763,u1_struct_0('#skF_9'))
      | k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10',C_763)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_6'('#skF_9','#skF_10',C_763),'#skF_9')
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10',C_763))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10',C_763))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10',C_763)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2738])).

tff(c_2811,plain,(
    ! [B_172] :
      ( ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)),'#skF_9')
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ v1_compts_1('#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_2799])).

tff(c_2822,plain,(
    ! [B_172] :
      ( ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)),'#skF_9')
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2542,c_2811])).

tff(c_2823,plain,(
    ! [B_172] :
      ( ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)),'#skF_9')
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2822])).

tff(c_2940,plain,(
    ! [B_827] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827)))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827)))
      | ~ l1_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_827))
      | ~ l1_waybel_0('#skF_10','#skF_9')
      | ~ v7_waybel_0('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_827,'#skF_9')
      | ~ v7_waybel_0(B_827)
      | ~ v4_orders_2(B_827)
      | v2_struct_0(B_827)
      | ~ v1_compts_1('#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2936,c_2823])).

tff(c_2943,plain,(
    ! [B_827] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827)))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827)))
      | ~ l1_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_827))
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_827,'#skF_9')
      | ~ v7_waybel_0(B_827)
      | ~ v4_orders_2(B_827)
      | v2_struct_0(B_827)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2542,c_2546,c_2552,c_2554,c_2940])).

tff(c_2944,plain,(
    ! [B_827] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827)))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_827)))
      | ~ l1_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_827))
      | ~ l1_waybel_0(B_827,'#skF_9')
      | ~ v7_waybel_0(B_827)
      | ~ v4_orders_2(B_827)
      | v2_struct_0(B_827) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2541,c_2943])).

tff(c_2972,plain,(
    ~ l1_struct_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2944])).

tff(c_2975,plain,(
    ~ l1_pre_topc('#skF_9') ),
    inference(resolution,[status(thm)],[c_16,c_2972])).

tff(c_2979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2975])).

tff(c_2981,plain,(
    l1_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2944])).

tff(c_44,plain,(
    ! [C_103,A_100,B_101] :
      ( v4_orders_2(C_103)
      | ~ m2_yellow_6(C_103,A_100,B_101)
      | ~ l1_waybel_0(B_101,A_100)
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101)
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2750,plain,(
    ! [A_742,B_743,C_744] :
      ( v4_orders_2('#skF_6'(A_742,B_743,C_744))
      | ~ l1_struct_0(A_742)
      | ~ r3_waybel_9(A_742,B_743,C_744)
      | ~ m1_subset_1(C_744,u1_struct_0(A_742))
      | ~ l1_waybel_0(B_743,A_742)
      | ~ v7_waybel_0(B_743)
      | ~ v4_orders_2(B_743)
      | v2_struct_0(B_743)
      | ~ l1_pre_topc(A_742)
      | ~ v2_pre_topc(A_742)
      | v2_struct_0(A_742) ) ),
    inference(resolution,[status(thm)],[c_2707,c_44])).

tff(c_2756,plain,(
    ! [A_165,B_743,B_172] :
      ( v4_orders_2('#skF_6'(A_165,B_743,'#skF_7'(A_165,B_172)))
      | ~ l1_struct_0(A_165)
      | ~ r3_waybel_9(A_165,B_743,'#skF_7'(A_165,B_172))
      | ~ l1_waybel_0(B_743,A_165)
      | ~ v7_waybel_0(B_743)
      | ~ v4_orders_2(B_743)
      | v2_struct_0(B_743)
      | ~ l1_waybel_0(B_172,A_165)
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ v1_compts_1(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_78,c_2750])).

tff(c_42,plain,(
    ! [C_103,A_100,B_101] :
      ( v7_waybel_0(C_103)
      | ~ m2_yellow_6(C_103,A_100,B_101)
      | ~ l1_waybel_0(B_101,A_100)
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101)
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2758,plain,(
    ! [A_748,B_749,C_750] :
      ( v7_waybel_0('#skF_6'(A_748,B_749,C_750))
      | ~ l1_struct_0(A_748)
      | ~ r3_waybel_9(A_748,B_749,C_750)
      | ~ m1_subset_1(C_750,u1_struct_0(A_748))
      | ~ l1_waybel_0(B_749,A_748)
      | ~ v7_waybel_0(B_749)
      | ~ v4_orders_2(B_749)
      | v2_struct_0(B_749)
      | ~ l1_pre_topc(A_748)
      | ~ v2_pre_topc(A_748)
      | v2_struct_0(A_748) ) ),
    inference(resolution,[status(thm)],[c_2707,c_42])).

tff(c_2764,plain,(
    ! [A_165,B_749,B_172] :
      ( v7_waybel_0('#skF_6'(A_165,B_749,'#skF_7'(A_165,B_172)))
      | ~ l1_struct_0(A_165)
      | ~ r3_waybel_9(A_165,B_749,'#skF_7'(A_165,B_172))
      | ~ l1_waybel_0(B_749,A_165)
      | ~ v7_waybel_0(B_749)
      | ~ v4_orders_2(B_749)
      | v2_struct_0(B_749)
      | ~ l1_waybel_0(B_172,A_165)
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ v1_compts_1(A_165)
      | ~ l1_pre_topc(A_165)
      | ~ v2_pre_topc(A_165)
      | v2_struct_0(A_165) ) ),
    inference(resolution,[status(thm)],[c_78,c_2758])).

tff(c_2983,plain,(
    ! [B_850] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_850))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_850)))
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_850)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_850)))
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_850))
      | ~ l1_waybel_0(B_850,'#skF_9')
      | ~ v7_waybel_0(B_850)
      | ~ v4_orders_2(B_850)
      | v2_struct_0(B_850) ) ),
    inference(splitRight,[status(thm)],[c_2944])).

tff(c_2987,plain,(
    ! [B_172] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))) = k1_xboole_0
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ l1_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | ~ l1_waybel_0('#skF_10','#skF_9')
      | ~ v7_waybel_0('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ v1_compts_1('#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2764,c_2983])).

tff(c_2990,plain,(
    ! [B_172] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))) = k1_xboole_0
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2542,c_2546,c_2552,c_2554,c_2981,c_2987])).

tff(c_2992,plain,(
    ! [B_851] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_851))) = k1_xboole_0
      | ~ v4_orders_2('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_851)))
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_851)))
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_851))
      | ~ l1_waybel_0(B_851,'#skF_9')
      | ~ v7_waybel_0(B_851)
      | ~ v4_orders_2(B_851)
      | v2_struct_0(B_851) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2541,c_2990])).

tff(c_2996,plain,(
    ! [B_172] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))) = k1_xboole_0
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ l1_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | ~ l1_waybel_0('#skF_10','#skF_9')
      | ~ v7_waybel_0('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ v1_compts_1('#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_2756,c_2992])).

tff(c_2999,plain,(
    ! [B_172] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))) = k1_xboole_0
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172)))
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | v2_struct_0('#skF_10')
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2542,c_2546,c_2552,c_2554,c_2981,c_2996])).

tff(c_3001,plain,(
    ! [B_852] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_852))) = k1_xboole_0
      | v2_struct_0('#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_852)))
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_852))
      | ~ l1_waybel_0(B_852,'#skF_9')
      | ~ v7_waybel_0(B_852)
      | ~ v4_orders_2(B_852)
      | v2_struct_0(B_852) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2541,c_2999])).

tff(c_46,plain,(
    ! [C_103,A_100,B_101] :
      ( ~ v2_struct_0(C_103)
      | ~ m2_yellow_6(C_103,A_100,B_101)
      | ~ l1_waybel_0(B_101,A_100)
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101)
      | ~ l1_struct_0(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2725,plain,(
    ! [A_734,B_735,C_736] :
      ( ~ v2_struct_0('#skF_6'(A_734,B_735,C_736))
      | ~ l1_struct_0(A_734)
      | ~ r3_waybel_9(A_734,B_735,C_736)
      | ~ m1_subset_1(C_736,u1_struct_0(A_734))
      | ~ l1_waybel_0(B_735,A_734)
      | ~ v7_waybel_0(B_735)
      | ~ v4_orders_2(B_735)
      | v2_struct_0(B_735)
      | ~ l1_pre_topc(A_734)
      | ~ v2_pre_topc(A_734)
      | v2_struct_0(A_734) ) ),
    inference(resolution,[status(thm)],[c_2707,c_46])).

tff(c_3003,plain,(
    ! [B_852] :
      ( ~ l1_struct_0('#skF_9')
      | ~ m1_subset_1('#skF_7'('#skF_9',B_852),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0('#skF_10','#skF_9')
      | ~ v7_waybel_0('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9')
      | k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_852))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_852))
      | ~ l1_waybel_0(B_852,'#skF_9')
      | ~ v7_waybel_0(B_852)
      | ~ v4_orders_2(B_852)
      | v2_struct_0(B_852) ) ),
    inference(resolution,[status(thm)],[c_3001,c_2725])).

tff(c_3006,plain,(
    ! [B_852] :
      ( ~ m1_subset_1('#skF_7'('#skF_9',B_852),u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_10')
      | v2_struct_0('#skF_9')
      | k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_852))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_852))
      | ~ l1_waybel_0(B_852,'#skF_9')
      | ~ v7_waybel_0(B_852)
      | ~ v4_orders_2(B_852)
      | v2_struct_0(B_852) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2546,c_2552,c_2554,c_2981,c_3003])).

tff(c_3008,plain,(
    ! [B_853] :
      ( ~ m1_subset_1('#skF_7'('#skF_9',B_853),u1_struct_0('#skF_9'))
      | k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_853))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_853))
      | ~ l1_waybel_0(B_853,'#skF_9')
      | ~ v7_waybel_0(B_853)
      | ~ v4_orders_2(B_853)
      | v2_struct_0(B_853) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2541,c_3006])).

tff(c_3012,plain,(
    ! [B_172] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ v1_compts_1('#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_3008])).

tff(c_3015,plain,(
    ! [B_172] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2542,c_3012])).

tff(c_3018,plain,(
    ! [B_857] :
      ( k10_yellow_6('#skF_9','#skF_6'('#skF_9','#skF_10','#skF_7'('#skF_9',B_857))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_857))
      | ~ l1_waybel_0(B_857,'#skF_9')
      | ~ v7_waybel_0(B_857)
      | ~ v4_orders_2(B_857)
      | v2_struct_0(B_857) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3015])).

tff(c_2765,plain,(
    ! [C_751,A_752,B_753] :
      ( r2_hidden(C_751,k10_yellow_6(A_752,'#skF_6'(A_752,B_753,C_751)))
      | ~ r3_waybel_9(A_752,B_753,C_751)
      | ~ m1_subset_1(C_751,u1_struct_0(A_752))
      | ~ l1_waybel_0(B_753,A_752)
      | ~ v7_waybel_0(B_753)
      | ~ v4_orders_2(B_753)
      | v2_struct_0(B_753)
      | ~ l1_pre_topc(A_752)
      | ~ v2_pre_topc(A_752)
      | v2_struct_0(A_752) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_2780,plain,(
    ! [A_752,B_753,C_751] :
      ( ~ r1_tarski(k10_yellow_6(A_752,'#skF_6'(A_752,B_753,C_751)),C_751)
      | ~ r3_waybel_9(A_752,B_753,C_751)
      | ~ m1_subset_1(C_751,u1_struct_0(A_752))
      | ~ l1_waybel_0(B_753,A_752)
      | ~ v7_waybel_0(B_753)
      | ~ v4_orders_2(B_753)
      | v2_struct_0(B_753)
      | ~ l1_pre_topc(A_752)
      | ~ v2_pre_topc(A_752)
      | v2_struct_0(A_752) ) ),
    inference(resolution,[status(thm)],[c_2765,c_14])).

tff(c_3044,plain,(
    ! [B_857] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_7'('#skF_9',B_857))
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_857))
      | ~ m1_subset_1('#skF_7'('#skF_9',B_857),u1_struct_0('#skF_9'))
      | ~ l1_waybel_0('#skF_10','#skF_9')
      | ~ v7_waybel_0('#skF_10')
      | ~ v4_orders_2('#skF_10')
      | v2_struct_0('#skF_10')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_857))
      | ~ l1_waybel_0(B_857,'#skF_9')
      | ~ v7_waybel_0(B_857)
      | ~ v4_orders_2(B_857)
      | v2_struct_0(B_857) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3018,c_2780])).

tff(c_3085,plain,(
    ! [B_857] :
      ( ~ m1_subset_1('#skF_7'('#skF_9',B_857),u1_struct_0('#skF_9'))
      | v2_struct_0('#skF_10')
      | v2_struct_0('#skF_9')
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_857))
      | ~ l1_waybel_0(B_857,'#skF_9')
      | ~ v7_waybel_0(B_857)
      | ~ v4_orders_2(B_857)
      | v2_struct_0(B_857) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2546,c_2552,c_2554,c_8,c_3044])).

tff(c_3106,plain,(
    ! [B_858] :
      ( ~ m1_subset_1('#skF_7'('#skF_9',B_858),u1_struct_0('#skF_9'))
      | ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_858))
      | ~ l1_waybel_0(B_858,'#skF_9')
      | ~ v7_waybel_0(B_858)
      | ~ v4_orders_2(B_858)
      | v2_struct_0(B_858) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2541,c_3085])).

tff(c_3110,plain,(
    ! [B_172] :
      ( ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | ~ v1_compts_1('#skF_9')
      | ~ l1_pre_topc('#skF_9')
      | ~ v2_pre_topc('#skF_9')
      | v2_struct_0('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_78,c_3106])).

tff(c_3113,plain,(
    ! [B_172] :
      ( ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_172))
      | ~ l1_waybel_0(B_172,'#skF_9')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172)
      | v2_struct_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2542,c_3110])).

tff(c_3115,plain,(
    ! [B_859] :
      ( ~ r3_waybel_9('#skF_9','#skF_10','#skF_7'('#skF_9',B_859))
      | ~ l1_waybel_0(B_859,'#skF_9')
      | ~ v7_waybel_0(B_859)
      | ~ v4_orders_2(B_859)
      | v2_struct_0(B_859) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_3113])).

tff(c_3119,plain,
    ( ~ l1_waybel_0('#skF_10','#skF_9')
    | ~ v7_waybel_0('#skF_10')
    | ~ v4_orders_2('#skF_10')
    | v2_struct_0('#skF_10')
    | ~ v1_compts_1('#skF_9')
    | ~ l1_pre_topc('#skF_9')
    | ~ v2_pre_topc('#skF_9')
    | v2_struct_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_76,c_3115])).

tff(c_3122,plain,
    ( v2_struct_0('#skF_10')
    | v2_struct_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_2542,c_2546,c_2552,c_2554,c_3119])).

tff(c_3124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_2541,c_3122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:06:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.65/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.64  
% 7.95/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.95/2.64  %$ r3_waybel_9 > r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_6 > #skF_8 > #skF_4 > #skF_10 > #skF_2 > #skF_5 > #skF_9 > #skF_11 > #skF_3 > #skF_7 > #skF_1
% 7.95/2.64  
% 7.95/2.64  %Foreground sorts:
% 7.95/2.64  
% 7.95/2.64  
% 7.95/2.64  %Background operators:
% 7.95/2.64  
% 7.95/2.64  
% 7.95/2.64  %Foreground operators:
% 7.95/2.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.95/2.64  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 7.95/2.64  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.95/2.64  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 7.95/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.95/2.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.95/2.64  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.95/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.95/2.64  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 7.95/2.64  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 7.95/2.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.95/2.64  tff('#skF_8', type, '#skF_8': $i > $i).
% 7.95/2.64  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 7.95/2.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.95/2.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.95/2.64  tff('#skF_10', type, '#skF_10': $i).
% 7.95/2.64  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 7.95/2.64  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 7.95/2.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.95/2.64  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.95/2.64  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 7.95/2.64  tff('#skF_9', type, '#skF_9': $i).
% 7.95/2.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.95/2.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.95/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.95/2.64  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 7.95/2.64  tff('#skF_11', type, '#skF_11': $i > $i).
% 7.95/2.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.95/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.95/2.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.95/2.64  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.95/2.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.95/2.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.95/2.64  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 7.95/2.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.95/2.64  
% 8.31/2.68  tff(f_297, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow19)).
% 8.31/2.68  tff(f_272, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_yellow19)).
% 8.31/2.68  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 8.31/2.68  tff(f_127, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 8.31/2.68  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.31/2.68  tff(f_101, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 8.31/2.68  tff(f_42, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 8.31/2.68  tff(f_219, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_waybel_9)).
% 8.31/2.68  tff(f_195, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> (![D]: (m1_connsp_2(D, A, C) => r2_waybel_0(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_waybel_9)).
% 8.31/2.68  tff(f_150, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (r2_waybel_0(A, C, D) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_6)).
% 8.31/2.68  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.31/2.68  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.31/2.68  tff(f_83, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 8.31/2.68  tff(f_47, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 8.31/2.68  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_yellow_6)).
% 8.31/2.68  tff(f_248, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 8.31/2.68  tff(c_84, plain, (~v2_struct_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.68  tff(c_94, plain, (~v2_struct_0('#skF_10') | ~v1_compts_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.68  tff(c_122, plain, (~v1_compts_1('#skF_9')), inference(splitLeft, [status(thm)], [c_94])).
% 8.31/2.68  tff(c_82, plain, (v2_pre_topc('#skF_9')), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.68  tff(c_80, plain, (l1_pre_topc('#skF_9')), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.68  tff(c_72, plain, (![A_165]: (v4_orders_2('#skF_8'(A_165)) | v1_compts_1(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.31/2.68  tff(c_70, plain, (![A_165]: (v7_waybel_0('#skF_8'(A_165)) | v1_compts_1(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.31/2.68  tff(c_68, plain, (![A_165]: (l1_waybel_0('#skF_8'(A_165), A_165) | v1_compts_1(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.31/2.68  tff(c_16, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_pre_topc(A_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.31/2.68  tff(c_120, plain, (![B_184]: (v1_compts_1('#skF_9') | m2_yellow_6('#skF_11'(B_184), '#skF_9', B_184) | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.68  tff(c_219, plain, (![B_184]: (m2_yellow_6('#skF_11'(B_184), '#skF_9', B_184) | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(negUnitSimplification, [status(thm)], [c_122, c_120])).
% 8.31/2.68  tff(c_223, plain, (![C_229, A_230, B_231]: (v7_waybel_0(C_229) | ~m2_yellow_6(C_229, A_230, B_231) | ~l1_waybel_0(B_231, A_230) | ~v7_waybel_0(B_231) | ~v4_orders_2(B_231) | v2_struct_0(B_231) | ~l1_struct_0(A_230) | v2_struct_0(A_230))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.31/2.68  tff(c_226, plain, (![B_184]: (v7_waybel_0('#skF_11'(B_184)) | ~l1_struct_0('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(resolution, [status(thm)], [c_219, c_223])).
% 8.31/2.68  tff(c_229, plain, (![B_184]: (v7_waybel_0('#skF_11'(B_184)) | ~l1_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(negUnitSimplification, [status(thm)], [c_84, c_226])).
% 8.31/2.68  tff(c_230, plain, (~l1_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_229])).
% 8.31/2.68  tff(c_240, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_16, c_230])).
% 8.31/2.68  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_240])).
% 8.31/2.68  tff(c_246, plain, (l1_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_229])).
% 8.31/2.68  tff(c_248, plain, (![C_236, A_237, B_238]: (v4_orders_2(C_236) | ~m2_yellow_6(C_236, A_237, B_238) | ~l1_waybel_0(B_238, A_237) | ~v7_waybel_0(B_238) | ~v4_orders_2(B_238) | v2_struct_0(B_238) | ~l1_struct_0(A_237) | v2_struct_0(A_237))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.31/2.68  tff(c_251, plain, (![B_184]: (v4_orders_2('#skF_11'(B_184)) | ~l1_struct_0('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(resolution, [status(thm)], [c_219, c_248])).
% 8.31/2.68  tff(c_254, plain, (![B_184]: (v4_orders_2('#skF_11'(B_184)) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_251])).
% 8.31/2.68  tff(c_255, plain, (![B_184]: (v4_orders_2('#skF_11'(B_184)) | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(negUnitSimplification, [status(thm)], [c_84, c_254])).
% 8.31/2.68  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.31/2.68  tff(c_275, plain, (![A_248, B_249]: (m1_subset_1(k10_yellow_6(A_248, B_249), k1_zfmisc_1(u1_struct_0(A_248))) | ~l1_waybel_0(B_249, A_248) | ~v7_waybel_0(B_249) | ~v4_orders_2(B_249) | v2_struct_0(B_249) | ~l1_pre_topc(A_248) | ~v2_pre_topc(A_248) | v2_struct_0(A_248))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.31/2.68  tff(c_12, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.31/2.68  tff(c_321, plain, (![A_267, A_268, B_269]: (m1_subset_1(A_267, u1_struct_0(A_268)) | ~r2_hidden(A_267, k10_yellow_6(A_268, B_269)) | ~l1_waybel_0(B_269, A_268) | ~v7_waybel_0(B_269) | ~v4_orders_2(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268))), inference(resolution, [status(thm)], [c_275, c_12])).
% 8.31/2.68  tff(c_331, plain, (![A_268, B_269, B_2]: (m1_subset_1('#skF_1'(k10_yellow_6(A_268, B_269), B_2), u1_struct_0(A_268)) | ~l1_waybel_0(B_269, A_268) | ~v7_waybel_0(B_269) | ~v4_orders_2(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268) | r1_tarski(k10_yellow_6(A_268, B_269), B_2))), inference(resolution, [status(thm)], [c_6, c_321])).
% 8.31/2.68  tff(c_338, plain, (![A_280, B_281, C_282]: (r3_waybel_9(A_280, B_281, C_282) | ~r2_hidden(C_282, k10_yellow_6(A_280, B_281)) | ~m1_subset_1(C_282, u1_struct_0(A_280)) | ~l1_waybel_0(B_281, A_280) | ~v7_waybel_0(B_281) | ~v4_orders_2(B_281) | v2_struct_0(B_281) | ~l1_pre_topc(A_280) | ~v2_pre_topc(A_280) | v2_struct_0(A_280))), inference(cnfTransformation, [status(thm)], [f_219])).
% 8.31/2.68  tff(c_446, plain, (![A_329, B_330, B_331]: (r3_waybel_9(A_329, B_330, '#skF_1'(k10_yellow_6(A_329, B_330), B_331)) | ~m1_subset_1('#skF_1'(k10_yellow_6(A_329, B_330), B_331), u1_struct_0(A_329)) | ~l1_waybel_0(B_330, A_329) | ~v7_waybel_0(B_330) | ~v4_orders_2(B_330) | v2_struct_0(B_330) | ~l1_pre_topc(A_329) | ~v2_pre_topc(A_329) | v2_struct_0(A_329) | r1_tarski(k10_yellow_6(A_329, B_330), B_331))), inference(resolution, [status(thm)], [c_6, c_338])).
% 8.31/2.69  tff(c_449, plain, (![A_268, B_269, B_2]: (r3_waybel_9(A_268, B_269, '#skF_1'(k10_yellow_6(A_268, B_269), B_2)) | ~l1_waybel_0(B_269, A_268) | ~v7_waybel_0(B_269) | ~v4_orders_2(B_269) | v2_struct_0(B_269) | ~l1_pre_topc(A_268) | ~v2_pre_topc(A_268) | v2_struct_0(A_268) | r1_tarski(k10_yellow_6(A_268, B_269), B_2))), inference(resolution, [status(thm)], [c_331, c_446])).
% 8.31/2.69  tff(c_58, plain, (![A_122, B_134, C_140]: (m1_connsp_2('#skF_5'(A_122, B_134, C_140), A_122, C_140) | r3_waybel_9(A_122, B_134, C_140) | ~m1_subset_1(C_140, u1_struct_0(A_122)) | ~l1_waybel_0(B_134, A_122) | v2_struct_0(B_134) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_195])).
% 8.31/2.69  tff(c_334, plain, (![A_276, B_277, D_278, C_279]: (r2_waybel_0(A_276, B_277, D_278) | ~m1_connsp_2(D_278, A_276, C_279) | ~r3_waybel_9(A_276, B_277, C_279) | ~m1_subset_1(C_279, u1_struct_0(A_276)) | ~l1_waybel_0(B_277, A_276) | v2_struct_0(B_277) | ~l1_pre_topc(A_276) | ~v2_pre_topc(A_276) | v2_struct_0(A_276))), inference(cnfTransformation, [status(thm)], [f_195])).
% 8.31/2.69  tff(c_432, plain, (![A_318, B_319, B_320, C_321]: (r2_waybel_0(A_318, B_319, '#skF_5'(A_318, B_320, C_321)) | ~r3_waybel_9(A_318, B_319, C_321) | ~l1_waybel_0(B_319, A_318) | v2_struct_0(B_319) | r3_waybel_9(A_318, B_320, C_321) | ~m1_subset_1(C_321, u1_struct_0(A_318)) | ~l1_waybel_0(B_320, A_318) | v2_struct_0(B_320) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318))), inference(resolution, [status(thm)], [c_58, c_334])).
% 8.31/2.69  tff(c_48, plain, (![A_104, B_112, D_118, C_116]: (r2_waybel_0(A_104, B_112, D_118) | ~r2_waybel_0(A_104, C_116, D_118) | ~m2_yellow_6(C_116, A_104, B_112) | ~l1_waybel_0(B_112, A_104) | ~v7_waybel_0(B_112) | ~v4_orders_2(B_112) | v2_struct_0(B_112) | ~l1_struct_0(A_104) | v2_struct_0(A_104))), inference(cnfTransformation, [status(thm)], [f_150])).
% 8.31/2.69  tff(c_565, plain, (![B_403, B_402, C_400, A_399, B_401]: (r2_waybel_0(A_399, B_402, '#skF_5'(A_399, B_403, C_400)) | ~m2_yellow_6(B_401, A_399, B_402) | ~l1_waybel_0(B_402, A_399) | ~v7_waybel_0(B_402) | ~v4_orders_2(B_402) | v2_struct_0(B_402) | ~l1_struct_0(A_399) | ~r3_waybel_9(A_399, B_401, C_400) | ~l1_waybel_0(B_401, A_399) | v2_struct_0(B_401) | r3_waybel_9(A_399, B_403, C_400) | ~m1_subset_1(C_400, u1_struct_0(A_399)) | ~l1_waybel_0(B_403, A_399) | v2_struct_0(B_403) | ~l1_pre_topc(A_399) | ~v2_pre_topc(A_399) | v2_struct_0(A_399))), inference(resolution, [status(thm)], [c_432, c_48])).
% 8.31/2.69  tff(c_569, plain, (![B_184, B_403, C_400]: (r2_waybel_0('#skF_9', B_184, '#skF_5'('#skF_9', B_403, C_400)) | ~l1_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', '#skF_11'(B_184), C_400) | ~l1_waybel_0('#skF_11'(B_184), '#skF_9') | v2_struct_0('#skF_11'(B_184)) | r3_waybel_9('#skF_9', B_403, C_400) | ~m1_subset_1(C_400, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_403, '#skF_9') | v2_struct_0(B_403) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(resolution, [status(thm)], [c_219, c_565])).
% 8.31/2.69  tff(c_573, plain, (![B_184, B_403, C_400]: (r2_waybel_0('#skF_9', B_184, '#skF_5'('#skF_9', B_403, C_400)) | ~r3_waybel_9('#skF_9', '#skF_11'(B_184), C_400) | ~l1_waybel_0('#skF_11'(B_184), '#skF_9') | v2_struct_0('#skF_11'(B_184)) | r3_waybel_9('#skF_9', B_403, C_400) | ~m1_subset_1(C_400, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_403, '#skF_9') | v2_struct_0(B_403) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_246, c_569])).
% 8.31/2.69  tff(c_575, plain, (![B_404, B_405, C_406]: (r2_waybel_0('#skF_9', B_404, '#skF_5'('#skF_9', B_405, C_406)) | ~r3_waybel_9('#skF_9', '#skF_11'(B_404), C_406) | ~l1_waybel_0('#skF_11'(B_404), '#skF_9') | v2_struct_0('#skF_11'(B_404)) | r3_waybel_9('#skF_9', B_405, C_406) | ~m1_subset_1(C_406, u1_struct_0('#skF_9')) | ~l1_waybel_0(B_405, '#skF_9') | v2_struct_0(B_405) | ~l1_waybel_0(B_404, '#skF_9') | ~v7_waybel_0(B_404) | ~v4_orders_2(B_404) | v2_struct_0(B_404))), inference(negUnitSimplification, [status(thm)], [c_84, c_573])).
% 8.31/2.69  tff(c_581, plain, (![B_404, B_405, B_2]: (r2_waybel_0('#skF_9', B_404, '#skF_5'('#skF_9', B_405, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_404)), B_2))) | r3_waybel_9('#skF_9', B_405, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_404)), B_2)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_404)), B_2), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_405, '#skF_9') | v2_struct_0(B_405) | ~l1_waybel_0(B_404, '#skF_9') | ~v7_waybel_0(B_404) | ~v4_orders_2(B_404) | v2_struct_0(B_404) | ~l1_waybel_0('#skF_11'(B_404), '#skF_9') | ~v7_waybel_0('#skF_11'(B_404)) | ~v4_orders_2('#skF_11'(B_404)) | v2_struct_0('#skF_11'(B_404)) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9') | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'(B_404)), B_2))), inference(resolution, [status(thm)], [c_449, c_575])).
% 8.31/2.69  tff(c_591, plain, (![B_404, B_405, B_2]: (r2_waybel_0('#skF_9', B_404, '#skF_5'('#skF_9', B_405, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_404)), B_2))) | r3_waybel_9('#skF_9', B_405, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_404)), B_2)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_404)), B_2), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_405, '#skF_9') | v2_struct_0(B_405) | ~l1_waybel_0(B_404, '#skF_9') | ~v7_waybel_0(B_404) | ~v4_orders_2(B_404) | v2_struct_0(B_404) | ~l1_waybel_0('#skF_11'(B_404), '#skF_9') | ~v7_waybel_0('#skF_11'(B_404)) | ~v4_orders_2('#skF_11'(B_404)) | v2_struct_0('#skF_11'(B_404)) | v2_struct_0('#skF_9') | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'(B_404)), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_581])).
% 8.31/2.69  tff(c_626, plain, (![B_436, B_437, B_438]: (r2_waybel_0('#skF_9', B_436, '#skF_5'('#skF_9', B_437, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_436)), B_438))) | r3_waybel_9('#skF_9', B_437, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_436)), B_438)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_436)), B_438), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_437, '#skF_9') | v2_struct_0(B_437) | ~l1_waybel_0(B_436, '#skF_9') | ~v7_waybel_0(B_436) | ~v4_orders_2(B_436) | v2_struct_0(B_436) | ~l1_waybel_0('#skF_11'(B_436), '#skF_9') | ~v7_waybel_0('#skF_11'(B_436)) | ~v4_orders_2('#skF_11'(B_436)) | v2_struct_0('#skF_11'(B_436)) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'(B_436)), B_438))), inference(negUnitSimplification, [status(thm)], [c_84, c_591])).
% 8.31/2.69  tff(c_56, plain, (![A_122, B_134, C_140]: (~r2_waybel_0(A_122, B_134, '#skF_5'(A_122, B_134, C_140)) | r3_waybel_9(A_122, B_134, C_140) | ~m1_subset_1(C_140, u1_struct_0(A_122)) | ~l1_waybel_0(B_134, A_122) | v2_struct_0(B_134) | ~l1_pre_topc(A_122) | ~v2_pre_topc(A_122) | v2_struct_0(A_122))), inference(cnfTransformation, [status(thm)], [f_195])).
% 8.31/2.69  tff(c_630, plain, (![B_437, B_438]: (~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9') | r3_waybel_9('#skF_9', B_437, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_437)), B_438)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_437)), B_438), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_437, '#skF_9') | ~v7_waybel_0(B_437) | ~v4_orders_2(B_437) | v2_struct_0(B_437) | ~l1_waybel_0('#skF_11'(B_437), '#skF_9') | ~v7_waybel_0('#skF_11'(B_437)) | ~v4_orders_2('#skF_11'(B_437)) | v2_struct_0('#skF_11'(B_437)) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'(B_437)), B_438))), inference(resolution, [status(thm)], [c_626, c_56])).
% 8.31/2.69  tff(c_635, plain, (![B_437, B_438]: (v2_struct_0('#skF_9') | r3_waybel_9('#skF_9', B_437, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_437)), B_438)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_437)), B_438), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_437, '#skF_9') | ~v7_waybel_0(B_437) | ~v4_orders_2(B_437) | v2_struct_0(B_437) | ~l1_waybel_0('#skF_11'(B_437), '#skF_9') | ~v7_waybel_0('#skF_11'(B_437)) | ~v4_orders_2('#skF_11'(B_437)) | v2_struct_0('#skF_11'(B_437)) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'(B_437)), B_438))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_630])).
% 8.31/2.69  tff(c_642, plain, (![B_442, B_443]: (r3_waybel_9('#skF_9', B_442, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_442)), B_443)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_442)), B_443), u1_struct_0('#skF_9')) | ~l1_waybel_0(B_442, '#skF_9') | ~v7_waybel_0(B_442) | ~v4_orders_2(B_442) | v2_struct_0(B_442) | ~l1_waybel_0('#skF_11'(B_442), '#skF_9') | ~v7_waybel_0('#skF_11'(B_442)) | ~v4_orders_2('#skF_11'(B_442)) | v2_struct_0('#skF_11'(B_442)) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'(B_442)), B_443))), inference(negUnitSimplification, [status(thm)], [c_84, c_635])).
% 8.31/2.69  tff(c_645, plain, (![B_442, B_2]: (r3_waybel_9('#skF_9', B_442, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_442)), B_2)) | ~l1_waybel_0(B_442, '#skF_9') | ~v7_waybel_0(B_442) | ~v4_orders_2(B_442) | v2_struct_0(B_442) | ~l1_waybel_0('#skF_11'(B_442), '#skF_9') | ~v7_waybel_0('#skF_11'(B_442)) | ~v4_orders_2('#skF_11'(B_442)) | v2_struct_0('#skF_11'(B_442)) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9') | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'(B_442)), B_2))), inference(resolution, [status(thm)], [c_331, c_642])).
% 8.31/2.69  tff(c_648, plain, (![B_442, B_2]: (r3_waybel_9('#skF_9', B_442, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_442)), B_2)) | ~l1_waybel_0(B_442, '#skF_9') | ~v7_waybel_0(B_442) | ~v4_orders_2(B_442) | v2_struct_0(B_442) | ~l1_waybel_0('#skF_11'(B_442), '#skF_9') | ~v7_waybel_0('#skF_11'(B_442)) | ~v4_orders_2('#skF_11'(B_442)) | v2_struct_0('#skF_11'(B_442)) | v2_struct_0('#skF_9') | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'(B_442)), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_645])).
% 8.31/2.69  tff(c_650, plain, (![B_444, B_445]: (r3_waybel_9('#skF_9', B_444, '#skF_1'(k10_yellow_6('#skF_9', '#skF_11'(B_444)), B_445)) | ~l1_waybel_0(B_444, '#skF_9') | ~v7_waybel_0(B_444) | ~v4_orders_2(B_444) | v2_struct_0(B_444) | ~l1_waybel_0('#skF_11'(B_444), '#skF_9') | ~v7_waybel_0('#skF_11'(B_444)) | ~v4_orders_2('#skF_11'(B_444)) | v2_struct_0('#skF_11'(B_444)) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'(B_444)), B_445))), inference(negUnitSimplification, [status(thm)], [c_84, c_648])).
% 8.31/2.69  tff(c_66, plain, (![A_165, C_175]: (~r3_waybel_9(A_165, '#skF_8'(A_165), C_175) | ~m1_subset_1(C_175, u1_struct_0(A_165)) | v1_compts_1(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.31/2.69  tff(c_657, plain, (![B_445]: (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9')) | ~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9') | ~v7_waybel_0('#skF_11'('#skF_8'('#skF_9'))) | ~v4_orders_2('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(resolution, [status(thm)], [c_650, c_66])).
% 8.31/2.69  tff(c_661, plain, (![B_445]: (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | v1_compts_1('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9')) | ~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9') | ~v7_waybel_0('#skF_11'('#skF_8'('#skF_9'))) | ~v4_orders_2('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_657])).
% 8.31/2.69  tff(c_662, plain, (![B_445]: (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9')) | ~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9') | ~v7_waybel_0('#skF_11'('#skF_8'('#skF_9'))) | ~v4_orders_2('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_661])).
% 8.31/2.69  tff(c_663, plain, (~v4_orders_2('#skF_11'('#skF_8'('#skF_9')))), inference(splitLeft, [status(thm)], [c_662])).
% 8.31/2.69  tff(c_667, plain, (~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9'))), inference(resolution, [status(thm)], [c_255, c_663])).
% 8.31/2.69  tff(c_673, plain, (~v4_orders_2('#skF_8'('#skF_9'))), inference(splitLeft, [status(thm)], [c_667])).
% 8.31/2.69  tff(c_676, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_72, c_673])).
% 8.31/2.69  tff(c_679, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_676])).
% 8.31/2.69  tff(c_681, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_679])).
% 8.31/2.69  tff(c_682, plain, (~v7_waybel_0('#skF_8'('#skF_9')) | ~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | v2_struct_0('#skF_8'('#skF_9'))), inference(splitRight, [status(thm)], [c_667])).
% 8.31/2.69  tff(c_699, plain, (~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9')), inference(splitLeft, [status(thm)], [c_682])).
% 8.31/2.69  tff(c_702, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_68, c_699])).
% 8.31/2.69  tff(c_705, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_702])).
% 8.31/2.69  tff(c_707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_705])).
% 8.31/2.69  tff(c_708, plain, (~v7_waybel_0('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9'))), inference(splitRight, [status(thm)], [c_682])).
% 8.31/2.69  tff(c_710, plain, (~v7_waybel_0('#skF_8'('#skF_9'))), inference(splitLeft, [status(thm)], [c_708])).
% 8.31/2.69  tff(c_713, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_70, c_710])).
% 8.31/2.69  tff(c_716, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_713])).
% 8.31/2.69  tff(c_718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_716])).
% 8.31/2.69  tff(c_719, plain, (v2_struct_0('#skF_8'('#skF_9'))), inference(splitRight, [status(thm)], [c_708])).
% 8.31/2.69  tff(c_74, plain, (![A_165]: (~v2_struct_0('#skF_8'(A_165)) | v1_compts_1(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.31/2.69  tff(c_742, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_719, c_74])).
% 8.31/2.69  tff(c_745, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_742])).
% 8.31/2.69  tff(c_747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_745])).
% 8.31/2.69  tff(c_748, plain, (![B_445]: (~v7_waybel_0('#skF_11'('#skF_8'('#skF_9'))) | ~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9') | ~v4_orders_2('#skF_8'('#skF_9')) | ~v7_waybel_0('#skF_8'('#skF_9')) | ~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_8'('#skF_9')) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(splitRight, [status(thm)], [c_662])).
% 8.31/2.69  tff(c_765, plain, (~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9')), inference(splitLeft, [status(thm)], [c_748])).
% 8.31/2.69  tff(c_768, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_68, c_765])).
% 8.31/2.69  tff(c_771, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_768])).
% 8.31/2.69  tff(c_773, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_771])).
% 8.31/2.69  tff(c_775, plain, (l1_waybel_0('#skF_8'('#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_748])).
% 8.31/2.69  tff(c_245, plain, (![B_184]: (v7_waybel_0('#skF_11'(B_184)) | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(splitRight, [status(thm)], [c_229])).
% 8.31/2.69  tff(c_774, plain, (![B_445]: (~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | ~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9') | ~v7_waybel_0('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_8'('#skF_9')) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(splitRight, [status(thm)], [c_748])).
% 8.31/2.69  tff(c_776, plain, (~v7_waybel_0('#skF_11'('#skF_8'('#skF_9')))), inference(splitLeft, [status(thm)], [c_774])).
% 8.31/2.69  tff(c_779, plain, (~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9'))), inference(resolution, [status(thm)], [c_245, c_776])).
% 8.31/2.69  tff(c_782, plain, (~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_775, c_779])).
% 8.31/2.69  tff(c_788, plain, (~v4_orders_2('#skF_8'('#skF_9'))), inference(splitLeft, [status(thm)], [c_782])).
% 8.31/2.69  tff(c_791, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_72, c_788])).
% 8.31/2.69  tff(c_794, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_791])).
% 8.31/2.69  tff(c_796, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_794])).
% 8.31/2.69  tff(c_797, plain, (~v7_waybel_0('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9'))), inference(splitRight, [status(thm)], [c_782])).
% 8.31/2.69  tff(c_807, plain, (~v7_waybel_0('#skF_8'('#skF_9'))), inference(splitLeft, [status(thm)], [c_797])).
% 8.31/2.69  tff(c_810, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_70, c_807])).
% 8.31/2.69  tff(c_813, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_810])).
% 8.31/2.69  tff(c_815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_813])).
% 8.31/2.69  tff(c_816, plain, (v2_struct_0('#skF_8'('#skF_9'))), inference(splitRight, [status(thm)], [c_797])).
% 8.31/2.69  tff(c_820, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_816, c_74])).
% 8.31/2.69  tff(c_823, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_820])).
% 8.31/2.69  tff(c_825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_823])).
% 8.31/2.69  tff(c_826, plain, (![B_445]: (~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9') | ~v4_orders_2('#skF_8'('#skF_9')) | ~v7_waybel_0('#skF_8'('#skF_9')) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_8'('#skF_9')) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(splitRight, [status(thm)], [c_774])).
% 8.31/2.69  tff(c_833, plain, (~v7_waybel_0('#skF_8'('#skF_9'))), inference(splitLeft, [status(thm)], [c_826])).
% 8.31/2.69  tff(c_836, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_70, c_833])).
% 8.31/2.69  tff(c_839, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_836])).
% 8.31/2.69  tff(c_841, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_839])).
% 8.31/2.69  tff(c_843, plain, (v7_waybel_0('#skF_8'('#skF_9'))), inference(splitRight, [status(thm)], [c_826])).
% 8.31/2.69  tff(c_266, plain, (![C_244, A_245, B_246]: (l1_waybel_0(C_244, A_245) | ~m2_yellow_6(C_244, A_245, B_246) | ~l1_waybel_0(B_246, A_245) | ~v7_waybel_0(B_246) | ~v4_orders_2(B_246) | v2_struct_0(B_246) | ~l1_struct_0(A_245) | v2_struct_0(A_245))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.31/2.69  tff(c_269, plain, (![B_184]: (l1_waybel_0('#skF_11'(B_184), '#skF_9') | ~l1_struct_0('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(resolution, [status(thm)], [c_219, c_266])).
% 8.31/2.69  tff(c_272, plain, (![B_184]: (l1_waybel_0('#skF_11'(B_184), '#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_269])).
% 8.31/2.69  tff(c_273, plain, (![B_184]: (l1_waybel_0('#skF_11'(B_184), '#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(negUnitSimplification, [status(thm)], [c_84, c_272])).
% 8.31/2.69  tff(c_842, plain, (![B_445]: (~v4_orders_2('#skF_8'('#skF_9')) | ~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9') | v2_struct_0('#skF_8'('#skF_9')) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(splitRight, [status(thm)], [c_826])).
% 8.31/2.69  tff(c_852, plain, (~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9')), inference(splitLeft, [status(thm)], [c_842])).
% 8.31/2.69  tff(c_855, plain, (~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9'))), inference(resolution, [status(thm)], [c_273, c_852])).
% 8.31/2.69  tff(c_858, plain, (~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_843, c_775, c_855])).
% 8.31/2.69  tff(c_859, plain, (~v4_orders_2('#skF_8'('#skF_9'))), inference(splitLeft, [status(thm)], [c_858])).
% 8.31/2.69  tff(c_862, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_72, c_859])).
% 8.31/2.69  tff(c_865, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_862])).
% 8.31/2.69  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_865])).
% 8.31/2.69  tff(c_868, plain, (v2_struct_0('#skF_8'('#skF_9'))), inference(splitRight, [status(thm)], [c_858])).
% 8.31/2.69  tff(c_891, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_868, c_74])).
% 8.31/2.69  tff(c_894, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_891])).
% 8.31/2.69  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_894])).
% 8.31/2.69  tff(c_897, plain, (![B_445]: (~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_8'('#skF_9')) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(splitRight, [status(thm)], [c_842])).
% 8.31/2.69  tff(c_899, plain, (~v4_orders_2('#skF_8'('#skF_9'))), inference(splitLeft, [status(thm)], [c_897])).
% 8.31/2.69  tff(c_914, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_72, c_899])).
% 8.31/2.69  tff(c_917, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_914])).
% 8.31/2.69  tff(c_919, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_917])).
% 8.31/2.69  tff(c_921, plain, (v4_orders_2('#skF_8'('#skF_9'))), inference(splitRight, [status(thm)], [c_897])).
% 8.31/2.69  tff(c_920, plain, (![B_445]: (v2_struct_0('#skF_8'('#skF_9')) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(splitRight, [status(thm)], [c_897])).
% 8.31/2.69  tff(c_922, plain, (v2_struct_0('#skF_11'('#skF_8'('#skF_9')))), inference(splitLeft, [status(thm)], [c_920])).
% 8.31/2.69  tff(c_257, plain, (![C_240, A_241, B_242]: (~v2_struct_0(C_240) | ~m2_yellow_6(C_240, A_241, B_242) | ~l1_waybel_0(B_242, A_241) | ~v7_waybel_0(B_242) | ~v4_orders_2(B_242) | v2_struct_0(B_242) | ~l1_struct_0(A_241) | v2_struct_0(A_241))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.31/2.69  tff(c_260, plain, (![B_184]: (~v2_struct_0('#skF_11'(B_184)) | ~l1_struct_0('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(resolution, [status(thm)], [c_219, c_257])).
% 8.31/2.69  tff(c_263, plain, (![B_184]: (~v2_struct_0('#skF_11'(B_184)) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_260])).
% 8.31/2.69  tff(c_264, plain, (![B_184]: (~v2_struct_0('#skF_11'(B_184)) | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(negUnitSimplification, [status(thm)], [c_84, c_263])).
% 8.31/2.69  tff(c_925, plain, (~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9'))), inference(resolution, [status(thm)], [c_922, c_264])).
% 8.31/2.69  tff(c_928, plain, (v2_struct_0('#skF_8'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_921, c_843, c_775, c_925])).
% 8.31/2.69  tff(c_931, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_928, c_74])).
% 8.31/2.69  tff(c_934, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_931])).
% 8.31/2.69  tff(c_936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_934])).
% 8.31/2.69  tff(c_937, plain, (![B_445]: (v2_struct_0('#skF_8'('#skF_9')) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445), u1_struct_0('#skF_9')) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_445))), inference(splitRight, [status(thm)], [c_920])).
% 8.31/2.69  tff(c_958, plain, (v2_struct_0('#skF_8'('#skF_9'))), inference(splitLeft, [status(thm)], [c_937])).
% 8.31/2.69  tff(c_961, plain, (v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_958, c_74])).
% 8.31/2.69  tff(c_964, plain, (v1_compts_1('#skF_9') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_961])).
% 8.31/2.69  tff(c_966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_122, c_964])).
% 8.31/2.69  tff(c_968, plain, (~v2_struct_0('#skF_8'('#skF_9'))), inference(splitRight, [status(thm)], [c_937])).
% 8.31/2.69  tff(c_938, plain, (~v2_struct_0('#skF_11'('#skF_8'('#skF_9')))), inference(splitRight, [status(thm)], [c_920])).
% 8.31/2.69  tff(c_749, plain, (v4_orders_2('#skF_11'('#skF_8'('#skF_9')))), inference(splitRight, [status(thm)], [c_662])).
% 8.31/2.69  tff(c_827, plain, (v7_waybel_0('#skF_11'('#skF_8'('#skF_9')))), inference(splitRight, [status(thm)], [c_774])).
% 8.31/2.69  tff(c_898, plain, (l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9')), inference(splitRight, [status(thm)], [c_842])).
% 8.31/2.69  tff(c_38, plain, (![A_98, B_99]: (m1_subset_1(k10_yellow_6(A_98, B_99), k1_zfmisc_1(u1_struct_0(A_98))) | ~l1_waybel_0(B_99, A_98) | ~v7_waybel_0(B_99) | ~v4_orders_2(B_99) | v2_struct_0(B_99) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.31/2.69  tff(c_981, plain, (![B_490]: (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_490), u1_struct_0('#skF_9')) | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_490))), inference(splitRight, [status(thm)], [c_937])).
% 8.31/2.69  tff(c_985, plain, (![B_2]: (~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9') | ~v7_waybel_0('#skF_11'('#skF_8'('#skF_9'))) | ~v4_orders_2('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9') | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_2))), inference(resolution, [status(thm)], [c_331, c_981])).
% 8.31/2.69  tff(c_988, plain, (![B_2]: (v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_9') | r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_749, c_827, c_898, c_985])).
% 8.31/2.69  tff(c_989, plain, (![B_2]: (r1_tarski(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), B_2))), inference(negUnitSimplification, [status(thm)], [c_84, c_938, c_988])).
% 8.31/2.69  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.31/2.69  tff(c_10, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.31/2.69  tff(c_18, plain, (![A_14, B_58, C_80]: (m1_subset_1('#skF_3'(A_14, B_58, C_80), u1_struct_0(A_14)) | k10_yellow_6(A_14, B_58)=C_80 | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_waybel_0(B_58, A_14) | ~v7_waybel_0(B_58) | ~v4_orders_2(B_58) | v2_struct_0(B_58) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.31/2.69  tff(c_517, plain, (![A_353, B_354, D_355]: (m1_connsp_2('#skF_2'(A_353, B_354, k10_yellow_6(A_353, B_354), D_355), A_353, D_355) | r2_hidden(D_355, k10_yellow_6(A_353, B_354)) | ~m1_subset_1(D_355, u1_struct_0(A_353)) | ~m1_subset_1(k10_yellow_6(A_353, B_354), k1_zfmisc_1(u1_struct_0(A_353))) | ~l1_waybel_0(B_354, A_353) | ~v7_waybel_0(B_354) | ~v4_orders_2(B_354) | v2_struct_0(B_354) | ~l1_pre_topc(A_353) | ~v2_pre_topc(A_353) | v2_struct_0(A_353))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.31/2.69  tff(c_521, plain, (![A_356, B_357, D_358]: (m1_connsp_2('#skF_2'(A_356, B_357, k10_yellow_6(A_356, B_357), D_358), A_356, D_358) | r2_hidden(D_358, k10_yellow_6(A_356, B_357)) | ~m1_subset_1(D_358, u1_struct_0(A_356)) | ~l1_waybel_0(B_357, A_356) | ~v7_waybel_0(B_357) | ~v4_orders_2(B_357) | v2_struct_0(B_357) | ~l1_pre_topc(A_356) | ~v2_pre_topc(A_356) | v2_struct_0(A_356))), inference(resolution, [status(thm)], [c_38, c_517])).
% 8.31/2.69  tff(c_30, plain, (![A_14, B_58, C_80, E_97]: (r2_hidden('#skF_3'(A_14, B_58, C_80), C_80) | r1_waybel_0(A_14, B_58, E_97) | ~m1_connsp_2(E_97, A_14, '#skF_3'(A_14, B_58, C_80)) | k10_yellow_6(A_14, B_58)=C_80 | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_waybel_0(B_58, A_14) | ~v7_waybel_0(B_58) | ~v4_orders_2(B_58) | v2_struct_0(B_58) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.31/2.69  tff(c_1445, plain, (![A_591, B_592, C_593, B_594]: (r2_hidden('#skF_3'(A_591, B_592, C_593), C_593) | r1_waybel_0(A_591, B_592, '#skF_2'(A_591, B_594, k10_yellow_6(A_591, B_594), '#skF_3'(A_591, B_592, C_593))) | k10_yellow_6(A_591, B_592)=C_593 | ~m1_subset_1(C_593, k1_zfmisc_1(u1_struct_0(A_591))) | ~l1_waybel_0(B_592, A_591) | ~v7_waybel_0(B_592) | ~v4_orders_2(B_592) | v2_struct_0(B_592) | r2_hidden('#skF_3'(A_591, B_592, C_593), k10_yellow_6(A_591, B_594)) | ~m1_subset_1('#skF_3'(A_591, B_592, C_593), u1_struct_0(A_591)) | ~l1_waybel_0(B_594, A_591) | ~v7_waybel_0(B_594) | ~v4_orders_2(B_594) | v2_struct_0(B_594) | ~l1_pre_topc(A_591) | ~v2_pre_topc(A_591) | v2_struct_0(A_591))), inference(resolution, [status(thm)], [c_521, c_30])).
% 8.31/2.69  tff(c_34, plain, (![A_14, B_58, D_91]: (~r1_waybel_0(A_14, B_58, '#skF_2'(A_14, B_58, k10_yellow_6(A_14, B_58), D_91)) | r2_hidden(D_91, k10_yellow_6(A_14, B_58)) | ~m1_subset_1(D_91, u1_struct_0(A_14)) | ~m1_subset_1(k10_yellow_6(A_14, B_58), k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_waybel_0(B_58, A_14) | ~v7_waybel_0(B_58) | ~v4_orders_2(B_58) | v2_struct_0(B_58) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.31/2.69  tff(c_1472, plain, (![A_595, B_596, C_597]: (~m1_subset_1(k10_yellow_6(A_595, B_596), k1_zfmisc_1(u1_struct_0(A_595))) | r2_hidden('#skF_3'(A_595, B_596, C_597), C_597) | k10_yellow_6(A_595, B_596)=C_597 | ~m1_subset_1(C_597, k1_zfmisc_1(u1_struct_0(A_595))) | r2_hidden('#skF_3'(A_595, B_596, C_597), k10_yellow_6(A_595, B_596)) | ~m1_subset_1('#skF_3'(A_595, B_596, C_597), u1_struct_0(A_595)) | ~l1_waybel_0(B_596, A_595) | ~v7_waybel_0(B_596) | ~v4_orders_2(B_596) | v2_struct_0(B_596) | ~l1_pre_topc(A_595) | ~v2_pre_topc(A_595) | v2_struct_0(A_595))), inference(resolution, [status(thm)], [c_1445, c_34])).
% 8.31/2.69  tff(c_1492, plain, (![A_598, B_599, C_600]: (r2_hidden('#skF_3'(A_598, B_599, C_600), C_600) | k10_yellow_6(A_598, B_599)=C_600 | ~m1_subset_1(C_600, k1_zfmisc_1(u1_struct_0(A_598))) | r2_hidden('#skF_3'(A_598, B_599, C_600), k10_yellow_6(A_598, B_599)) | ~m1_subset_1('#skF_3'(A_598, B_599, C_600), u1_struct_0(A_598)) | ~l1_waybel_0(B_599, A_598) | ~v7_waybel_0(B_599) | ~v4_orders_2(B_599) | v2_struct_0(B_599) | ~l1_pre_topc(A_598) | ~v2_pre_topc(A_598) | v2_struct_0(A_598))), inference(resolution, [status(thm)], [c_38, c_1472])).
% 8.31/2.69  tff(c_60, plain, (![A_144, B_148, C_150]: (r3_waybel_9(A_144, B_148, C_150) | ~r2_hidden(C_150, k10_yellow_6(A_144, B_148)) | ~m1_subset_1(C_150, u1_struct_0(A_144)) | ~l1_waybel_0(B_148, A_144) | ~v7_waybel_0(B_148) | ~v4_orders_2(B_148) | v2_struct_0(B_148) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_219])).
% 8.31/2.69  tff(c_1533, plain, (![A_601, B_602, C_603]: (r3_waybel_9(A_601, B_602, '#skF_3'(A_601, B_602, C_603)) | r2_hidden('#skF_3'(A_601, B_602, C_603), C_603) | k10_yellow_6(A_601, B_602)=C_603 | ~m1_subset_1(C_603, k1_zfmisc_1(u1_struct_0(A_601))) | ~m1_subset_1('#skF_3'(A_601, B_602, C_603), u1_struct_0(A_601)) | ~l1_waybel_0(B_602, A_601) | ~v7_waybel_0(B_602) | ~v4_orders_2(B_602) | v2_struct_0(B_602) | ~l1_pre_topc(A_601) | ~v2_pre_topc(A_601) | v2_struct_0(A_601))), inference(resolution, [status(thm)], [c_1492, c_60])).
% 8.31/2.69  tff(c_1567, plain, (![A_608, B_609, C_610]: (r3_waybel_9(A_608, B_609, '#skF_3'(A_608, B_609, C_610)) | r2_hidden('#skF_3'(A_608, B_609, C_610), C_610) | k10_yellow_6(A_608, B_609)=C_610 | ~m1_subset_1(C_610, k1_zfmisc_1(u1_struct_0(A_608))) | ~l1_waybel_0(B_609, A_608) | ~v7_waybel_0(B_609) | ~v4_orders_2(B_609) | v2_struct_0(B_609) | ~l1_pre_topc(A_608) | ~v2_pre_topc(A_608) | v2_struct_0(A_608))), inference(resolution, [status(thm)], [c_18, c_1533])).
% 8.31/2.69  tff(c_1575, plain, (![A_611, B_612]: (r3_waybel_9(A_611, B_612, '#skF_3'(A_611, B_612, k1_xboole_0)) | r2_hidden('#skF_3'(A_611, B_612, k1_xboole_0), k1_xboole_0) | k10_yellow_6(A_611, B_612)=k1_xboole_0 | ~l1_waybel_0(B_612, A_611) | ~v7_waybel_0(B_612) | ~v4_orders_2(B_612) | v2_struct_0(B_612) | ~l1_pre_topc(A_611) | ~v2_pre_topc(A_611) | v2_struct_0(A_611))), inference(resolution, [status(thm)], [c_10, c_1567])).
% 8.31/2.69  tff(c_1604, plain, (![A_613]: (~m1_subset_1('#skF_3'(A_613, '#skF_8'(A_613), k1_xboole_0), u1_struct_0(A_613)) | v1_compts_1(A_613) | r2_hidden('#skF_3'(A_613, '#skF_8'(A_613), k1_xboole_0), k1_xboole_0) | k10_yellow_6(A_613, '#skF_8'(A_613))=k1_xboole_0 | ~l1_waybel_0('#skF_8'(A_613), A_613) | ~v7_waybel_0('#skF_8'(A_613)) | ~v4_orders_2('#skF_8'(A_613)) | v2_struct_0('#skF_8'(A_613)) | ~l1_pre_topc(A_613) | ~v2_pre_topc(A_613) | v2_struct_0(A_613))), inference(resolution, [status(thm)], [c_1575, c_66])).
% 8.31/2.69  tff(c_1608, plain, (![A_14]: (v1_compts_1(A_14) | r2_hidden('#skF_3'(A_14, '#skF_8'(A_14), k1_xboole_0), k1_xboole_0) | k10_yellow_6(A_14, '#skF_8'(A_14))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_14))) | ~l1_waybel_0('#skF_8'(A_14), A_14) | ~v7_waybel_0('#skF_8'(A_14)) | ~v4_orders_2('#skF_8'(A_14)) | v2_struct_0('#skF_8'(A_14)) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(resolution, [status(thm)], [c_18, c_1604])).
% 8.31/2.69  tff(c_1612, plain, (![A_614]: (v1_compts_1(A_614) | r2_hidden('#skF_3'(A_614, '#skF_8'(A_614), k1_xboole_0), k1_xboole_0) | k10_yellow_6(A_614, '#skF_8'(A_614))=k1_xboole_0 | ~l1_waybel_0('#skF_8'(A_614), A_614) | ~v7_waybel_0('#skF_8'(A_614)) | ~v4_orders_2('#skF_8'(A_614)) | v2_struct_0('#skF_8'(A_614)) | ~l1_pre_topc(A_614) | ~v2_pre_topc(A_614) | v2_struct_0(A_614))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1608])).
% 8.31/2.69  tff(c_14, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.31/2.69  tff(c_1619, plain, (![A_614]: (~r1_tarski(k1_xboole_0, '#skF_3'(A_614, '#skF_8'(A_614), k1_xboole_0)) | v1_compts_1(A_614) | k10_yellow_6(A_614, '#skF_8'(A_614))=k1_xboole_0 | ~l1_waybel_0('#skF_8'(A_614), A_614) | ~v7_waybel_0('#skF_8'(A_614)) | ~v4_orders_2('#skF_8'(A_614)) | v2_struct_0('#skF_8'(A_614)) | ~l1_pre_topc(A_614) | ~v2_pre_topc(A_614) | v2_struct_0(A_614))), inference(resolution, [status(thm)], [c_1612, c_14])).
% 8.31/2.69  tff(c_1627, plain, (![A_615]: (v1_compts_1(A_615) | k10_yellow_6(A_615, '#skF_8'(A_615))=k1_xboole_0 | ~l1_waybel_0('#skF_8'(A_615), A_615) | ~v7_waybel_0('#skF_8'(A_615)) | ~v4_orders_2('#skF_8'(A_615)) | v2_struct_0('#skF_8'(A_615)) | ~l1_pre_topc(A_615) | ~v2_pre_topc(A_615) | v2_struct_0(A_615))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1619])).
% 8.31/2.69  tff(c_1630, plain, (v1_compts_1('#skF_9') | k10_yellow_6('#skF_9', '#skF_8'('#skF_9'))=k1_xboole_0 | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9')) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_775, c_1627])).
% 8.31/2.69  tff(c_1636, plain, (v1_compts_1('#skF_9') | k10_yellow_6('#skF_9', '#skF_8'('#skF_9'))=k1_xboole_0 | v2_struct_0('#skF_8'('#skF_9')) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_921, c_843, c_1630])).
% 8.31/2.69  tff(c_1637, plain, (k10_yellow_6('#skF_9', '#skF_8'('#skF_9'))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_84, c_968, c_122, c_1636])).
% 8.31/2.69  tff(c_1475, plain, (![A_98, B_99, C_597]: (r2_hidden('#skF_3'(A_98, B_99, C_597), C_597) | k10_yellow_6(A_98, B_99)=C_597 | ~m1_subset_1(C_597, k1_zfmisc_1(u1_struct_0(A_98))) | r2_hidden('#skF_3'(A_98, B_99, C_597), k10_yellow_6(A_98, B_99)) | ~m1_subset_1('#skF_3'(A_98, B_99, C_597), u1_struct_0(A_98)) | ~l1_waybel_0(B_99, A_98) | ~v7_waybel_0(B_99) | ~v4_orders_2(B_99) | v2_struct_0(B_99) | ~l1_pre_topc(A_98) | ~v2_pre_topc(A_98) | v2_struct_0(A_98))), inference(resolution, [status(thm)], [c_38, c_1472])).
% 8.31/2.69  tff(c_1666, plain, (![C_597]: (r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_597), C_597) | k10_yellow_6('#skF_9', '#skF_8'('#skF_9'))=C_597 | ~m1_subset_1(C_597, k1_zfmisc_1(u1_struct_0('#skF_9'))) | r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_597), k1_xboole_0) | ~m1_subset_1('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_597), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9')) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1637, c_1475])).
% 8.31/2.69  tff(c_1740, plain, (![C_597]: (r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_597), C_597) | k1_xboole_0=C_597 | ~m1_subset_1(C_597, k1_zfmisc_1(u1_struct_0('#skF_9'))) | r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_597), k1_xboole_0) | ~m1_subset_1('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_597), u1_struct_0('#skF_9')) | v2_struct_0('#skF_8'('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_921, c_843, c_775, c_1637, c_1666])).
% 8.31/2.69  tff(c_2150, plain, (![C_639]: (r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_639), C_639) | k1_xboole_0=C_639 | ~m1_subset_1(C_639, k1_zfmisc_1(u1_struct_0('#skF_9'))) | r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_639), k1_xboole_0) | ~m1_subset_1('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_639), u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_84, c_968, c_1740])).
% 8.31/2.69  tff(c_2153, plain, (![C_80]: (r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_80), C_80) | k1_xboole_0=C_80 | r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_80), k1_xboole_0) | k10_yellow_6('#skF_9', '#skF_8'('#skF_9'))=C_80 | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0('#skF_9'))) | ~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9')) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_18, c_2150])).
% 8.31/2.69  tff(c_2156, plain, (![C_80]: (r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_80), C_80) | r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_80), k1_xboole_0) | k1_xboole_0=C_80 | ~m1_subset_1(C_80, k1_zfmisc_1(u1_struct_0('#skF_9'))) | v2_struct_0('#skF_8'('#skF_9')) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_921, c_843, c_775, c_1637, c_2153])).
% 8.31/2.69  tff(c_2178, plain, (![C_640]: (r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_640), C_640) | r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_640), k1_xboole_0) | k1_xboole_0=C_640 | ~m1_subset_1(C_640, k1_zfmisc_1(u1_struct_0('#skF_9'))))), inference(negUnitSimplification, [status(thm)], [c_84, c_968, c_2156])).
% 8.31/2.69  tff(c_2205, plain, (![C_640]: (~r1_tarski(k1_xboole_0, '#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_640)) | r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_640), C_640) | k1_xboole_0=C_640 | ~m1_subset_1(C_640, k1_zfmisc_1(u1_struct_0('#skF_9'))))), inference(resolution, [status(thm)], [c_2178, c_14])).
% 8.31/2.69  tff(c_2225, plain, (![C_641]: (r2_hidden('#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_641), C_641) | k1_xboole_0=C_641 | ~m1_subset_1(C_641, k1_zfmisc_1(u1_struct_0('#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_2205])).
% 8.31/2.69  tff(c_2265, plain, (![C_642]: (~r1_tarski(C_642, '#skF_3'('#skF_9', '#skF_8'('#skF_9'), C_642)) | k1_xboole_0=C_642 | ~m1_subset_1(C_642, k1_zfmisc_1(u1_struct_0('#skF_9'))))), inference(resolution, [status(thm)], [c_2225, c_14])).
% 8.31/2.69  tff(c_2283, plain, (k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9')))=k1_xboole_0 | ~m1_subset_1(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), k1_zfmisc_1(u1_struct_0('#skF_9')))), inference(resolution, [status(thm)], [c_989, c_2265])).
% 8.31/2.69  tff(c_2327, plain, (~m1_subset_1(k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9'))), k1_zfmisc_1(u1_struct_0('#skF_9')))), inference(splitLeft, [status(thm)], [c_2283])).
% 8.31/2.69  tff(c_2330, plain, (~l1_waybel_0('#skF_11'('#skF_8'('#skF_9')), '#skF_9') | ~v7_waybel_0('#skF_11'('#skF_8'('#skF_9'))) | ~v4_orders_2('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_38, c_2327])).
% 8.31/2.69  tff(c_2333, plain, (v2_struct_0('#skF_11'('#skF_8'('#skF_9'))) | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_749, c_827, c_898, c_2330])).
% 8.31/2.69  tff(c_2335, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_938, c_2333])).
% 8.31/2.69  tff(c_2336, plain, (k10_yellow_6('#skF_9', '#skF_11'('#skF_8'('#skF_9')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_2283])).
% 8.31/2.69  tff(c_108, plain, (![B_184]: (v1_compts_1('#skF_9') | v3_yellow_6('#skF_11'(B_184), '#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.69  tff(c_216, plain, (![B_184]: (v3_yellow_6('#skF_11'(B_184), '#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(negUnitSimplification, [status(thm)], [c_122, c_108])).
% 8.31/2.69  tff(c_279, plain, (![A_250, B_251]: (k10_yellow_6(A_250, B_251)!=k1_xboole_0 | ~v3_yellow_6(B_251, A_250) | ~l1_waybel_0(B_251, A_250) | ~v7_waybel_0(B_251) | ~v4_orders_2(B_251) | v2_struct_0(B_251) | ~l1_pre_topc(A_250) | ~v2_pre_topc(A_250) | v2_struct_0(A_250))), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.31/2.69  tff(c_282, plain, (![B_184]: (k10_yellow_6('#skF_9', '#skF_11'(B_184))!=k1_xboole_0 | ~l1_waybel_0('#skF_11'(B_184), '#skF_9') | ~v7_waybel_0('#skF_11'(B_184)) | ~v4_orders_2('#skF_11'(B_184)) | v2_struct_0('#skF_11'(B_184)) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(resolution, [status(thm)], [c_216, c_279])).
% 8.31/2.69  tff(c_285, plain, (![B_184]: (k10_yellow_6('#skF_9', '#skF_11'(B_184))!=k1_xboole_0 | ~l1_waybel_0('#skF_11'(B_184), '#skF_9') | ~v7_waybel_0('#skF_11'(B_184)) | ~v4_orders_2('#skF_11'(B_184)) | v2_struct_0('#skF_11'(B_184)) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_184, '#skF_9') | ~v7_waybel_0(B_184) | ~v4_orders_2(B_184) | v2_struct_0(B_184))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_282])).
% 8.31/2.69  tff(c_287, plain, (![B_252]: (k10_yellow_6('#skF_9', '#skF_11'(B_252))!=k1_xboole_0 | ~l1_waybel_0('#skF_11'(B_252), '#skF_9') | ~v7_waybel_0('#skF_11'(B_252)) | ~v4_orders_2('#skF_11'(B_252)) | v2_struct_0('#skF_11'(B_252)) | ~l1_waybel_0(B_252, '#skF_9') | ~v7_waybel_0(B_252) | ~v4_orders_2(B_252) | v2_struct_0(B_252))), inference(negUnitSimplification, [status(thm)], [c_84, c_285])).
% 8.31/2.69  tff(c_304, plain, (![B_259]: (k10_yellow_6('#skF_9', '#skF_11'(B_259))!=k1_xboole_0 | ~v7_waybel_0('#skF_11'(B_259)) | ~v4_orders_2('#skF_11'(B_259)) | v2_struct_0('#skF_11'(B_259)) | ~l1_waybel_0(B_259, '#skF_9') | ~v7_waybel_0(B_259) | ~v4_orders_2(B_259) | v2_struct_0(B_259))), inference(resolution, [status(thm)], [c_273, c_287])).
% 8.31/2.69  tff(c_309, plain, (![B_260]: (k10_yellow_6('#skF_9', '#skF_11'(B_260))!=k1_xboole_0 | ~v4_orders_2('#skF_11'(B_260)) | v2_struct_0('#skF_11'(B_260)) | ~l1_waybel_0(B_260, '#skF_9') | ~v7_waybel_0(B_260) | ~v4_orders_2(B_260) | v2_struct_0(B_260))), inference(resolution, [status(thm)], [c_245, c_304])).
% 8.31/2.69  tff(c_315, plain, (![B_265]: (k10_yellow_6('#skF_9', '#skF_11'(B_265))!=k1_xboole_0 | v2_struct_0('#skF_11'(B_265)) | ~l1_waybel_0(B_265, '#skF_9') | ~v7_waybel_0(B_265) | ~v4_orders_2(B_265) | v2_struct_0(B_265))), inference(resolution, [status(thm)], [c_255, c_309])).
% 8.31/2.69  tff(c_319, plain, (![B_265]: (k10_yellow_6('#skF_9', '#skF_11'(B_265))!=k1_xboole_0 | ~l1_waybel_0(B_265, '#skF_9') | ~v7_waybel_0(B_265) | ~v4_orders_2(B_265) | v2_struct_0(B_265))), inference(resolution, [status(thm)], [c_315, c_264])).
% 8.31/2.69  tff(c_2434, plain, (~l1_waybel_0('#skF_8'('#skF_9'), '#skF_9') | ~v7_waybel_0('#skF_8'('#skF_9')) | ~v4_orders_2('#skF_8'('#skF_9')) | v2_struct_0('#skF_8'('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2336, c_319])).
% 8.31/2.69  tff(c_2538, plain, (v2_struct_0('#skF_8'('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_921, c_843, c_775, c_2434])).
% 8.31/2.69  tff(c_2540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_968, c_2538])).
% 8.31/2.69  tff(c_2541, plain, (~v2_struct_0('#skF_10')), inference(splitRight, [status(thm)], [c_94])).
% 8.31/2.69  tff(c_2542, plain, (v1_compts_1('#skF_9')), inference(splitRight, [status(thm)], [c_94])).
% 8.31/2.69  tff(c_92, plain, (v4_orders_2('#skF_10') | ~v1_compts_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.69  tff(c_2543, plain, (~v1_compts_1('#skF_9')), inference(splitLeft, [status(thm)], [c_92])).
% 8.31/2.69  tff(c_2545, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2542, c_2543])).
% 8.31/2.69  tff(c_2546, plain, (v4_orders_2('#skF_10')), inference(splitRight, [status(thm)], [c_92])).
% 8.31/2.69  tff(c_90, plain, (v7_waybel_0('#skF_10') | ~v1_compts_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.69  tff(c_2552, plain, (v7_waybel_0('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_90])).
% 8.31/2.69  tff(c_88, plain, (l1_waybel_0('#skF_10', '#skF_9') | ~v1_compts_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.69  tff(c_2554, plain, (l1_waybel_0('#skF_10', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_88])).
% 8.31/2.69  tff(c_76, plain, (![A_165, B_172]: (r3_waybel_9(A_165, B_172, '#skF_7'(A_165, B_172)) | ~l1_waybel_0(B_172, A_165) | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~v1_compts_1(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.31/2.69  tff(c_78, plain, (![A_165, B_172]: (m1_subset_1('#skF_7'(A_165, B_172), u1_struct_0(A_165)) | ~l1_waybel_0(B_172, A_165) | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~v1_compts_1(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(cnfTransformation, [status(thm)], [f_272])).
% 8.31/2.69  tff(c_2707, plain, (![A_734, B_735, C_736]: (m2_yellow_6('#skF_6'(A_734, B_735, C_736), A_734, B_735) | ~r3_waybel_9(A_734, B_735, C_736) | ~m1_subset_1(C_736, u1_struct_0(A_734)) | ~l1_waybel_0(B_735, A_734) | ~v7_waybel_0(B_735) | ~v4_orders_2(B_735) | v2_struct_0(B_735) | ~l1_pre_topc(A_734) | ~v2_pre_topc(A_734) | v2_struct_0(A_734))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.31/2.69  tff(c_40, plain, (![C_103, A_100, B_101]: (l1_waybel_0(C_103, A_100) | ~m2_yellow_6(C_103, A_100, B_101) | ~l1_waybel_0(B_101, A_100) | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.31/2.69  tff(c_2788, plain, (![A_757, B_758, C_759]: (l1_waybel_0('#skF_6'(A_757, B_758, C_759), A_757) | ~l1_struct_0(A_757) | ~r3_waybel_9(A_757, B_758, C_759) | ~m1_subset_1(C_759, u1_struct_0(A_757)) | ~l1_waybel_0(B_758, A_757) | ~v7_waybel_0(B_758) | ~v4_orders_2(B_758) | v2_struct_0(B_758) | ~l1_pre_topc(A_757) | ~v2_pre_topc(A_757) | v2_struct_0(A_757))), inference(resolution, [status(thm)], [c_2707, c_40])).
% 8.31/2.69  tff(c_2936, plain, (![A_825, B_826, B_827]: (l1_waybel_0('#skF_6'(A_825, B_826, '#skF_7'(A_825, B_827)), A_825) | ~l1_struct_0(A_825) | ~r3_waybel_9(A_825, B_826, '#skF_7'(A_825, B_827)) | ~l1_waybel_0(B_826, A_825) | ~v7_waybel_0(B_826) | ~v4_orders_2(B_826) | v2_struct_0(B_826) | ~l1_waybel_0(B_827, A_825) | ~v7_waybel_0(B_827) | ~v4_orders_2(B_827) | v2_struct_0(B_827) | ~v1_compts_1(A_825) | ~l1_pre_topc(A_825) | ~v2_pre_topc(A_825) | v2_struct_0(A_825))), inference(resolution, [status(thm)], [c_78, c_2788])).
% 8.31/2.69  tff(c_50, plain, (![B_121, A_119]: (v3_yellow_6(B_121, A_119) | k10_yellow_6(A_119, B_121)=k1_xboole_0 | ~l1_waybel_0(B_121, A_119) | ~v7_waybel_0(B_121) | ~v4_orders_2(B_121) | v2_struct_0(B_121) | ~l1_pre_topc(A_119) | ~v2_pre_topc(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_172])).
% 8.31/2.69  tff(c_86, plain, (![C_183]: (~v3_yellow_6(C_183, '#skF_9') | ~m2_yellow_6(C_183, '#skF_9', '#skF_10') | ~v1_compts_1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_297])).
% 8.31/2.69  tff(c_2580, plain, (![C_183]: (~v3_yellow_6(C_183, '#skF_9') | ~m2_yellow_6(C_183, '#skF_9', '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_2542, c_86])).
% 8.31/2.69  tff(c_2723, plain, (![C_736]: (~v3_yellow_6('#skF_6'('#skF_9', '#skF_10', C_736), '#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', C_736) | ~m1_subset_1(C_736, u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_2707, c_2580])).
% 8.31/2.69  tff(c_2730, plain, (![C_736]: (~v3_yellow_6('#skF_6'('#skF_9', '#skF_10', C_736), '#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', C_736) | ~m1_subset_1(C_736, u1_struct_0('#skF_9')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2546, c_2552, c_2554, c_2723])).
% 8.31/2.69  tff(c_2732, plain, (![C_737]: (~v3_yellow_6('#skF_6'('#skF_9', '#skF_10', C_737), '#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', C_737) | ~m1_subset_1(C_737, u1_struct_0('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_84, c_2541, c_2730])).
% 8.31/2.69  tff(c_2735, plain, (![C_737]: (~r3_waybel_9('#skF_9', '#skF_10', C_737) | ~m1_subset_1(C_737, u1_struct_0('#skF_9')) | k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', C_737))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_9', '#skF_10', C_737), '#skF_9') | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', C_737)) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', C_737)) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', C_737)) | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_50, c_2732])).
% 8.31/2.69  tff(c_2738, plain, (![C_737]: (~r3_waybel_9('#skF_9', '#skF_10', C_737) | ~m1_subset_1(C_737, u1_struct_0('#skF_9')) | k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', C_737))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_9', '#skF_10', C_737), '#skF_9') | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', C_737)) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', C_737)) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', C_737)) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2735])).
% 8.31/2.69  tff(c_2799, plain, (![C_763]: (~r3_waybel_9('#skF_9', '#skF_10', C_763) | ~m1_subset_1(C_763, u1_struct_0('#skF_9')) | k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', C_763))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_9', '#skF_10', C_763), '#skF_9') | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', C_763)) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', C_763)) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', C_763)))), inference(negUnitSimplification, [status(thm)], [c_84, c_2738])).
% 8.31/2.69  tff(c_2811, plain, (![B_172]: (~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)), '#skF_9') | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_2799])).
% 8.31/2.69  tff(c_2822, plain, (![B_172]: (~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)), '#skF_9') | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2542, c_2811])).
% 8.31/2.69  tff(c_2823, plain, (![B_172]: (~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)))=k1_xboole_0 | ~l1_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)), '#skF_9') | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172))), inference(negUnitSimplification, [status(thm)], [c_84, c_2822])).
% 8.31/2.69  tff(c_2940, plain, (![B_827]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827)))=k1_xboole_0 | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827))) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827))) | ~l1_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827)) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_827, '#skF_9') | ~v7_waybel_0(B_827) | ~v4_orders_2(B_827) | v2_struct_0(B_827) | ~v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_2936, c_2823])).
% 8.31/2.69  tff(c_2943, plain, (![B_827]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827)))=k1_xboole_0 | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827))) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827))) | ~l1_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827)) | v2_struct_0('#skF_10') | ~l1_waybel_0(B_827, '#skF_9') | ~v7_waybel_0(B_827) | ~v4_orders_2(B_827) | v2_struct_0(B_827) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2542, c_2546, c_2552, c_2554, c_2940])).
% 8.31/2.69  tff(c_2944, plain, (![B_827]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827)))=k1_xboole_0 | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827))) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827))) | ~l1_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_827)) | ~l1_waybel_0(B_827, '#skF_9') | ~v7_waybel_0(B_827) | ~v4_orders_2(B_827) | v2_struct_0(B_827))), inference(negUnitSimplification, [status(thm)], [c_84, c_2541, c_2943])).
% 8.31/2.69  tff(c_2972, plain, (~l1_struct_0('#skF_9')), inference(splitLeft, [status(thm)], [c_2944])).
% 8.31/2.69  tff(c_2975, plain, (~l1_pre_topc('#skF_9')), inference(resolution, [status(thm)], [c_16, c_2972])).
% 8.31/2.69  tff(c_2979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_2975])).
% 8.31/2.69  tff(c_2981, plain, (l1_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_2944])).
% 8.31/2.69  tff(c_44, plain, (![C_103, A_100, B_101]: (v4_orders_2(C_103) | ~m2_yellow_6(C_103, A_100, B_101) | ~l1_waybel_0(B_101, A_100) | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.31/2.69  tff(c_2750, plain, (![A_742, B_743, C_744]: (v4_orders_2('#skF_6'(A_742, B_743, C_744)) | ~l1_struct_0(A_742) | ~r3_waybel_9(A_742, B_743, C_744) | ~m1_subset_1(C_744, u1_struct_0(A_742)) | ~l1_waybel_0(B_743, A_742) | ~v7_waybel_0(B_743) | ~v4_orders_2(B_743) | v2_struct_0(B_743) | ~l1_pre_topc(A_742) | ~v2_pre_topc(A_742) | v2_struct_0(A_742))), inference(resolution, [status(thm)], [c_2707, c_44])).
% 8.31/2.69  tff(c_2756, plain, (![A_165, B_743, B_172]: (v4_orders_2('#skF_6'(A_165, B_743, '#skF_7'(A_165, B_172))) | ~l1_struct_0(A_165) | ~r3_waybel_9(A_165, B_743, '#skF_7'(A_165, B_172)) | ~l1_waybel_0(B_743, A_165) | ~v7_waybel_0(B_743) | ~v4_orders_2(B_743) | v2_struct_0(B_743) | ~l1_waybel_0(B_172, A_165) | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~v1_compts_1(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_78, c_2750])).
% 8.31/2.69  tff(c_42, plain, (![C_103, A_100, B_101]: (v7_waybel_0(C_103) | ~m2_yellow_6(C_103, A_100, B_101) | ~l1_waybel_0(B_101, A_100) | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.31/2.69  tff(c_2758, plain, (![A_748, B_749, C_750]: (v7_waybel_0('#skF_6'(A_748, B_749, C_750)) | ~l1_struct_0(A_748) | ~r3_waybel_9(A_748, B_749, C_750) | ~m1_subset_1(C_750, u1_struct_0(A_748)) | ~l1_waybel_0(B_749, A_748) | ~v7_waybel_0(B_749) | ~v4_orders_2(B_749) | v2_struct_0(B_749) | ~l1_pre_topc(A_748) | ~v2_pre_topc(A_748) | v2_struct_0(A_748))), inference(resolution, [status(thm)], [c_2707, c_42])).
% 8.31/2.69  tff(c_2764, plain, (![A_165, B_749, B_172]: (v7_waybel_0('#skF_6'(A_165, B_749, '#skF_7'(A_165, B_172))) | ~l1_struct_0(A_165) | ~r3_waybel_9(A_165, B_749, '#skF_7'(A_165, B_172)) | ~l1_waybel_0(B_749, A_165) | ~v7_waybel_0(B_749) | ~v4_orders_2(B_749) | v2_struct_0(B_749) | ~l1_waybel_0(B_172, A_165) | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~v1_compts_1(A_165) | ~l1_pre_topc(A_165) | ~v2_pre_topc(A_165) | v2_struct_0(A_165))), inference(resolution, [status(thm)], [c_78, c_2758])).
% 8.31/2.69  tff(c_2983, plain, (![B_850]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_850)))=k1_xboole_0 | ~v7_waybel_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_850))) | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_850))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_850))) | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_850)) | ~l1_waybel_0(B_850, '#skF_9') | ~v7_waybel_0(B_850) | ~v4_orders_2(B_850) | v2_struct_0(B_850))), inference(splitRight, [status(thm)], [c_2944])).
% 8.31/2.69  tff(c_2987, plain, (![B_172]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)))=k1_xboole_0 | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~l1_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_2764, c_2983])).
% 8.31/2.69  tff(c_2990, plain, (![B_172]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)))=k1_xboole_0 | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | v2_struct_0('#skF_10') | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2542, c_2546, c_2552, c_2554, c_2981, c_2987])).
% 8.31/2.69  tff(c_2992, plain, (![B_851]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_851)))=k1_xboole_0 | ~v4_orders_2('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_851))) | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_851))) | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_851)) | ~l1_waybel_0(B_851, '#skF_9') | ~v7_waybel_0(B_851) | ~v4_orders_2(B_851) | v2_struct_0(B_851))), inference(negUnitSimplification, [status(thm)], [c_84, c_2541, c_2990])).
% 8.31/2.69  tff(c_2996, plain, (![B_172]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)))=k1_xboole_0 | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~l1_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_2756, c_2992])).
% 8.31/2.69  tff(c_2999, plain, (![B_172]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)))=k1_xboole_0 | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172))) | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | v2_struct_0('#skF_10') | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2542, c_2546, c_2552, c_2554, c_2981, c_2996])).
% 8.31/2.69  tff(c_3001, plain, (![B_852]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_852)))=k1_xboole_0 | v2_struct_0('#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_852))) | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_852)) | ~l1_waybel_0(B_852, '#skF_9') | ~v7_waybel_0(B_852) | ~v4_orders_2(B_852) | v2_struct_0(B_852))), inference(negUnitSimplification, [status(thm)], [c_84, c_2541, c_2999])).
% 8.31/2.69  tff(c_46, plain, (![C_103, A_100, B_101]: (~v2_struct_0(C_103) | ~m2_yellow_6(C_103, A_100, B_101) | ~l1_waybel_0(B_101, A_100) | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101) | ~l1_struct_0(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.31/2.69  tff(c_2725, plain, (![A_734, B_735, C_736]: (~v2_struct_0('#skF_6'(A_734, B_735, C_736)) | ~l1_struct_0(A_734) | ~r3_waybel_9(A_734, B_735, C_736) | ~m1_subset_1(C_736, u1_struct_0(A_734)) | ~l1_waybel_0(B_735, A_734) | ~v7_waybel_0(B_735) | ~v4_orders_2(B_735) | v2_struct_0(B_735) | ~l1_pre_topc(A_734) | ~v2_pre_topc(A_734) | v2_struct_0(A_734))), inference(resolution, [status(thm)], [c_2707, c_46])).
% 8.31/2.69  tff(c_3003, plain, (![B_852]: (~l1_struct_0('#skF_9') | ~m1_subset_1('#skF_7'('#skF_9', B_852), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9') | k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_852)))=k1_xboole_0 | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_852)) | ~l1_waybel_0(B_852, '#skF_9') | ~v7_waybel_0(B_852) | ~v4_orders_2(B_852) | v2_struct_0(B_852))), inference(resolution, [status(thm)], [c_3001, c_2725])).
% 8.31/2.69  tff(c_3006, plain, (![B_852]: (~m1_subset_1('#skF_7'('#skF_9', B_852), u1_struct_0('#skF_9')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9') | k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_852)))=k1_xboole_0 | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_852)) | ~l1_waybel_0(B_852, '#skF_9') | ~v7_waybel_0(B_852) | ~v4_orders_2(B_852) | v2_struct_0(B_852))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2546, c_2552, c_2554, c_2981, c_3003])).
% 8.31/2.69  tff(c_3008, plain, (![B_853]: (~m1_subset_1('#skF_7'('#skF_9', B_853), u1_struct_0('#skF_9')) | k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_853)))=k1_xboole_0 | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_853)) | ~l1_waybel_0(B_853, '#skF_9') | ~v7_waybel_0(B_853) | ~v4_orders_2(B_853) | v2_struct_0(B_853))), inference(negUnitSimplification, [status(thm)], [c_84, c_2541, c_3006])).
% 8.31/2.69  tff(c_3012, plain, (![B_172]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)))=k1_xboole_0 | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_3008])).
% 8.31/2.69  tff(c_3015, plain, (![B_172]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)))=k1_xboole_0 | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2542, c_3012])).
% 8.31/2.69  tff(c_3018, plain, (![B_857]: (k10_yellow_6('#skF_9', '#skF_6'('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_857)))=k1_xboole_0 | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_857)) | ~l1_waybel_0(B_857, '#skF_9') | ~v7_waybel_0(B_857) | ~v4_orders_2(B_857) | v2_struct_0(B_857))), inference(negUnitSimplification, [status(thm)], [c_84, c_3015])).
% 8.31/2.69  tff(c_2765, plain, (![C_751, A_752, B_753]: (r2_hidden(C_751, k10_yellow_6(A_752, '#skF_6'(A_752, B_753, C_751))) | ~r3_waybel_9(A_752, B_753, C_751) | ~m1_subset_1(C_751, u1_struct_0(A_752)) | ~l1_waybel_0(B_753, A_752) | ~v7_waybel_0(B_753) | ~v4_orders_2(B_753) | v2_struct_0(B_753) | ~l1_pre_topc(A_752) | ~v2_pre_topc(A_752) | v2_struct_0(A_752))), inference(cnfTransformation, [status(thm)], [f_248])).
% 8.31/2.69  tff(c_2780, plain, (![A_752, B_753, C_751]: (~r1_tarski(k10_yellow_6(A_752, '#skF_6'(A_752, B_753, C_751)), C_751) | ~r3_waybel_9(A_752, B_753, C_751) | ~m1_subset_1(C_751, u1_struct_0(A_752)) | ~l1_waybel_0(B_753, A_752) | ~v7_waybel_0(B_753) | ~v4_orders_2(B_753) | v2_struct_0(B_753) | ~l1_pre_topc(A_752) | ~v2_pre_topc(A_752) | v2_struct_0(A_752))), inference(resolution, [status(thm)], [c_2765, c_14])).
% 8.31/2.69  tff(c_3044, plain, (![B_857]: (~r1_tarski(k1_xboole_0, '#skF_7'('#skF_9', B_857)) | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_857)) | ~m1_subset_1('#skF_7'('#skF_9', B_857), u1_struct_0('#skF_9')) | ~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_857)) | ~l1_waybel_0(B_857, '#skF_9') | ~v7_waybel_0(B_857) | ~v4_orders_2(B_857) | v2_struct_0(B_857))), inference(superposition, [status(thm), theory('equality')], [c_3018, c_2780])).
% 8.31/2.69  tff(c_3085, plain, (![B_857]: (~m1_subset_1('#skF_7'('#skF_9', B_857), u1_struct_0('#skF_9')) | v2_struct_0('#skF_10') | v2_struct_0('#skF_9') | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_857)) | ~l1_waybel_0(B_857, '#skF_9') | ~v7_waybel_0(B_857) | ~v4_orders_2(B_857) | v2_struct_0(B_857))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2546, c_2552, c_2554, c_8, c_3044])).
% 8.31/2.69  tff(c_3106, plain, (![B_858]: (~m1_subset_1('#skF_7'('#skF_9', B_858), u1_struct_0('#skF_9')) | ~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_858)) | ~l1_waybel_0(B_858, '#skF_9') | ~v7_waybel_0(B_858) | ~v4_orders_2(B_858) | v2_struct_0(B_858))), inference(negUnitSimplification, [status(thm)], [c_84, c_2541, c_3085])).
% 8.31/2.69  tff(c_3110, plain, (![B_172]: (~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | ~v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9'))), inference(resolution, [status(thm)], [c_78, c_3106])).
% 8.31/2.69  tff(c_3113, plain, (![B_172]: (~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_172)) | ~l1_waybel_0(B_172, '#skF_9') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172) | v2_struct_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2542, c_3110])).
% 8.31/2.69  tff(c_3115, plain, (![B_859]: (~r3_waybel_9('#skF_9', '#skF_10', '#skF_7'('#skF_9', B_859)) | ~l1_waybel_0(B_859, '#skF_9') | ~v7_waybel_0(B_859) | ~v4_orders_2(B_859) | v2_struct_0(B_859))), inference(negUnitSimplification, [status(thm)], [c_84, c_3113])).
% 8.31/2.69  tff(c_3119, plain, (~l1_waybel_0('#skF_10', '#skF_9') | ~v7_waybel_0('#skF_10') | ~v4_orders_2('#skF_10') | v2_struct_0('#skF_10') | ~v1_compts_1('#skF_9') | ~l1_pre_topc('#skF_9') | ~v2_pre_topc('#skF_9') | v2_struct_0('#skF_9')), inference(resolution, [status(thm)], [c_76, c_3115])).
% 8.31/2.69  tff(c_3122, plain, (v2_struct_0('#skF_10') | v2_struct_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_2542, c_2546, c_2552, c_2554, c_3119])).
% 8.31/2.69  tff(c_3124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_2541, c_3122])).
% 8.31/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.31/2.69  
% 8.31/2.69  Inference rules
% 8.31/2.69  ----------------------
% 8.31/2.69  #Ref     : 0
% 8.31/2.69  #Sup     : 549
% 8.31/2.69  #Fact    : 4
% 8.31/2.69  #Define  : 0
% 8.31/2.69  #Split   : 21
% 8.31/2.69  #Chain   : 0
% 8.31/2.69  #Close   : 0
% 8.31/2.69  
% 8.31/2.69  Ordering : KBO
% 8.31/2.69  
% 8.31/2.69  Simplification rules
% 8.31/2.69  ----------------------
% 8.31/2.69  #Subsume      : 150
% 8.31/2.69  #Demod        : 828
% 8.31/2.69  #Tautology    : 119
% 8.31/2.69  #SimpNegUnit  : 172
% 8.31/2.69  #BackRed      : 6
% 8.31/2.69  
% 8.31/2.69  #Partial instantiations: 0
% 8.31/2.69  #Strategies tried      : 1
% 8.31/2.69  
% 8.31/2.69  Timing (in seconds)
% 8.31/2.69  ----------------------
% 8.31/2.69  Preprocessing        : 0.41
% 8.31/2.69  Parsing              : 0.22
% 8.31/2.69  CNF conversion       : 0.04
% 8.31/2.69  Main loop            : 1.34
% 8.31/2.69  Inferencing          : 0.55
% 8.31/2.69  Reduction            : 0.36
% 8.31/2.69  Demodulation         : 0.25
% 8.31/2.69  BG Simplification    : 0.06
% 8.31/2.69  Subsumption          : 0.30
% 8.31/2.69  Abstraction          : 0.06
% 8.31/2.69  MUC search           : 0.00
% 8.31/2.69  Cooper               : 0.00
% 8.31/2.69  Total                : 1.88
% 8.31/2.69  Index Insertion      : 0.00
% 8.31/2.69  Index Deletion       : 0.00
% 8.31/2.69  Index Matching       : 0.00
% 8.31/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
