%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:39 EST 2020

% Result     : Theorem 5.69s
% Output     : CNFRefutation 6.12s
% Verified   : 
% Statistics : Number of formulae       :  242 (3020 expanded)
%              Number of leaves         :   45 ( 997 expanded)
%              Depth                    :   37
%              Number of atoms          : 1167 (19104 expanded)
%              Number of equality atoms :   36 (  81 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > m2_yellow_6 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k6_yellow_6 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_8 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_compts_1,type,(
    v1_compts_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_278,negated_conjecture,(
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

tff(f_253,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_yellow19)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
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

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_145,axiom,(
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
         => ! [C] :
              ( m2_yellow_6(C,A,B)
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( r3_waybel_9(A,C,D)
                   => r3_waybel_9(A,B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_99,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_121,axiom,(
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

tff(f_225,axiom,(
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

tff(f_201,axiom,(
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

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_78,plain,
    ( ~ v2_struct_0('#skF_7')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_108,plain,(
    ~ v1_compts_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_66,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_64,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_56,plain,(
    ! [A_66] :
      ( v4_orders_2('#skF_5'(A_66))
      | v1_compts_1(A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_104,plain,(
    ! [B_85] :
      ( v1_compts_1('#skF_6')
      | m2_yellow_6('#skF_8'(B_85),'#skF_6',B_85)
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_218,plain,(
    ! [B_85] :
      ( m2_yellow_6('#skF_8'(B_85),'#skF_6',B_85)
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_104])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_293,plain,(
    ! [A_153,B_154] :
      ( m1_subset_1(k10_yellow_6(A_153,B_154),k1_zfmisc_1(u1_struct_0(A_153)))
      | ~ l1_waybel_0(B_154,A_153)
      | ~ v7_waybel_0(B_154)
      | ~ v4_orders_2(B_154)
      | v2_struct_0(B_154)
      | ~ l1_pre_topc(A_153)
      | ~ v2_pre_topc(A_153)
      | v2_struct_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_317,plain,(
    ! [A_163,A_164,B_165] :
      ( m1_subset_1(A_163,u1_struct_0(A_164))
      | ~ r2_hidden(A_163,k10_yellow_6(A_164,B_165))
      | ~ l1_waybel_0(B_165,A_164)
      | ~ v7_waybel_0(B_165)
      | ~ v4_orders_2(B_165)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164) ) ),
    inference(resolution,[status(thm)],[c_293,c_16])).

tff(c_332,plain,(
    ! [A_164,B_165,B_2] :
      ( m1_subset_1('#skF_1'(k10_yellow_6(A_164,B_165),B_2),u1_struct_0(A_164))
      | ~ l1_waybel_0(B_165,A_164)
      | ~ v7_waybel_0(B_165)
      | ~ v4_orders_2(B_165)
      | v2_struct_0(B_165)
      | ~ l1_pre_topc(A_164)
      | ~ v2_pre_topc(A_164)
      | v2_struct_0(A_164)
      | r1_tarski(k10_yellow_6(A_164,B_165),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_317])).

tff(c_361,plain,(
    ! [A_175,B_176,C_177] :
      ( r3_waybel_9(A_175,B_176,C_177)
      | ~ r2_hidden(C_177,k10_yellow_6(A_175,B_176))
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ l1_waybel_0(B_176,A_175)
      | ~ v7_waybel_0(B_176)
      | ~ v4_orders_2(B_176)
      | v2_struct_0(B_176)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_471,plain,(
    ! [A_221,B_222,B_223] :
      ( r3_waybel_9(A_221,B_222,'#skF_1'(k10_yellow_6(A_221,B_222),B_223))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6(A_221,B_222),B_223),u1_struct_0(A_221))
      | ~ l1_waybel_0(B_222,A_221)
      | ~ v7_waybel_0(B_222)
      | ~ v4_orders_2(B_222)
      | v2_struct_0(B_222)
      | ~ l1_pre_topc(A_221)
      | ~ v2_pre_topc(A_221)
      | v2_struct_0(A_221)
      | r1_tarski(k10_yellow_6(A_221,B_222),B_223) ) ),
    inference(resolution,[status(thm)],[c_6,c_361])).

tff(c_475,plain,(
    ! [A_224,B_225,B_226] :
      ( r3_waybel_9(A_224,B_225,'#skF_1'(k10_yellow_6(A_224,B_225),B_226))
      | ~ l1_waybel_0(B_225,A_224)
      | ~ v7_waybel_0(B_225)
      | ~ v4_orders_2(B_225)
      | v2_struct_0(B_225)
      | ~ l1_pre_topc(A_224)
      | ~ v2_pre_topc(A_224)
      | v2_struct_0(A_224)
      | r1_tarski(k10_yellow_6(A_224,B_225),B_226) ) ),
    inference(resolution,[status(thm)],[c_332,c_471])).

tff(c_38,plain,(
    ! [A_31,B_39,D_45,C_43] :
      ( r3_waybel_9(A_31,B_39,D_45)
      | ~ r3_waybel_9(A_31,C_43,D_45)
      | ~ m1_subset_1(D_45,u1_struct_0(A_31))
      | ~ m2_yellow_6(C_43,A_31,B_39)
      | ~ l1_waybel_0(B_39,A_31)
      | ~ v7_waybel_0(B_39)
      | ~ v4_orders_2(B_39)
      | v2_struct_0(B_39)
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_801,plain,(
    ! [A_310,B_311,B_312,B_313] :
      ( r3_waybel_9(A_310,B_311,'#skF_1'(k10_yellow_6(A_310,B_312),B_313))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6(A_310,B_312),B_313),u1_struct_0(A_310))
      | ~ m2_yellow_6(B_312,A_310,B_311)
      | ~ l1_waybel_0(B_311,A_310)
      | ~ v7_waybel_0(B_311)
      | ~ v4_orders_2(B_311)
      | v2_struct_0(B_311)
      | ~ l1_waybel_0(B_312,A_310)
      | ~ v7_waybel_0(B_312)
      | ~ v4_orders_2(B_312)
      | v2_struct_0(B_312)
      | ~ l1_pre_topc(A_310)
      | ~ v2_pre_topc(A_310)
      | v2_struct_0(A_310)
      | r1_tarski(k10_yellow_6(A_310,B_312),B_313) ) ),
    inference(resolution,[status(thm)],[c_475,c_38])).

tff(c_811,plain,(
    ! [A_318,B_319,B_320,B_321] :
      ( r3_waybel_9(A_318,B_319,'#skF_1'(k10_yellow_6(A_318,B_320),B_321))
      | ~ m2_yellow_6(B_320,A_318,B_319)
      | ~ l1_waybel_0(B_319,A_318)
      | ~ v7_waybel_0(B_319)
      | ~ v4_orders_2(B_319)
      | v2_struct_0(B_319)
      | ~ l1_waybel_0(B_320,A_318)
      | ~ v7_waybel_0(B_320)
      | ~ v4_orders_2(B_320)
      | v2_struct_0(B_320)
      | ~ l1_pre_topc(A_318)
      | ~ v2_pre_topc(A_318)
      | v2_struct_0(A_318)
      | r1_tarski(k10_yellow_6(A_318,B_320),B_321) ) ),
    inference(resolution,[status(thm)],[c_332,c_801])).

tff(c_48,plain,(
    ! [A_66,C_76] :
      ( ~ r3_waybel_9(A_66,'#skF_5'(A_66),C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(A_66))
      | v1_compts_1(A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_823,plain,(
    ! [A_322,B_323,B_324] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6(A_322,B_323),B_324),u1_struct_0(A_322))
      | v1_compts_1(A_322)
      | ~ m2_yellow_6(B_323,A_322,'#skF_5'(A_322))
      | ~ l1_waybel_0('#skF_5'(A_322),A_322)
      | ~ v7_waybel_0('#skF_5'(A_322))
      | ~ v4_orders_2('#skF_5'(A_322))
      | v2_struct_0('#skF_5'(A_322))
      | ~ l1_waybel_0(B_323,A_322)
      | ~ v7_waybel_0(B_323)
      | ~ v4_orders_2(B_323)
      | v2_struct_0(B_323)
      | ~ l1_pre_topc(A_322)
      | ~ v2_pre_topc(A_322)
      | v2_struct_0(A_322)
      | r1_tarski(k10_yellow_6(A_322,B_323),B_324) ) ),
    inference(resolution,[status(thm)],[c_811,c_48])).

tff(c_831,plain,(
    ! [A_325,B_326,B_327] :
      ( v1_compts_1(A_325)
      | ~ m2_yellow_6(B_326,A_325,'#skF_5'(A_325))
      | ~ l1_waybel_0('#skF_5'(A_325),A_325)
      | ~ v7_waybel_0('#skF_5'(A_325))
      | ~ v4_orders_2('#skF_5'(A_325))
      | v2_struct_0('#skF_5'(A_325))
      | ~ l1_waybel_0(B_326,A_325)
      | ~ v7_waybel_0(B_326)
      | ~ v4_orders_2(B_326)
      | v2_struct_0(B_326)
      | ~ l1_pre_topc(A_325)
      | ~ v2_pre_topc(A_325)
      | v2_struct_0(A_325)
      | r1_tarski(k10_yellow_6(A_325,B_326),B_327) ) ),
    inference(resolution,[status(thm)],[c_332,c_823])).

tff(c_837,plain,(
    ! [B_327] :
      ( v1_compts_1('#skF_6')
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327)
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_5'('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_218,c_831])).

tff(c_841,plain,(
    ! [B_327] :
      ( v1_compts_1('#skF_6')
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327)
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_5'('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_837])).

tff(c_842,plain,(
    ! [B_327] :
      ( ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327)
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_5'('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_841])).

tff(c_843,plain,(
    ~ v4_orders_2('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_842])).

tff(c_846,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_843])).

tff(c_849,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_846])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_849])).

tff(c_853,plain,(
    v4_orders_2('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_54,plain,(
    ! [A_66] :
      ( v7_waybel_0('#skF_5'(A_66))
      | v1_compts_1(A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_52,plain,(
    ! [A_66] :
      ( l1_waybel_0('#skF_5'(A_66),A_66)
      | v1_compts_1(A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_241,plain,(
    ! [C_134,A_135,B_136] :
      ( v7_waybel_0(C_134)
      | ~ m2_yellow_6(C_134,A_135,B_136)
      | ~ l1_waybel_0(B_136,A_135)
      | ~ v7_waybel_0(B_136)
      | ~ v4_orders_2(B_136)
      | v2_struct_0(B_136)
      | ~ l1_struct_0(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_244,plain,(
    ! [B_85] :
      ( v7_waybel_0('#skF_8'(B_85))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(resolution,[status(thm)],[c_218,c_241])).

tff(c_247,plain,(
    ! [B_85] :
      ( v7_waybel_0('#skF_8'(B_85))
      | ~ l1_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_244])).

tff(c_248,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_247])).

tff(c_251,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_248])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_251])).

tff(c_257,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_284,plain,(
    ! [C_149,A_150,B_151] :
      ( l1_waybel_0(C_149,A_150)
      | ~ m2_yellow_6(C_149,A_150,B_151)
      | ~ l1_waybel_0(B_151,A_150)
      | ~ v7_waybel_0(B_151)
      | ~ v4_orders_2(B_151)
      | v2_struct_0(B_151)
      | ~ l1_struct_0(A_150)
      | v2_struct_0(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_287,plain,(
    ! [B_85] :
      ( l1_waybel_0('#skF_8'(B_85),'#skF_6')
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(resolution,[status(thm)],[c_218,c_284])).

tff(c_290,plain,(
    ! [B_85] :
      ( l1_waybel_0('#skF_8'(B_85),'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_287])).

tff(c_291,plain,(
    ! [B_85] :
      ( l1_waybel_0('#skF_8'(B_85),'#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_290])).

tff(c_852,plain,(
    ! [B_327] :
      ( ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | v2_struct_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327) ) ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_858,plain,(
    ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_852])).

tff(c_861,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_291,c_858])).

tff(c_864,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_861])).

tff(c_865,plain,(
    ~ v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_864])).

tff(c_868,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_865])).

tff(c_871,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_868])).

tff(c_873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_871])).

tff(c_874,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_864])).

tff(c_876,plain,(
    ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_879,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_876])).

tff(c_882,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_879])).

tff(c_884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_882])).

tff(c_885,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_58,plain,(
    ! [A_66] :
      ( ~ v2_struct_0('#skF_5'(A_66))
      | v1_compts_1(A_66)
      | ~ l1_pre_topc(A_66)
      | ~ v2_pre_topc(A_66)
      | v2_struct_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_253])).

tff(c_889,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_885,c_58])).

tff(c_892,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_889])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_892])).

tff(c_895,plain,(
    ! [B_327] :
      ( ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327) ) ),
    inference(splitRight,[status(thm)],[c_852])).

tff(c_907,plain,(
    ~ v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_895])).

tff(c_910,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_907])).

tff(c_913,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_910])).

tff(c_915,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_913])).

tff(c_917,plain,(
    v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_895])).

tff(c_256,plain,(
    ! [B_85] :
      ( v7_waybel_0('#skF_8'(B_85))
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(splitRight,[status(thm)],[c_247])).

tff(c_916,plain,(
    ! [B_327] :
      ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327) ) ),
    inference(splitRight,[status(thm)],[c_895])).

tff(c_918,plain,(
    ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_916])).

tff(c_921,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_256,c_918])).

tff(c_924,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_917,c_921])).

tff(c_925,plain,(
    ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_924])).

tff(c_928,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_925])).

tff(c_931,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_928])).

tff(c_933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_931])).

tff(c_934,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_924])).

tff(c_938,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_934,c_58])).

tff(c_941,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_938])).

tff(c_943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_941])).

tff(c_944,plain,(
    ! [B_327] :
      ( ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327) ) ),
    inference(splitRight,[status(thm)],[c_916])).

tff(c_956,plain,(
    ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_944])).

tff(c_959,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_956])).

tff(c_962,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_959])).

tff(c_964,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_962])).

tff(c_966,plain,(
    l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_944])).

tff(c_259,plain,(
    ! [C_138,A_139,B_140] :
      ( v4_orders_2(C_138)
      | ~ m2_yellow_6(C_138,A_139,B_140)
      | ~ l1_waybel_0(B_140,A_139)
      | ~ v7_waybel_0(B_140)
      | ~ v4_orders_2(B_140)
      | v2_struct_0(B_140)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_262,plain,(
    ! [B_85] :
      ( v4_orders_2('#skF_8'(B_85))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(resolution,[status(thm)],[c_218,c_259])).

tff(c_265,plain,(
    ! [B_85] :
      ( v4_orders_2('#skF_8'(B_85))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_262])).

tff(c_266,plain,(
    ! [B_85] :
      ( v4_orders_2('#skF_8'(B_85))
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_265])).

tff(c_965,plain,(
    ! [B_327] :
      ( ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327) ) ),
    inference(splitRight,[status(thm)],[c_944])).

tff(c_967,plain,(
    ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_965])).

tff(c_970,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_266,c_967])).

tff(c_973,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_917,c_966,c_970])).

tff(c_976,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_973,c_58])).

tff(c_979,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_976])).

tff(c_981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_979])).

tff(c_982,plain,(
    ! [B_327] :
      ( v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327) ) ),
    inference(splitRight,[status(thm)],[c_965])).

tff(c_984,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_982])).

tff(c_993,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_984,c_58])).

tff(c_996,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_993])).

tff(c_998,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_996])).

tff(c_1000,plain,(
    ~ v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_982])).

tff(c_999,plain,(
    ! [B_327] :
      ( v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_327) ) ),
    inference(splitRight,[status(thm)],[c_982])).

tff(c_1001,plain,(
    v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_999])).

tff(c_268,plain,(
    ! [C_142,A_143,B_144] :
      ( ~ v2_struct_0(C_142)
      | ~ m2_yellow_6(C_142,A_143,B_144)
      | ~ l1_waybel_0(B_144,A_143)
      | ~ v7_waybel_0(B_144)
      | ~ v4_orders_2(B_144)
      | v2_struct_0(B_144)
      | ~ l1_struct_0(A_143)
      | v2_struct_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_271,plain,(
    ! [B_85] :
      ( ~ v2_struct_0('#skF_8'(B_85))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(resolution,[status(thm)],[c_218,c_268])).

tff(c_274,plain,(
    ! [B_85] :
      ( ~ v2_struct_0('#skF_8'(B_85))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_271])).

tff(c_275,plain,(
    ! [B_85] :
      ( ~ v2_struct_0('#skF_8'(B_85))
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_274])).

tff(c_1004,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1001,c_275])).

tff(c_1007,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_917,c_966,c_1004])).

tff(c_1009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_1007])).

tff(c_1012,plain,(
    ! [B_345] : r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_345) ),
    inference(splitRight,[status(thm)],[c_999])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [B_92,A_93] :
      ( B_92 = A_93
      | ~ r1_tarski(B_92,A_93)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_120,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_111])).

tff(c_1064,plain,(
    k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1012,c_120])).

tff(c_92,plain,(
    ! [B_85] :
      ( v1_compts_1('#skF_6')
      | v3_yellow_6('#skF_8'(B_85),'#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_216,plain,(
    ! [B_85] :
      ( v3_yellow_6('#skF_8'(B_85),'#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_92])).

tff(c_298,plain,(
    ! [A_157,B_158] :
      ( k10_yellow_6(A_157,B_158) != k1_xboole_0
      | ~ v3_yellow_6(B_158,A_157)
      | ~ l1_waybel_0(B_158,A_157)
      | ~ v7_waybel_0(B_158)
      | ~ v4_orders_2(B_158)
      | v2_struct_0(B_158)
      | ~ l1_pre_topc(A_157)
      | ~ v2_pre_topc(A_157)
      | v2_struct_0(A_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_304,plain,(
    ! [B_85] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_85)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(B_85),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_85))
      | ~ v4_orders_2('#skF_8'(B_85))
      | v2_struct_0('#skF_8'(B_85))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(resolution,[status(thm)],[c_216,c_298])).

tff(c_308,plain,(
    ! [B_85] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_85)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(B_85),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_85))
      | ~ v4_orders_2('#skF_8'(B_85))
      | v2_struct_0('#skF_8'(B_85))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_85,'#skF_6')
      | ~ v7_waybel_0(B_85)
      | ~ v4_orders_2(B_85)
      | v2_struct_0(B_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_304])).

tff(c_339,plain,(
    ! [B_168] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_168)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(B_168),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_168))
      | ~ v4_orders_2('#skF_8'(B_168))
      | v2_struct_0('#skF_8'(B_168))
      | ~ l1_waybel_0(B_168,'#skF_6')
      | ~ v7_waybel_0(B_168)
      | ~ v4_orders_2(B_168)
      | v2_struct_0(B_168) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_308])).

tff(c_344,plain,(
    ! [B_169] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_169)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_8'(B_169))
      | ~ v4_orders_2('#skF_8'(B_169))
      | v2_struct_0('#skF_8'(B_169))
      | ~ l1_waybel_0(B_169,'#skF_6')
      | ~ v7_waybel_0(B_169)
      | ~ v4_orders_2(B_169)
      | v2_struct_0(B_169) ) ),
    inference(resolution,[status(thm)],[c_291,c_339])).

tff(c_349,plain,(
    ! [B_170] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_170)) != k1_xboole_0
      | ~ v4_orders_2('#skF_8'(B_170))
      | v2_struct_0('#skF_8'(B_170))
      | ~ l1_waybel_0(B_170,'#skF_6')
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170) ) ),
    inference(resolution,[status(thm)],[c_256,c_344])).

tff(c_354,plain,(
    ! [B_171] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_171)) != k1_xboole_0
      | v2_struct_0('#skF_8'(B_171))
      | ~ l1_waybel_0(B_171,'#skF_6')
      | ~ v7_waybel_0(B_171)
      | ~ v4_orders_2(B_171)
      | v2_struct_0(B_171) ) ),
    inference(resolution,[status(thm)],[c_266,c_349])).

tff(c_358,plain,(
    ! [B_171] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_171)) != k1_xboole_0
      | ~ l1_waybel_0(B_171,'#skF_6')
      | ~ v7_waybel_0(B_171)
      | ~ v4_orders_2(B_171)
      | v2_struct_0(B_171) ) ),
    inference(resolution,[status(thm)],[c_354,c_275])).

tff(c_1103,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1064,c_358])).

tff(c_1147,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_853,c_917,c_966,c_1103])).

tff(c_1149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1000,c_1147])).

tff(c_1150,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1151,plain,(
    v1_compts_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,
    ( v4_orders_2('#skF_7')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_1156,plain,(
    v4_orders_2('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_76])).

tff(c_74,plain,
    ( v7_waybel_0('#skF_7')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_1153,plain,(
    v7_waybel_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_74])).

tff(c_72,plain,
    ( l1_waybel_0('#skF_7','#skF_6')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_1158,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_72])).

tff(c_44,plain,(
    ! [A_60,B_64] :
      ( r3_waybel_9(A_60,B_64,'#skF_3'(A_60,B_64))
      | ~ l1_waybel_0(B_64,A_60)
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_46,plain,(
    ! [A_60,B_64] :
      ( m1_subset_1('#skF_3'(A_60,B_64),u1_struct_0(A_60))
      | ~ l1_waybel_0(B_64,A_60)
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_1360,plain,(
    ! [A_428,B_429,C_430] :
      ( m2_yellow_6('#skF_2'(A_428,B_429,C_430),A_428,B_429)
      | ~ r3_waybel_9(A_428,B_429,C_430)
      | ~ m1_subset_1(C_430,u1_struct_0(A_428))
      | ~ l1_waybel_0(B_429,A_428)
      | ~ v7_waybel_0(B_429)
      | ~ v4_orders_2(B_429)
      | v2_struct_0(B_429)
      | ~ l1_pre_topc(A_428)
      | ~ v2_pre_topc(A_428)
      | v2_struct_0(A_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_24,plain,(
    ! [C_20,A_17,B_18] :
      ( l1_waybel_0(C_20,A_17)
      | ~ m2_yellow_6(C_20,A_17,B_18)
      | ~ l1_waybel_0(B_18,A_17)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1448,plain,(
    ! [A_455,B_456,C_457] :
      ( l1_waybel_0('#skF_2'(A_455,B_456,C_457),A_455)
      | ~ l1_struct_0(A_455)
      | ~ r3_waybel_9(A_455,B_456,C_457)
      | ~ m1_subset_1(C_457,u1_struct_0(A_455))
      | ~ l1_waybel_0(B_456,A_455)
      | ~ v7_waybel_0(B_456)
      | ~ v4_orders_2(B_456)
      | v2_struct_0(B_456)
      | ~ l1_pre_topc(A_455)
      | ~ v2_pre_topc(A_455)
      | v2_struct_0(A_455) ) ),
    inference(resolution,[status(thm)],[c_1360,c_24])).

tff(c_1805,plain,(
    ! [A_531,B_532,B_533] :
      ( l1_waybel_0('#skF_2'(A_531,B_532,'#skF_3'(A_531,B_533)),A_531)
      | ~ l1_struct_0(A_531)
      | ~ r3_waybel_9(A_531,B_532,'#skF_3'(A_531,B_533))
      | ~ l1_waybel_0(B_532,A_531)
      | ~ v7_waybel_0(B_532)
      | ~ v4_orders_2(B_532)
      | v2_struct_0(B_532)
      | ~ l1_waybel_0(B_533,A_531)
      | ~ v7_waybel_0(B_533)
      | ~ v4_orders_2(B_533)
      | v2_struct_0(B_533)
      | ~ v1_compts_1(A_531)
      | ~ l1_pre_topc(A_531)
      | ~ v2_pre_topc(A_531)
      | v2_struct_0(A_531) ) ),
    inference(resolution,[status(thm)],[c_46,c_1448])).

tff(c_32,plain,(
    ! [B_23,A_21] :
      ( v3_yellow_6(B_23,A_21)
      | k10_yellow_6(A_21,B_23) = k1_xboole_0
      | ~ l1_waybel_0(B_23,A_21)
      | ~ v7_waybel_0(B_23)
      | ~ v4_orders_2(B_23)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_70,plain,(
    ! [C_84] :
      ( ~ v3_yellow_6(C_84,'#skF_6')
      | ~ m2_yellow_6(C_84,'#skF_6','#skF_7')
      | ~ v1_compts_1('#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_1160,plain,(
    ! [C_84] :
      ( ~ v3_yellow_6(C_84,'#skF_6')
      | ~ m2_yellow_6(C_84,'#skF_6','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1151,c_70])).

tff(c_1376,plain,(
    ! [C_430] :
      ( ~ v3_yellow_6('#skF_2'('#skF_6','#skF_7',C_430),'#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7',C_430)
      | ~ m1_subset_1(C_430,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1360,c_1160])).

tff(c_1383,plain,(
    ! [C_430] :
      ( ~ v3_yellow_6('#skF_2'('#skF_6','#skF_7',C_430),'#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7',C_430)
      | ~ m1_subset_1(C_430,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1156,c_1153,c_1158,c_1376])).

tff(c_1385,plain,(
    ! [C_431] :
      ( ~ v3_yellow_6('#skF_2'('#skF_6','#skF_7',C_431),'#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7',C_431)
      | ~ m1_subset_1(C_431,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1150,c_1383])).

tff(c_1388,plain,(
    ! [C_431] :
      ( ~ r3_waybel_9('#skF_6','#skF_7',C_431)
      | ~ m1_subset_1(C_431,u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7',C_431)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7',C_431),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7',C_431))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7',C_431))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7',C_431))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_32,c_1385])).

tff(c_1391,plain,(
    ! [C_431] :
      ( ~ r3_waybel_9('#skF_6','#skF_7',C_431)
      | ~ m1_subset_1(C_431,u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7',C_431)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7',C_431),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7',C_431))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7',C_431))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7',C_431))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1388])).

tff(c_1458,plain,(
    ! [C_458] :
      ( ~ r3_waybel_9('#skF_6','#skF_7',C_458)
      | ~ m1_subset_1(C_458,u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7',C_458)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7',C_458),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7',C_458))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7',C_458))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7',C_458)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1391])).

tff(c_1470,plain,(
    ! [B_64] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_1458])).

tff(c_1481,plain,(
    ! [B_64] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1151,c_1470])).

tff(c_1482,plain,(
    ! [B_64] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)),'#skF_6')
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1481])).

tff(c_1809,plain,(
    ! [B_533] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_533))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_533,'#skF_6')
      | ~ v7_waybel_0(B_533)
      | ~ v4_orders_2(B_533)
      | v2_struct_0(B_533)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1805,c_1482])).

tff(c_1812,plain,(
    ! [B_533] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_533))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_533,'#skF_6')
      | ~ v7_waybel_0(B_533)
      | ~ v4_orders_2(B_533)
      | v2_struct_0(B_533)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1151,c_1156,c_1153,c_1158,c_1809])).

tff(c_1813,plain,(
    ! [B_533] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_533)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_533))
      | ~ l1_waybel_0(B_533,'#skF_6')
      | ~ v7_waybel_0(B_533)
      | ~ v4_orders_2(B_533)
      | v2_struct_0(B_533) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1150,c_1812])).

tff(c_1828,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1813])).

tff(c_1831,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_1828])).

tff(c_1835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1831])).

tff(c_1837,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1813])).

tff(c_28,plain,(
    ! [C_20,A_17,B_18] :
      ( v4_orders_2(C_20)
      | ~ m2_yellow_6(C_20,A_17,B_18)
      | ~ l1_waybel_0(B_18,A_17)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1404,plain,(
    ! [A_439,B_440,C_441] :
      ( v4_orders_2('#skF_2'(A_439,B_440,C_441))
      | ~ l1_struct_0(A_439)
      | ~ r3_waybel_9(A_439,B_440,C_441)
      | ~ m1_subset_1(C_441,u1_struct_0(A_439))
      | ~ l1_waybel_0(B_440,A_439)
      | ~ v7_waybel_0(B_440)
      | ~ v4_orders_2(B_440)
      | v2_struct_0(B_440)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439)
      | v2_struct_0(A_439) ) ),
    inference(resolution,[status(thm)],[c_1360,c_28])).

tff(c_1413,plain,(
    ! [A_60,B_440,B_64] :
      ( v4_orders_2('#skF_2'(A_60,B_440,'#skF_3'(A_60,B_64)))
      | ~ l1_struct_0(A_60)
      | ~ r3_waybel_9(A_60,B_440,'#skF_3'(A_60,B_64))
      | ~ l1_waybel_0(B_440,A_60)
      | ~ v7_waybel_0(B_440)
      | ~ v4_orders_2(B_440)
      | v2_struct_0(B_440)
      | ~ l1_waybel_0(B_64,A_60)
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_46,c_1404])).

tff(c_26,plain,(
    ! [C_20,A_17,B_18] :
      ( v7_waybel_0(C_20)
      | ~ m2_yellow_6(C_20,A_17,B_18)
      | ~ l1_waybel_0(B_18,A_17)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1414,plain,(
    ! [A_442,B_443,C_444] :
      ( v7_waybel_0('#skF_2'(A_442,B_443,C_444))
      | ~ l1_struct_0(A_442)
      | ~ r3_waybel_9(A_442,B_443,C_444)
      | ~ m1_subset_1(C_444,u1_struct_0(A_442))
      | ~ l1_waybel_0(B_443,A_442)
      | ~ v7_waybel_0(B_443)
      | ~ v4_orders_2(B_443)
      | v2_struct_0(B_443)
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(resolution,[status(thm)],[c_1360,c_26])).

tff(c_1423,plain,(
    ! [A_60,B_443,B_64] :
      ( v7_waybel_0('#skF_2'(A_60,B_443,'#skF_3'(A_60,B_64)))
      | ~ l1_struct_0(A_60)
      | ~ r3_waybel_9(A_60,B_443,'#skF_3'(A_60,B_64))
      | ~ l1_waybel_0(B_443,A_60)
      | ~ v7_waybel_0(B_443)
      | ~ v4_orders_2(B_443)
      | v2_struct_0(B_443)
      | ~ l1_waybel_0(B_64,A_60)
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ v1_compts_1(A_60)
      | ~ l1_pre_topc(A_60)
      | ~ v2_pre_topc(A_60)
      | v2_struct_0(A_60) ) ),
    inference(resolution,[status(thm)],[c_46,c_1414])).

tff(c_1838,plain,(
    ! [B_544] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_544))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_544)))
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_544)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_544)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_544))
      | ~ l1_waybel_0(B_544,'#skF_6')
      | ~ v7_waybel_0(B_544)
      | ~ v4_orders_2(B_544)
      | v2_struct_0(B_544) ) ),
    inference(splitRight,[status(thm)],[c_1813])).

tff(c_1842,plain,(
    ! [B_64] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1423,c_1838])).

tff(c_1845,plain,(
    ! [B_64] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1151,c_1156,c_1153,c_1158,c_1837,c_1842])).

tff(c_1847,plain,(
    ! [B_545] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_545))) = k1_xboole_0
      | ~ v4_orders_2('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_545)))
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_545)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_545))
      | ~ l1_waybel_0(B_545,'#skF_6')
      | ~ v7_waybel_0(B_545)
      | ~ v4_orders_2(B_545)
      | v2_struct_0(B_545) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1150,c_1845])).

tff(c_1851,plain,(
    ! [B_64] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1413,c_1847])).

tff(c_1854,plain,(
    ! [B_64] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1151,c_1156,c_1153,c_1158,c_1837,c_1851])).

tff(c_1856,plain,(
    ! [B_546] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_546))) = k1_xboole_0
      | v2_struct_0('#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_546)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_546))
      | ~ l1_waybel_0(B_546,'#skF_6')
      | ~ v7_waybel_0(B_546)
      | ~ v4_orders_2(B_546)
      | v2_struct_0(B_546) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1150,c_1854])).

tff(c_30,plain,(
    ! [C_20,A_17,B_18] :
      ( ~ v2_struct_0(C_20)
      | ~ m2_yellow_6(C_20,A_17,B_18)
      | ~ l1_waybel_0(B_18,A_17)
      | ~ v7_waybel_0(B_18)
      | ~ v4_orders_2(B_18)
      | v2_struct_0(B_18)
      | ~ l1_struct_0(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1378,plain,(
    ! [A_428,B_429,C_430] :
      ( ~ v2_struct_0('#skF_2'(A_428,B_429,C_430))
      | ~ l1_struct_0(A_428)
      | ~ r3_waybel_9(A_428,B_429,C_430)
      | ~ m1_subset_1(C_430,u1_struct_0(A_428))
      | ~ l1_waybel_0(B_429,A_428)
      | ~ v7_waybel_0(B_429)
      | ~ v4_orders_2(B_429)
      | v2_struct_0(B_429)
      | ~ l1_pre_topc(A_428)
      | ~ v2_pre_topc(A_428)
      | v2_struct_0(A_428) ) ),
    inference(resolution,[status(thm)],[c_1360,c_30])).

tff(c_1858,plain,(
    ! [B_546] :
      ( ~ l1_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_3'('#skF_6',B_546),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_546))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_546))
      | ~ l1_waybel_0(B_546,'#skF_6')
      | ~ v7_waybel_0(B_546)
      | ~ v4_orders_2(B_546)
      | v2_struct_0(B_546) ) ),
    inference(resolution,[status(thm)],[c_1856,c_1378])).

tff(c_1861,plain,(
    ! [B_546] :
      ( ~ m1_subset_1('#skF_3'('#skF_6',B_546),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6')
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_546))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_546))
      | ~ l1_waybel_0(B_546,'#skF_6')
      | ~ v7_waybel_0(B_546)
      | ~ v4_orders_2(B_546)
      | v2_struct_0(B_546) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1156,c_1153,c_1158,c_1837,c_1858])).

tff(c_1872,plain,(
    ! [B_550] :
      ( ~ m1_subset_1('#skF_3'('#skF_6',B_550),u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_550))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_550))
      | ~ l1_waybel_0(B_550,'#skF_6')
      | ~ v7_waybel_0(B_550)
      | ~ v4_orders_2(B_550)
      | v2_struct_0(B_550) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1150,c_1861])).

tff(c_1876,plain,(
    ! [B_64] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_1872])).

tff(c_1879,plain,(
    ! [B_64] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1151,c_1876])).

tff(c_1881,plain,(
    ! [B_551] :
      ( k10_yellow_6('#skF_6','#skF_2'('#skF_6','#skF_7','#skF_3'('#skF_6',B_551))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_551))
      | ~ l1_waybel_0(B_551,'#skF_6')
      | ~ v7_waybel_0(B_551)
      | ~ v4_orders_2(B_551)
      | v2_struct_0(B_551) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1879])).

tff(c_1424,plain,(
    ! [C_445,A_446,B_447] :
      ( r2_hidden(C_445,k10_yellow_6(A_446,'#skF_2'(A_446,B_447,C_445)))
      | ~ r3_waybel_9(A_446,B_447,C_445)
      | ~ m1_subset_1(C_445,u1_struct_0(A_446))
      | ~ l1_waybel_0(B_447,A_446)
      | ~ v7_waybel_0(B_447)
      | ~ v4_orders_2(B_447)
      | v2_struct_0(B_447)
      | ~ l1_pre_topc(A_446)
      | ~ v2_pre_topc(A_446)
      | v2_struct_0(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1439,plain,(
    ! [A_446,B_447,C_445] :
      ( ~ r1_tarski(k10_yellow_6(A_446,'#skF_2'(A_446,B_447,C_445)),C_445)
      | ~ r3_waybel_9(A_446,B_447,C_445)
      | ~ m1_subset_1(C_445,u1_struct_0(A_446))
      | ~ l1_waybel_0(B_447,A_446)
      | ~ v7_waybel_0(B_447)
      | ~ v4_orders_2(B_447)
      | v2_struct_0(B_447)
      | ~ l1_pre_topc(A_446)
      | ~ v2_pre_topc(A_446)
      | v2_struct_0(A_446) ) ),
    inference(resolution,[status(thm)],[c_1424,c_18])).

tff(c_1905,plain,(
    ! [B_551] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_3'('#skF_6',B_551))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_551))
      | ~ m1_subset_1('#skF_3'('#skF_6',B_551),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_551))
      | ~ l1_waybel_0(B_551,'#skF_6')
      | ~ v7_waybel_0(B_551)
      | ~ v4_orders_2(B_551)
      | v2_struct_0(B_551) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1881,c_1439])).

tff(c_1943,plain,(
    ! [B_551] :
      ( ~ m1_subset_1('#skF_3'('#skF_6',B_551),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_551))
      | ~ l1_waybel_0(B_551,'#skF_6')
      | ~ v7_waybel_0(B_551)
      | ~ v4_orders_2(B_551)
      | v2_struct_0(B_551) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1156,c_1153,c_1158,c_14,c_1905])).

tff(c_1964,plain,(
    ! [B_552] :
      ( ~ m1_subset_1('#skF_3'('#skF_6',B_552),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_552))
      | ~ l1_waybel_0(B_552,'#skF_6')
      | ~ v7_waybel_0(B_552)
      | ~ v4_orders_2(B_552)
      | v2_struct_0(B_552) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1150,c_1943])).

tff(c_1968,plain,(
    ! [B_64] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_1964])).

tff(c_1971,plain,(
    ! [B_64] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_64))
      | ~ l1_waybel_0(B_64,'#skF_6')
      | ~ v7_waybel_0(B_64)
      | ~ v4_orders_2(B_64)
      | v2_struct_0(B_64)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1151,c_1968])).

tff(c_1973,plain,(
    ! [B_553] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_3'('#skF_6',B_553))
      | ~ l1_waybel_0(B_553,'#skF_6')
      | ~ v7_waybel_0(B_553)
      | ~ v4_orders_2(B_553)
      | v2_struct_0(B_553) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1971])).

tff(c_1981,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ v7_waybel_0('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_44,c_1973])).

tff(c_1988,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1151,c_1156,c_1153,c_1158,c_1981])).

tff(c_1990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1150,c_1988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:58:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.69/2.03  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.69/2.05  
% 5.69/2.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.69/2.06  %$ r3_waybel_9 > m2_yellow_6 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k6_yellow_6 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_8 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 5.69/2.06  
% 5.69/2.06  %Foreground sorts:
% 5.69/2.06  
% 5.69/2.06  
% 5.69/2.06  %Background operators:
% 5.69/2.06  
% 5.69/2.06  
% 5.69/2.06  %Foreground operators:
% 5.69/2.06  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.69/2.06  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.69/2.06  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 5.69/2.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.69/2.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.69/2.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.69/2.06  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 5.69/2.06  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 5.69/2.06  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.69/2.06  tff('#skF_8', type, '#skF_8': $i > $i).
% 5.69/2.06  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.69/2.06  tff('#skF_7', type, '#skF_7': $i).
% 5.69/2.06  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.69/2.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.69/2.06  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 5.69/2.06  tff('#skF_6', type, '#skF_6': $i).
% 5.69/2.06  tff(k6_yellow_6, type, k6_yellow_6: $i > $i).
% 5.69/2.06  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.69/2.06  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.69/2.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.69/2.06  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.69/2.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.69/2.06  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.69/2.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.69/2.06  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.69/2.06  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.69/2.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.69/2.06  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 5.69/2.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.69/2.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.69/2.06  
% 6.12/2.10  tff(f_278, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow19)).
% 6.12/2.10  tff(f_253, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ~(r2_hidden(B, k6_yellow_6(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~r3_waybel_9(A, B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_yellow19)).
% 6.12/2.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.12/2.10  tff(f_73, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 6.12/2.10  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 6.12/2.10  tff(f_145, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_waybel_9)).
% 6.12/2.10  tff(f_172, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_waybel_9)).
% 6.12/2.10  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.12/2.10  tff(f_99, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 6.12/2.10  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.12/2.10  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.12/2.10  tff(f_121, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_yellow_6)).
% 6.12/2.10  tff(f_225, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l37_yellow19)).
% 6.12/2.10  tff(f_201, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 6.12/2.10  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.12/2.10  tff(c_68, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_78, plain, (~v2_struct_0('#skF_7') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_108, plain, (~v1_compts_1('#skF_6')), inference(splitLeft, [status(thm)], [c_78])).
% 6.12/2.10  tff(c_66, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_64, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_56, plain, (![A_66]: (v4_orders_2('#skF_5'(A_66)) | v1_compts_1(A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_253])).
% 6.12/2.10  tff(c_104, plain, (![B_85]: (v1_compts_1('#skF_6') | m2_yellow_6('#skF_8'(B_85), '#skF_6', B_85) | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_218, plain, (![B_85]: (m2_yellow_6('#skF_8'(B_85), '#skF_6', B_85) | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(negUnitSimplification, [status(thm)], [c_108, c_104])).
% 6.12/2.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.12/2.10  tff(c_293, plain, (![A_153, B_154]: (m1_subset_1(k10_yellow_6(A_153, B_154), k1_zfmisc_1(u1_struct_0(A_153))) | ~l1_waybel_0(B_154, A_153) | ~v7_waybel_0(B_154) | ~v4_orders_2(B_154) | v2_struct_0(B_154) | ~l1_pre_topc(A_153) | ~v2_pre_topc(A_153) | v2_struct_0(A_153))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.12/2.10  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.12/2.10  tff(c_317, plain, (![A_163, A_164, B_165]: (m1_subset_1(A_163, u1_struct_0(A_164)) | ~r2_hidden(A_163, k10_yellow_6(A_164, B_165)) | ~l1_waybel_0(B_165, A_164) | ~v7_waybel_0(B_165) | ~v4_orders_2(B_165) | v2_struct_0(B_165) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164))), inference(resolution, [status(thm)], [c_293, c_16])).
% 6.12/2.10  tff(c_332, plain, (![A_164, B_165, B_2]: (m1_subset_1('#skF_1'(k10_yellow_6(A_164, B_165), B_2), u1_struct_0(A_164)) | ~l1_waybel_0(B_165, A_164) | ~v7_waybel_0(B_165) | ~v4_orders_2(B_165) | v2_struct_0(B_165) | ~l1_pre_topc(A_164) | ~v2_pre_topc(A_164) | v2_struct_0(A_164) | r1_tarski(k10_yellow_6(A_164, B_165), B_2))), inference(resolution, [status(thm)], [c_6, c_317])).
% 6.12/2.10  tff(c_361, plain, (![A_175, B_176, C_177]: (r3_waybel_9(A_175, B_176, C_177) | ~r2_hidden(C_177, k10_yellow_6(A_175, B_176)) | ~m1_subset_1(C_177, u1_struct_0(A_175)) | ~l1_waybel_0(B_176, A_175) | ~v7_waybel_0(B_176) | ~v4_orders_2(B_176) | v2_struct_0(B_176) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_145])).
% 6.12/2.10  tff(c_471, plain, (![A_221, B_222, B_223]: (r3_waybel_9(A_221, B_222, '#skF_1'(k10_yellow_6(A_221, B_222), B_223)) | ~m1_subset_1('#skF_1'(k10_yellow_6(A_221, B_222), B_223), u1_struct_0(A_221)) | ~l1_waybel_0(B_222, A_221) | ~v7_waybel_0(B_222) | ~v4_orders_2(B_222) | v2_struct_0(B_222) | ~l1_pre_topc(A_221) | ~v2_pre_topc(A_221) | v2_struct_0(A_221) | r1_tarski(k10_yellow_6(A_221, B_222), B_223))), inference(resolution, [status(thm)], [c_6, c_361])).
% 6.12/2.10  tff(c_475, plain, (![A_224, B_225, B_226]: (r3_waybel_9(A_224, B_225, '#skF_1'(k10_yellow_6(A_224, B_225), B_226)) | ~l1_waybel_0(B_225, A_224) | ~v7_waybel_0(B_225) | ~v4_orders_2(B_225) | v2_struct_0(B_225) | ~l1_pre_topc(A_224) | ~v2_pre_topc(A_224) | v2_struct_0(A_224) | r1_tarski(k10_yellow_6(A_224, B_225), B_226))), inference(resolution, [status(thm)], [c_332, c_471])).
% 6.12/2.10  tff(c_38, plain, (![A_31, B_39, D_45, C_43]: (r3_waybel_9(A_31, B_39, D_45) | ~r3_waybel_9(A_31, C_43, D_45) | ~m1_subset_1(D_45, u1_struct_0(A_31)) | ~m2_yellow_6(C_43, A_31, B_39) | ~l1_waybel_0(B_39, A_31) | ~v7_waybel_0(B_39) | ~v4_orders_2(B_39) | v2_struct_0(B_39) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_172])).
% 6.12/2.10  tff(c_801, plain, (![A_310, B_311, B_312, B_313]: (r3_waybel_9(A_310, B_311, '#skF_1'(k10_yellow_6(A_310, B_312), B_313)) | ~m1_subset_1('#skF_1'(k10_yellow_6(A_310, B_312), B_313), u1_struct_0(A_310)) | ~m2_yellow_6(B_312, A_310, B_311) | ~l1_waybel_0(B_311, A_310) | ~v7_waybel_0(B_311) | ~v4_orders_2(B_311) | v2_struct_0(B_311) | ~l1_waybel_0(B_312, A_310) | ~v7_waybel_0(B_312) | ~v4_orders_2(B_312) | v2_struct_0(B_312) | ~l1_pre_topc(A_310) | ~v2_pre_topc(A_310) | v2_struct_0(A_310) | r1_tarski(k10_yellow_6(A_310, B_312), B_313))), inference(resolution, [status(thm)], [c_475, c_38])).
% 6.12/2.10  tff(c_811, plain, (![A_318, B_319, B_320, B_321]: (r3_waybel_9(A_318, B_319, '#skF_1'(k10_yellow_6(A_318, B_320), B_321)) | ~m2_yellow_6(B_320, A_318, B_319) | ~l1_waybel_0(B_319, A_318) | ~v7_waybel_0(B_319) | ~v4_orders_2(B_319) | v2_struct_0(B_319) | ~l1_waybel_0(B_320, A_318) | ~v7_waybel_0(B_320) | ~v4_orders_2(B_320) | v2_struct_0(B_320) | ~l1_pre_topc(A_318) | ~v2_pre_topc(A_318) | v2_struct_0(A_318) | r1_tarski(k10_yellow_6(A_318, B_320), B_321))), inference(resolution, [status(thm)], [c_332, c_801])).
% 6.12/2.10  tff(c_48, plain, (![A_66, C_76]: (~r3_waybel_9(A_66, '#skF_5'(A_66), C_76) | ~m1_subset_1(C_76, u1_struct_0(A_66)) | v1_compts_1(A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_253])).
% 6.12/2.10  tff(c_823, plain, (![A_322, B_323, B_324]: (~m1_subset_1('#skF_1'(k10_yellow_6(A_322, B_323), B_324), u1_struct_0(A_322)) | v1_compts_1(A_322) | ~m2_yellow_6(B_323, A_322, '#skF_5'(A_322)) | ~l1_waybel_0('#skF_5'(A_322), A_322) | ~v7_waybel_0('#skF_5'(A_322)) | ~v4_orders_2('#skF_5'(A_322)) | v2_struct_0('#skF_5'(A_322)) | ~l1_waybel_0(B_323, A_322) | ~v7_waybel_0(B_323) | ~v4_orders_2(B_323) | v2_struct_0(B_323) | ~l1_pre_topc(A_322) | ~v2_pre_topc(A_322) | v2_struct_0(A_322) | r1_tarski(k10_yellow_6(A_322, B_323), B_324))), inference(resolution, [status(thm)], [c_811, c_48])).
% 6.12/2.10  tff(c_831, plain, (![A_325, B_326, B_327]: (v1_compts_1(A_325) | ~m2_yellow_6(B_326, A_325, '#skF_5'(A_325)) | ~l1_waybel_0('#skF_5'(A_325), A_325) | ~v7_waybel_0('#skF_5'(A_325)) | ~v4_orders_2('#skF_5'(A_325)) | v2_struct_0('#skF_5'(A_325)) | ~l1_waybel_0(B_326, A_325) | ~v7_waybel_0(B_326) | ~v4_orders_2(B_326) | v2_struct_0(B_326) | ~l1_pre_topc(A_325) | ~v2_pre_topc(A_325) | v2_struct_0(A_325) | r1_tarski(k10_yellow_6(A_325, B_326), B_327))), inference(resolution, [status(thm)], [c_332, c_823])).
% 6.12/2.10  tff(c_837, plain, (![B_327]: (v1_compts_1('#skF_6') | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6')))), inference(resolution, [status(thm)], [c_218, c_831])).
% 6.12/2.10  tff(c_841, plain, (![B_327]: (v1_compts_1('#skF_6') | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_837])).
% 6.12/2.10  tff(c_842, plain, (![B_327]: (~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_841])).
% 6.12/2.10  tff(c_843, plain, (~v4_orders_2('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_842])).
% 6.12/2.10  tff(c_846, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_843])).
% 6.12/2.10  tff(c_849, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_846])).
% 6.12/2.10  tff(c_851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_849])).
% 6.12/2.10  tff(c_853, plain, (v4_orders_2('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_842])).
% 6.12/2.10  tff(c_54, plain, (![A_66]: (v7_waybel_0('#skF_5'(A_66)) | v1_compts_1(A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_253])).
% 6.12/2.10  tff(c_52, plain, (![A_66]: (l1_waybel_0('#skF_5'(A_66), A_66) | v1_compts_1(A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_253])).
% 6.12/2.10  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.12/2.10  tff(c_241, plain, (![C_134, A_135, B_136]: (v7_waybel_0(C_134) | ~m2_yellow_6(C_134, A_135, B_136) | ~l1_waybel_0(B_136, A_135) | ~v7_waybel_0(B_136) | ~v4_orders_2(B_136) | v2_struct_0(B_136) | ~l1_struct_0(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.12/2.10  tff(c_244, plain, (![B_85]: (v7_waybel_0('#skF_8'(B_85)) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(resolution, [status(thm)], [c_218, c_241])).
% 6.12/2.10  tff(c_247, plain, (![B_85]: (v7_waybel_0('#skF_8'(B_85)) | ~l1_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(negUnitSimplification, [status(thm)], [c_68, c_244])).
% 6.12/2.10  tff(c_248, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_247])).
% 6.12/2.10  tff(c_251, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_248])).
% 6.12/2.10  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_251])).
% 6.12/2.10  tff(c_257, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_247])).
% 6.12/2.10  tff(c_284, plain, (![C_149, A_150, B_151]: (l1_waybel_0(C_149, A_150) | ~m2_yellow_6(C_149, A_150, B_151) | ~l1_waybel_0(B_151, A_150) | ~v7_waybel_0(B_151) | ~v4_orders_2(B_151) | v2_struct_0(B_151) | ~l1_struct_0(A_150) | v2_struct_0(A_150))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.12/2.10  tff(c_287, plain, (![B_85]: (l1_waybel_0('#skF_8'(B_85), '#skF_6') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(resolution, [status(thm)], [c_218, c_284])).
% 6.12/2.10  tff(c_290, plain, (![B_85]: (l1_waybel_0('#skF_8'(B_85), '#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_287])).
% 6.12/2.10  tff(c_291, plain, (![B_85]: (l1_waybel_0('#skF_8'(B_85), '#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(negUnitSimplification, [status(thm)], [c_68, c_290])).
% 6.12/2.10  tff(c_852, plain, (![B_327]: (~v7_waybel_0('#skF_5'('#skF_6')) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | v2_struct_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327))), inference(splitRight, [status(thm)], [c_842])).
% 6.12/2.10  tff(c_858, plain, (~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6')), inference(splitLeft, [status(thm)], [c_852])).
% 6.12/2.10  tff(c_861, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_291, c_858])).
% 6.12/2.10  tff(c_864, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_853, c_861])).
% 6.12/2.10  tff(c_865, plain, (~v7_waybel_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_864])).
% 6.12/2.10  tff(c_868, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_865])).
% 6.12/2.10  tff(c_871, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_868])).
% 6.12/2.10  tff(c_873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_871])).
% 6.12/2.10  tff(c_874, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_864])).
% 6.12/2.10  tff(c_876, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_874])).
% 6.12/2.10  tff(c_879, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_876])).
% 6.12/2.10  tff(c_882, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_879])).
% 6.12/2.10  tff(c_884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_882])).
% 6.12/2.10  tff(c_885, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_874])).
% 6.12/2.10  tff(c_58, plain, (![A_66]: (~v2_struct_0('#skF_5'(A_66)) | v1_compts_1(A_66) | ~l1_pre_topc(A_66) | ~v2_pre_topc(A_66) | v2_struct_0(A_66))), inference(cnfTransformation, [status(thm)], [f_253])).
% 6.12/2.10  tff(c_889, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_885, c_58])).
% 6.12/2.10  tff(c_892, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_889])).
% 6.12/2.10  tff(c_894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_892])).
% 6.12/2.10  tff(c_895, plain, (![B_327]: (~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327))), inference(splitRight, [status(thm)], [c_852])).
% 6.12/2.10  tff(c_907, plain, (~v7_waybel_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_895])).
% 6.12/2.10  tff(c_910, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_907])).
% 6.12/2.10  tff(c_913, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_910])).
% 6.12/2.10  tff(c_915, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_913])).
% 6.12/2.10  tff(c_917, plain, (v7_waybel_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_895])).
% 6.12/2.10  tff(c_256, plain, (![B_85]: (v7_waybel_0('#skF_8'(B_85)) | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(splitRight, [status(thm)], [c_247])).
% 6.12/2.10  tff(c_916, plain, (![B_327]: (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327))), inference(splitRight, [status(thm)], [c_895])).
% 6.12/2.10  tff(c_918, plain, (~v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitLeft, [status(thm)], [c_916])).
% 6.12/2.10  tff(c_921, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_256, c_918])).
% 6.12/2.10  tff(c_924, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_853, c_917, c_921])).
% 6.12/2.10  tff(c_925, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_924])).
% 6.12/2.10  tff(c_928, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_925])).
% 6.12/2.10  tff(c_931, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_928])).
% 6.12/2.10  tff(c_933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_931])).
% 6.12/2.10  tff(c_934, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_924])).
% 6.12/2.10  tff(c_938, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_934, c_58])).
% 6.12/2.10  tff(c_941, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_938])).
% 6.12/2.10  tff(c_943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_941])).
% 6.12/2.10  tff(c_944, plain, (![B_327]: (~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327))), inference(splitRight, [status(thm)], [c_916])).
% 6.12/2.10  tff(c_956, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_944])).
% 6.12/2.10  tff(c_959, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_956])).
% 6.12/2.10  tff(c_962, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_959])).
% 6.12/2.10  tff(c_964, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_962])).
% 6.12/2.10  tff(c_966, plain, (l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_944])).
% 6.12/2.10  tff(c_259, plain, (![C_138, A_139, B_140]: (v4_orders_2(C_138) | ~m2_yellow_6(C_138, A_139, B_140) | ~l1_waybel_0(B_140, A_139) | ~v7_waybel_0(B_140) | ~v4_orders_2(B_140) | v2_struct_0(B_140) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.12/2.10  tff(c_262, plain, (![B_85]: (v4_orders_2('#skF_8'(B_85)) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(resolution, [status(thm)], [c_218, c_259])).
% 6.12/2.10  tff(c_265, plain, (![B_85]: (v4_orders_2('#skF_8'(B_85)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_262])).
% 6.12/2.10  tff(c_266, plain, (![B_85]: (v4_orders_2('#skF_8'(B_85)) | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(negUnitSimplification, [status(thm)], [c_68, c_265])).
% 6.12/2.10  tff(c_965, plain, (![B_327]: (~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327))), inference(splitRight, [status(thm)], [c_944])).
% 6.12/2.10  tff(c_967, plain, (~v4_orders_2('#skF_8'('#skF_5'('#skF_6')))), inference(splitLeft, [status(thm)], [c_965])).
% 6.12/2.10  tff(c_970, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_266, c_967])).
% 6.12/2.10  tff(c_973, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_853, c_917, c_966, c_970])).
% 6.12/2.10  tff(c_976, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_973, c_58])).
% 6.12/2.10  tff(c_979, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_976])).
% 6.12/2.10  tff(c_981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_979])).
% 6.12/2.10  tff(c_982, plain, (![B_327]: (v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327))), inference(splitRight, [status(thm)], [c_965])).
% 6.12/2.10  tff(c_984, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_982])).
% 6.12/2.10  tff(c_993, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_984, c_58])).
% 6.12/2.10  tff(c_996, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_993])).
% 6.12/2.10  tff(c_998, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_996])).
% 6.12/2.10  tff(c_1000, plain, (~v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_982])).
% 6.12/2.10  tff(c_999, plain, (![B_327]: (v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_327))), inference(splitRight, [status(thm)], [c_982])).
% 6.12/2.10  tff(c_1001, plain, (v2_struct_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitLeft, [status(thm)], [c_999])).
% 6.12/2.10  tff(c_268, plain, (![C_142, A_143, B_144]: (~v2_struct_0(C_142) | ~m2_yellow_6(C_142, A_143, B_144) | ~l1_waybel_0(B_144, A_143) | ~v7_waybel_0(B_144) | ~v4_orders_2(B_144) | v2_struct_0(B_144) | ~l1_struct_0(A_143) | v2_struct_0(A_143))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.12/2.10  tff(c_271, plain, (![B_85]: (~v2_struct_0('#skF_8'(B_85)) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(resolution, [status(thm)], [c_218, c_268])).
% 6.12/2.10  tff(c_274, plain, (![B_85]: (~v2_struct_0('#skF_8'(B_85)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_257, c_271])).
% 6.12/2.10  tff(c_275, plain, (![B_85]: (~v2_struct_0('#skF_8'(B_85)) | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(negUnitSimplification, [status(thm)], [c_68, c_274])).
% 6.12/2.10  tff(c_1004, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_1001, c_275])).
% 6.12/2.10  tff(c_1007, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_853, c_917, c_966, c_1004])).
% 6.12/2.10  tff(c_1009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1000, c_1007])).
% 6.12/2.10  tff(c_1012, plain, (![B_345]: (r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_345))), inference(splitRight, [status(thm)], [c_999])).
% 6.12/2.10  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.12/2.10  tff(c_111, plain, (![B_92, A_93]: (B_92=A_93 | ~r1_tarski(B_92, A_93) | ~r1_tarski(A_93, B_92))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.12/2.10  tff(c_120, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_111])).
% 6.12/2.10  tff(c_1064, plain, (k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6')))=k1_xboole_0), inference(resolution, [status(thm)], [c_1012, c_120])).
% 6.12/2.10  tff(c_92, plain, (![B_85]: (v1_compts_1('#skF_6') | v3_yellow_6('#skF_8'(B_85), '#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_216, plain, (![B_85]: (v3_yellow_6('#skF_8'(B_85), '#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(negUnitSimplification, [status(thm)], [c_108, c_92])).
% 6.12/2.10  tff(c_298, plain, (![A_157, B_158]: (k10_yellow_6(A_157, B_158)!=k1_xboole_0 | ~v3_yellow_6(B_158, A_157) | ~l1_waybel_0(B_158, A_157) | ~v7_waybel_0(B_158) | ~v4_orders_2(B_158) | v2_struct_0(B_158) | ~l1_pre_topc(A_157) | ~v2_pre_topc(A_157) | v2_struct_0(A_157))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.12/2.10  tff(c_304, plain, (![B_85]: (k10_yellow_6('#skF_6', '#skF_8'(B_85))!=k1_xboole_0 | ~l1_waybel_0('#skF_8'(B_85), '#skF_6') | ~v7_waybel_0('#skF_8'(B_85)) | ~v4_orders_2('#skF_8'(B_85)) | v2_struct_0('#skF_8'(B_85)) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(resolution, [status(thm)], [c_216, c_298])).
% 6.12/2.10  tff(c_308, plain, (![B_85]: (k10_yellow_6('#skF_6', '#skF_8'(B_85))!=k1_xboole_0 | ~l1_waybel_0('#skF_8'(B_85), '#skF_6') | ~v7_waybel_0('#skF_8'(B_85)) | ~v4_orders_2('#skF_8'(B_85)) | v2_struct_0('#skF_8'(B_85)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_85, '#skF_6') | ~v7_waybel_0(B_85) | ~v4_orders_2(B_85) | v2_struct_0(B_85))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_304])).
% 6.12/2.10  tff(c_339, plain, (![B_168]: (k10_yellow_6('#skF_6', '#skF_8'(B_168))!=k1_xboole_0 | ~l1_waybel_0('#skF_8'(B_168), '#skF_6') | ~v7_waybel_0('#skF_8'(B_168)) | ~v4_orders_2('#skF_8'(B_168)) | v2_struct_0('#skF_8'(B_168)) | ~l1_waybel_0(B_168, '#skF_6') | ~v7_waybel_0(B_168) | ~v4_orders_2(B_168) | v2_struct_0(B_168))), inference(negUnitSimplification, [status(thm)], [c_68, c_308])).
% 6.12/2.10  tff(c_344, plain, (![B_169]: (k10_yellow_6('#skF_6', '#skF_8'(B_169))!=k1_xboole_0 | ~v7_waybel_0('#skF_8'(B_169)) | ~v4_orders_2('#skF_8'(B_169)) | v2_struct_0('#skF_8'(B_169)) | ~l1_waybel_0(B_169, '#skF_6') | ~v7_waybel_0(B_169) | ~v4_orders_2(B_169) | v2_struct_0(B_169))), inference(resolution, [status(thm)], [c_291, c_339])).
% 6.12/2.10  tff(c_349, plain, (![B_170]: (k10_yellow_6('#skF_6', '#skF_8'(B_170))!=k1_xboole_0 | ~v4_orders_2('#skF_8'(B_170)) | v2_struct_0('#skF_8'(B_170)) | ~l1_waybel_0(B_170, '#skF_6') | ~v7_waybel_0(B_170) | ~v4_orders_2(B_170) | v2_struct_0(B_170))), inference(resolution, [status(thm)], [c_256, c_344])).
% 6.12/2.10  tff(c_354, plain, (![B_171]: (k10_yellow_6('#skF_6', '#skF_8'(B_171))!=k1_xboole_0 | v2_struct_0('#skF_8'(B_171)) | ~l1_waybel_0(B_171, '#skF_6') | ~v7_waybel_0(B_171) | ~v4_orders_2(B_171) | v2_struct_0(B_171))), inference(resolution, [status(thm)], [c_266, c_349])).
% 6.12/2.10  tff(c_358, plain, (![B_171]: (k10_yellow_6('#skF_6', '#skF_8'(B_171))!=k1_xboole_0 | ~l1_waybel_0(B_171, '#skF_6') | ~v7_waybel_0(B_171) | ~v4_orders_2(B_171) | v2_struct_0(B_171))), inference(resolution, [status(thm)], [c_354, c_275])).
% 6.12/2.10  tff(c_1103, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1064, c_358])).
% 6.12/2.10  tff(c_1147, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_853, c_917, c_966, c_1103])).
% 6.12/2.10  tff(c_1149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1000, c_1147])).
% 6.12/2.10  tff(c_1150, plain, (~v2_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 6.12/2.10  tff(c_1151, plain, (v1_compts_1('#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 6.12/2.10  tff(c_76, plain, (v4_orders_2('#skF_7') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_1156, plain, (v4_orders_2('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_76])).
% 6.12/2.10  tff(c_74, plain, (v7_waybel_0('#skF_7') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_1153, plain, (v7_waybel_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_74])).
% 6.12/2.10  tff(c_72, plain, (l1_waybel_0('#skF_7', '#skF_6') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_1158, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_72])).
% 6.12/2.10  tff(c_44, plain, (![A_60, B_64]: (r3_waybel_9(A_60, B_64, '#skF_3'(A_60, B_64)) | ~l1_waybel_0(B_64, A_60) | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_225])).
% 6.12/2.10  tff(c_46, plain, (![A_60, B_64]: (m1_subset_1('#skF_3'(A_60, B_64), u1_struct_0(A_60)) | ~l1_waybel_0(B_64, A_60) | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(cnfTransformation, [status(thm)], [f_225])).
% 6.12/2.10  tff(c_1360, plain, (![A_428, B_429, C_430]: (m2_yellow_6('#skF_2'(A_428, B_429, C_430), A_428, B_429) | ~r3_waybel_9(A_428, B_429, C_430) | ~m1_subset_1(C_430, u1_struct_0(A_428)) | ~l1_waybel_0(B_429, A_428) | ~v7_waybel_0(B_429) | ~v4_orders_2(B_429) | v2_struct_0(B_429) | ~l1_pre_topc(A_428) | ~v2_pre_topc(A_428) | v2_struct_0(A_428))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.12/2.10  tff(c_24, plain, (![C_20, A_17, B_18]: (l1_waybel_0(C_20, A_17) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.12/2.10  tff(c_1448, plain, (![A_455, B_456, C_457]: (l1_waybel_0('#skF_2'(A_455, B_456, C_457), A_455) | ~l1_struct_0(A_455) | ~r3_waybel_9(A_455, B_456, C_457) | ~m1_subset_1(C_457, u1_struct_0(A_455)) | ~l1_waybel_0(B_456, A_455) | ~v7_waybel_0(B_456) | ~v4_orders_2(B_456) | v2_struct_0(B_456) | ~l1_pre_topc(A_455) | ~v2_pre_topc(A_455) | v2_struct_0(A_455))), inference(resolution, [status(thm)], [c_1360, c_24])).
% 6.12/2.10  tff(c_1805, plain, (![A_531, B_532, B_533]: (l1_waybel_0('#skF_2'(A_531, B_532, '#skF_3'(A_531, B_533)), A_531) | ~l1_struct_0(A_531) | ~r3_waybel_9(A_531, B_532, '#skF_3'(A_531, B_533)) | ~l1_waybel_0(B_532, A_531) | ~v7_waybel_0(B_532) | ~v4_orders_2(B_532) | v2_struct_0(B_532) | ~l1_waybel_0(B_533, A_531) | ~v7_waybel_0(B_533) | ~v4_orders_2(B_533) | v2_struct_0(B_533) | ~v1_compts_1(A_531) | ~l1_pre_topc(A_531) | ~v2_pre_topc(A_531) | v2_struct_0(A_531))), inference(resolution, [status(thm)], [c_46, c_1448])).
% 6.12/2.10  tff(c_32, plain, (![B_23, A_21]: (v3_yellow_6(B_23, A_21) | k10_yellow_6(A_21, B_23)=k1_xboole_0 | ~l1_waybel_0(B_23, A_21) | ~v7_waybel_0(B_23) | ~v4_orders_2(B_23) | v2_struct_0(B_23) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.12/2.10  tff(c_70, plain, (![C_84]: (~v3_yellow_6(C_84, '#skF_6') | ~m2_yellow_6(C_84, '#skF_6', '#skF_7') | ~v1_compts_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 6.12/2.10  tff(c_1160, plain, (![C_84]: (~v3_yellow_6(C_84, '#skF_6') | ~m2_yellow_6(C_84, '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1151, c_70])).
% 6.12/2.10  tff(c_1376, plain, (![C_430]: (~v3_yellow_6('#skF_2'('#skF_6', '#skF_7', C_430), '#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', C_430) | ~m1_subset_1(C_430, u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1360, c_1160])).
% 6.12/2.10  tff(c_1383, plain, (![C_430]: (~v3_yellow_6('#skF_2'('#skF_6', '#skF_7', C_430), '#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', C_430) | ~m1_subset_1(C_430, u1_struct_0('#skF_6')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1156, c_1153, c_1158, c_1376])).
% 6.12/2.10  tff(c_1385, plain, (![C_431]: (~v3_yellow_6('#skF_2'('#skF_6', '#skF_7', C_431), '#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', C_431) | ~m1_subset_1(C_431, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_1150, c_1383])).
% 6.12/2.10  tff(c_1388, plain, (![C_431]: (~r3_waybel_9('#skF_6', '#skF_7', C_431) | ~m1_subset_1(C_431, u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', C_431))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', C_431), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', C_431)) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', C_431)) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', C_431)) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_1385])).
% 6.12/2.10  tff(c_1391, plain, (![C_431]: (~r3_waybel_9('#skF_6', '#skF_7', C_431) | ~m1_subset_1(C_431, u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', C_431))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', C_431), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', C_431)) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', C_431)) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', C_431)) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1388])).
% 6.12/2.10  tff(c_1458, plain, (![C_458]: (~r3_waybel_9('#skF_6', '#skF_7', C_458) | ~m1_subset_1(C_458, u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', C_458))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', C_458), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', C_458)) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', C_458)) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', C_458)))), inference(negUnitSimplification, [status(thm)], [c_68, c_1391])).
% 6.12/2.10  tff(c_1470, plain, (![B_64]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_1458])).
% 6.12/2.10  tff(c_1481, plain, (![B_64]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1151, c_1470])).
% 6.12/2.10  tff(c_1482, plain, (![B_64]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)))=k1_xboole_0 | ~l1_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)), '#skF_6') | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64))), inference(negUnitSimplification, [status(thm)], [c_68, c_1481])).
% 6.12/2.10  tff(c_1809, plain, (![B_533]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533)) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_533, '#skF_6') | ~v7_waybel_0(B_533) | ~v4_orders_2(B_533) | v2_struct_0(B_533) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1805, c_1482])).
% 6.12/2.10  tff(c_1812, plain, (![B_533]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_533, '#skF_6') | ~v7_waybel_0(B_533) | ~v4_orders_2(B_533) | v2_struct_0(B_533) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1151, c_1156, c_1153, c_1158, c_1809])).
% 6.12/2.10  tff(c_1813, plain, (![B_533]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_533)) | ~l1_waybel_0(B_533, '#skF_6') | ~v7_waybel_0(B_533) | ~v4_orders_2(B_533) | v2_struct_0(B_533))), inference(negUnitSimplification, [status(thm)], [c_68, c_1150, c_1812])).
% 6.12/2.10  tff(c_1828, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1813])).
% 6.12/2.10  tff(c_1831, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_1828])).
% 6.12/2.10  tff(c_1835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_1831])).
% 6.12/2.10  tff(c_1837, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_1813])).
% 6.12/2.10  tff(c_28, plain, (![C_20, A_17, B_18]: (v4_orders_2(C_20) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.12/2.10  tff(c_1404, plain, (![A_439, B_440, C_441]: (v4_orders_2('#skF_2'(A_439, B_440, C_441)) | ~l1_struct_0(A_439) | ~r3_waybel_9(A_439, B_440, C_441) | ~m1_subset_1(C_441, u1_struct_0(A_439)) | ~l1_waybel_0(B_440, A_439) | ~v7_waybel_0(B_440) | ~v4_orders_2(B_440) | v2_struct_0(B_440) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439) | v2_struct_0(A_439))), inference(resolution, [status(thm)], [c_1360, c_28])).
% 6.12/2.10  tff(c_1413, plain, (![A_60, B_440, B_64]: (v4_orders_2('#skF_2'(A_60, B_440, '#skF_3'(A_60, B_64))) | ~l1_struct_0(A_60) | ~r3_waybel_9(A_60, B_440, '#skF_3'(A_60, B_64)) | ~l1_waybel_0(B_440, A_60) | ~v7_waybel_0(B_440) | ~v4_orders_2(B_440) | v2_struct_0(B_440) | ~l1_waybel_0(B_64, A_60) | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_46, c_1404])).
% 6.12/2.10  tff(c_26, plain, (![C_20, A_17, B_18]: (v7_waybel_0(C_20) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.12/2.10  tff(c_1414, plain, (![A_442, B_443, C_444]: (v7_waybel_0('#skF_2'(A_442, B_443, C_444)) | ~l1_struct_0(A_442) | ~r3_waybel_9(A_442, B_443, C_444) | ~m1_subset_1(C_444, u1_struct_0(A_442)) | ~l1_waybel_0(B_443, A_442) | ~v7_waybel_0(B_443) | ~v4_orders_2(B_443) | v2_struct_0(B_443) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(resolution, [status(thm)], [c_1360, c_26])).
% 6.12/2.10  tff(c_1423, plain, (![A_60, B_443, B_64]: (v7_waybel_0('#skF_2'(A_60, B_443, '#skF_3'(A_60, B_64))) | ~l1_struct_0(A_60) | ~r3_waybel_9(A_60, B_443, '#skF_3'(A_60, B_64)) | ~l1_waybel_0(B_443, A_60) | ~v7_waybel_0(B_443) | ~v4_orders_2(B_443) | v2_struct_0(B_443) | ~l1_waybel_0(B_64, A_60) | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~v1_compts_1(A_60) | ~l1_pre_topc(A_60) | ~v2_pre_topc(A_60) | v2_struct_0(A_60))), inference(resolution, [status(thm)], [c_46, c_1414])).
% 6.12/2.10  tff(c_1838, plain, (![B_544]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_544)))=k1_xboole_0 | ~v7_waybel_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_544))) | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_544))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_544))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_544)) | ~l1_waybel_0(B_544, '#skF_6') | ~v7_waybel_0(B_544) | ~v4_orders_2(B_544) | v2_struct_0(B_544))), inference(splitRight, [status(thm)], [c_1813])).
% 6.12/2.10  tff(c_1842, plain, (![B_64]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)))=k1_xboole_0 | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1423, c_1838])).
% 6.12/2.10  tff(c_1845, plain, (![B_64]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)))=k1_xboole_0 | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1151, c_1156, c_1153, c_1158, c_1837, c_1842])).
% 6.12/2.10  tff(c_1847, plain, (![B_545]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_545)))=k1_xboole_0 | ~v4_orders_2('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_545))) | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_545))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_545)) | ~l1_waybel_0(B_545, '#skF_6') | ~v7_waybel_0(B_545) | ~v4_orders_2(B_545) | v2_struct_0(B_545))), inference(negUnitSimplification, [status(thm)], [c_68, c_1150, c_1845])).
% 6.12/2.10  tff(c_1851, plain, (![B_64]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)))=k1_xboole_0 | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1413, c_1847])).
% 6.12/2.10  tff(c_1854, plain, (![B_64]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)))=k1_xboole_0 | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1151, c_1156, c_1153, c_1158, c_1837, c_1851])).
% 6.12/2.10  tff(c_1856, plain, (![B_546]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_546)))=k1_xboole_0 | v2_struct_0('#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_546))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_546)) | ~l1_waybel_0(B_546, '#skF_6') | ~v7_waybel_0(B_546) | ~v4_orders_2(B_546) | v2_struct_0(B_546))), inference(negUnitSimplification, [status(thm)], [c_68, c_1150, c_1854])).
% 6.12/2.10  tff(c_30, plain, (![C_20, A_17, B_18]: (~v2_struct_0(C_20) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.12/2.10  tff(c_1378, plain, (![A_428, B_429, C_430]: (~v2_struct_0('#skF_2'(A_428, B_429, C_430)) | ~l1_struct_0(A_428) | ~r3_waybel_9(A_428, B_429, C_430) | ~m1_subset_1(C_430, u1_struct_0(A_428)) | ~l1_waybel_0(B_429, A_428) | ~v7_waybel_0(B_429) | ~v4_orders_2(B_429) | v2_struct_0(B_429) | ~l1_pre_topc(A_428) | ~v2_pre_topc(A_428) | v2_struct_0(A_428))), inference(resolution, [status(thm)], [c_1360, c_30])).
% 6.12/2.10  tff(c_1858, plain, (![B_546]: (~l1_struct_0('#skF_6') | ~m1_subset_1('#skF_3'('#skF_6', B_546), u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_546)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_546)) | ~l1_waybel_0(B_546, '#skF_6') | ~v7_waybel_0(B_546) | ~v4_orders_2(B_546) | v2_struct_0(B_546))), inference(resolution, [status(thm)], [c_1856, c_1378])).
% 6.12/2.10  tff(c_1861, plain, (![B_546]: (~m1_subset_1('#skF_3'('#skF_6', B_546), u1_struct_0('#skF_6')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_546)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_546)) | ~l1_waybel_0(B_546, '#skF_6') | ~v7_waybel_0(B_546) | ~v4_orders_2(B_546) | v2_struct_0(B_546))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1156, c_1153, c_1158, c_1837, c_1858])).
% 6.12/2.10  tff(c_1872, plain, (![B_550]: (~m1_subset_1('#skF_3'('#skF_6', B_550), u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_550)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_550)) | ~l1_waybel_0(B_550, '#skF_6') | ~v7_waybel_0(B_550) | ~v4_orders_2(B_550) | v2_struct_0(B_550))), inference(negUnitSimplification, [status(thm)], [c_68, c_1150, c_1861])).
% 6.12/2.10  tff(c_1876, plain, (![B_64]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_1872])).
% 6.12/2.10  tff(c_1879, plain, (![B_64]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1151, c_1876])).
% 6.12/2.10  tff(c_1881, plain, (![B_551]: (k10_yellow_6('#skF_6', '#skF_2'('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_551)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_551)) | ~l1_waybel_0(B_551, '#skF_6') | ~v7_waybel_0(B_551) | ~v4_orders_2(B_551) | v2_struct_0(B_551))), inference(negUnitSimplification, [status(thm)], [c_68, c_1879])).
% 6.12/2.10  tff(c_1424, plain, (![C_445, A_446, B_447]: (r2_hidden(C_445, k10_yellow_6(A_446, '#skF_2'(A_446, B_447, C_445))) | ~r3_waybel_9(A_446, B_447, C_445) | ~m1_subset_1(C_445, u1_struct_0(A_446)) | ~l1_waybel_0(B_447, A_446) | ~v7_waybel_0(B_447) | ~v4_orders_2(B_447) | v2_struct_0(B_447) | ~l1_pre_topc(A_446) | ~v2_pre_topc(A_446) | v2_struct_0(A_446))), inference(cnfTransformation, [status(thm)], [f_201])).
% 6.12/2.10  tff(c_18, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.12/2.10  tff(c_1439, plain, (![A_446, B_447, C_445]: (~r1_tarski(k10_yellow_6(A_446, '#skF_2'(A_446, B_447, C_445)), C_445) | ~r3_waybel_9(A_446, B_447, C_445) | ~m1_subset_1(C_445, u1_struct_0(A_446)) | ~l1_waybel_0(B_447, A_446) | ~v7_waybel_0(B_447) | ~v4_orders_2(B_447) | v2_struct_0(B_447) | ~l1_pre_topc(A_446) | ~v2_pre_topc(A_446) | v2_struct_0(A_446))), inference(resolution, [status(thm)], [c_1424, c_18])).
% 6.12/2.10  tff(c_1905, plain, (![B_551]: (~r1_tarski(k1_xboole_0, '#skF_3'('#skF_6', B_551)) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_551)) | ~m1_subset_1('#skF_3'('#skF_6', B_551), u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_551)) | ~l1_waybel_0(B_551, '#skF_6') | ~v7_waybel_0(B_551) | ~v4_orders_2(B_551) | v2_struct_0(B_551))), inference(superposition, [status(thm), theory('equality')], [c_1881, c_1439])).
% 6.12/2.10  tff(c_1943, plain, (![B_551]: (~m1_subset_1('#skF_3'('#skF_6', B_551), u1_struct_0('#skF_6')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_551)) | ~l1_waybel_0(B_551, '#skF_6') | ~v7_waybel_0(B_551) | ~v4_orders_2(B_551) | v2_struct_0(B_551))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1156, c_1153, c_1158, c_14, c_1905])).
% 6.12/2.10  tff(c_1964, plain, (![B_552]: (~m1_subset_1('#skF_3'('#skF_6', B_552), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_552)) | ~l1_waybel_0(B_552, '#skF_6') | ~v7_waybel_0(B_552) | ~v4_orders_2(B_552) | v2_struct_0(B_552))), inference(negUnitSimplification, [status(thm)], [c_68, c_1150, c_1943])).
% 6.12/2.10  tff(c_1968, plain, (![B_64]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_46, c_1964])).
% 6.12/2.10  tff(c_1971, plain, (![B_64]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_64)) | ~l1_waybel_0(B_64, '#skF_6') | ~v7_waybel_0(B_64) | ~v4_orders_2(B_64) | v2_struct_0(B_64) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1151, c_1968])).
% 6.12/2.10  tff(c_1973, plain, (![B_553]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_3'('#skF_6', B_553)) | ~l1_waybel_0(B_553, '#skF_6') | ~v7_waybel_0(B_553) | ~v4_orders_2(B_553) | v2_struct_0(B_553))), inference(negUnitSimplification, [status(thm)], [c_68, c_1971])).
% 6.12/2.10  tff(c_1981, plain, (~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_44, c_1973])).
% 6.12/2.10  tff(c_1988, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1151, c_1156, c_1153, c_1158, c_1981])).
% 6.12/2.10  tff(c_1990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1150, c_1988])).
% 6.12/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.12/2.10  
% 6.12/2.10  Inference rules
% 6.12/2.10  ----------------------
% 6.12/2.10  #Ref     : 0
% 6.12/2.10  #Sup     : 374
% 6.12/2.10  #Fact    : 0
% 6.12/2.10  #Define  : 0
% 6.12/2.10  #Split   : 19
% 6.12/2.10  #Chain   : 0
% 6.12/2.10  #Close   : 0
% 6.12/2.10  
% 6.12/2.10  Ordering : KBO
% 6.12/2.10  
% 6.12/2.10  Simplification rules
% 6.12/2.10  ----------------------
% 6.12/2.10  #Subsume      : 159
% 6.12/2.10  #Demod        : 270
% 6.12/2.10  #Tautology    : 83
% 6.12/2.10  #SimpNegUnit  : 61
% 6.12/2.10  #BackRed      : 1
% 6.12/2.10  
% 6.12/2.10  #Partial instantiations: 0
% 6.12/2.10  #Strategies tried      : 1
% 6.12/2.10  
% 6.12/2.10  Timing (in seconds)
% 6.12/2.10  ----------------------
% 6.12/2.10  Preprocessing        : 0.37
% 6.12/2.10  Parsing              : 0.20
% 6.12/2.10  CNF conversion       : 0.03
% 6.12/2.10  Main loop            : 0.91
% 6.12/2.10  Inferencing          : 0.38
% 6.12/2.10  Reduction            : 0.23
% 6.12/2.10  Demodulation         : 0.15
% 6.12/2.10  BG Simplification    : 0.04
% 6.12/2.10  Subsumption          : 0.21
% 6.12/2.10  Abstraction          : 0.03
% 6.12/2.11  MUC search           : 0.00
% 6.12/2.11  Cooper               : 0.00
% 6.12/2.11  Total                : 1.37
% 6.12/2.11  Index Insertion      : 0.00
% 6.12/2.11  Index Deletion       : 0.00
% 6.12/2.11  Index Matching       : 0.00
% 6.12/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
