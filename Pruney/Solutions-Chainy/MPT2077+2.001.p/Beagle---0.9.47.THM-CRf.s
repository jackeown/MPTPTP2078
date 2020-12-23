%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:39 EST 2020

% Result     : Theorem 5.39s
% Output     : CNFRefutation 5.98s
% Verified   : 
% Statistics : Number of formulae       :  279 (4829 expanded)
%              Number of leaves         :   46 (1625 expanded)
%              Depth                    :   37
%              Number of atoms          : 1376 (32497 expanded)
%              Number of equality atoms :   36 (  81 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r2_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_8 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_269,negated_conjecture,(
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

tff(f_244,axiom,(
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

tff(f_191,axiom,(
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

tff(f_167,axiom,(
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

tff(f_122,axiom,(
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

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_220,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_78,plain,
    ( ~ v2_struct_0('#skF_7')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_108,plain,(
    ~ v1_compts_1('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_66,plain,(
    v2_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_64,plain,(
    l1_pre_topc('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_56,plain,(
    ! [A_82] :
      ( v4_orders_2('#skF_5'(A_82))
      | v1_compts_1(A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_54,plain,(
    ! [A_82] :
      ( v7_waybel_0('#skF_5'(A_82))
      | v1_compts_1(A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_52,plain,(
    ! [A_82] :
      ( l1_waybel_0('#skF_5'(A_82),A_82)
      | v1_compts_1(A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_104,plain,(
    ! [B_101] :
      ( v1_compts_1('#skF_6')
      | m2_yellow_6('#skF_8'(B_101),'#skF_6',B_101)
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_208,plain,(
    ! [B_101] :
      ( m2_yellow_6('#skF_8'(B_101),'#skF_6',B_101)
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_104])).

tff(c_212,plain,(
    ! [C_143,A_144,B_145] :
      ( v4_orders_2(C_143)
      | ~ m2_yellow_6(C_143,A_144,B_145)
      | ~ l1_waybel_0(B_145,A_144)
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ l1_struct_0(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_215,plain,(
    ! [B_101] :
      ( v4_orders_2('#skF_8'(B_101))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_208,c_212])).

tff(c_218,plain,(
    ! [B_101] :
      ( v4_orders_2('#skF_8'(B_101))
      | ~ l1_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_215])).

tff(c_219,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_222,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_222])).

tff(c_227,plain,(
    ! [B_101] :
      ( v4_orders_2('#skF_8'(B_101))
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_258,plain,(
    ! [A_161,B_162] :
      ( m1_subset_1(k10_yellow_6(A_161,B_162),k1_zfmisc_1(u1_struct_0(A_161)))
      | ~ l1_waybel_0(B_162,A_161)
      | ~ v7_waybel_0(B_162)
      | ~ v4_orders_2(B_162)
      | v2_struct_0(B_162)
      | ~ l1_pre_topc(A_161)
      | ~ v2_pre_topc(A_161)
      | v2_struct_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_302,plain,(
    ! [A_174,A_175,B_176] :
      ( m1_subset_1(A_174,u1_struct_0(A_175))
      | ~ r2_hidden(A_174,k10_yellow_6(A_175,B_176))
      | ~ l1_waybel_0(B_176,A_175)
      | ~ v7_waybel_0(B_176)
      | ~ v4_orders_2(B_176)
      | v2_struct_0(B_176)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_258,c_16])).

tff(c_312,plain,(
    ! [A_175,B_176,B_2] :
      ( m1_subset_1('#skF_1'(k10_yellow_6(A_175,B_176),B_2),u1_struct_0(A_175))
      | ~ l1_waybel_0(B_176,A_175)
      | ~ v7_waybel_0(B_176)
      | ~ v4_orders_2(B_176)
      | v2_struct_0(B_176)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175)
      | r1_tarski(k10_yellow_6(A_175,B_176),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_302])).

tff(c_320,plain,(
    ! [A_191,B_192,C_193] :
      ( r3_waybel_9(A_191,B_192,C_193)
      | ~ r2_hidden(C_193,k10_yellow_6(A_191,B_192))
      | ~ m1_subset_1(C_193,u1_struct_0(A_191))
      | ~ l1_waybel_0(B_192,A_191)
      | ~ v7_waybel_0(B_192)
      | ~ v4_orders_2(B_192)
      | v2_struct_0(B_192)
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_417,plain,(
    ! [A_234,B_235,B_236] :
      ( r3_waybel_9(A_234,B_235,'#skF_1'(k10_yellow_6(A_234,B_235),B_236))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6(A_234,B_235),B_236),u1_struct_0(A_234))
      | ~ l1_waybel_0(B_235,A_234)
      | ~ v7_waybel_0(B_235)
      | ~ v4_orders_2(B_235)
      | v2_struct_0(B_235)
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234)
      | r1_tarski(k10_yellow_6(A_234,B_235),B_236) ) ),
    inference(resolution,[status(thm)],[c_6,c_320])).

tff(c_420,plain,(
    ! [A_175,B_176,B_2] :
      ( r3_waybel_9(A_175,B_176,'#skF_1'(k10_yellow_6(A_175,B_176),B_2))
      | ~ l1_waybel_0(B_176,A_175)
      | ~ v7_waybel_0(B_176)
      | ~ v4_orders_2(B_176)
      | v2_struct_0(B_176)
      | ~ l1_pre_topc(A_175)
      | ~ v2_pre_topc(A_175)
      | v2_struct_0(A_175)
      | r1_tarski(k10_yellow_6(A_175,B_176),B_2) ) ),
    inference(resolution,[status(thm)],[c_312,c_417])).

tff(c_228,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_42,plain,(
    ! [A_39,B_51,C_57] :
      ( m1_connsp_2('#skF_2'(A_39,B_51,C_57),A_39,C_57)
      | r3_waybel_9(A_39,B_51,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0(A_39))
      | ~ l1_waybel_0(B_51,A_39)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_316,plain,(
    ! [A_187,B_188,D_189,C_190] :
      ( r2_waybel_0(A_187,B_188,D_189)
      | ~ m1_connsp_2(D_189,A_187,C_190)
      | ~ r3_waybel_9(A_187,B_188,C_190)
      | ~ m1_subset_1(C_190,u1_struct_0(A_187))
      | ~ l1_waybel_0(B_188,A_187)
      | v2_struct_0(B_188)
      | ~ l1_pre_topc(A_187)
      | ~ v2_pre_topc(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_404,plain,(
    ! [A_226,B_227,B_228,C_229] :
      ( r2_waybel_0(A_226,B_227,'#skF_2'(A_226,B_228,C_229))
      | ~ r3_waybel_9(A_226,B_227,C_229)
      | ~ l1_waybel_0(B_227,A_226)
      | v2_struct_0(B_227)
      | r3_waybel_9(A_226,B_228,C_229)
      | ~ m1_subset_1(C_229,u1_struct_0(A_226))
      | ~ l1_waybel_0(B_228,A_226)
      | v2_struct_0(B_228)
      | ~ l1_pre_topc(A_226)
      | ~ v2_pre_topc(A_226)
      | v2_struct_0(A_226) ) ),
    inference(resolution,[status(thm)],[c_42,c_316])).

tff(c_32,plain,(
    ! [A_21,B_29,D_35,C_33] :
      ( r2_waybel_0(A_21,B_29,D_35)
      | ~ r2_waybel_0(A_21,C_33,D_35)
      | ~ m2_yellow_6(C_33,A_21,B_29)
      | ~ l1_waybel_0(B_29,A_21)
      | ~ v7_waybel_0(B_29)
      | ~ v4_orders_2(B_29)
      | v2_struct_0(B_29)
      | ~ l1_struct_0(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_652,plain,(
    ! [A_285,B_281,C_283,B_284,B_282] :
      ( r2_waybel_0(A_285,B_284,'#skF_2'(A_285,B_282,C_283))
      | ~ m2_yellow_6(B_281,A_285,B_284)
      | ~ l1_waybel_0(B_284,A_285)
      | ~ v7_waybel_0(B_284)
      | ~ v4_orders_2(B_284)
      | v2_struct_0(B_284)
      | ~ l1_struct_0(A_285)
      | ~ r3_waybel_9(A_285,B_281,C_283)
      | ~ l1_waybel_0(B_281,A_285)
      | v2_struct_0(B_281)
      | r3_waybel_9(A_285,B_282,C_283)
      | ~ m1_subset_1(C_283,u1_struct_0(A_285))
      | ~ l1_waybel_0(B_282,A_285)
      | v2_struct_0(B_282)
      | ~ l1_pre_topc(A_285)
      | ~ v2_pre_topc(A_285)
      | v2_struct_0(A_285) ) ),
    inference(resolution,[status(thm)],[c_404,c_32])).

tff(c_656,plain,(
    ! [B_101,B_282,C_283] :
      ( r2_waybel_0('#skF_6',B_101,'#skF_2'('#skF_6',B_282,C_283))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_8'(B_101),C_283)
      | ~ l1_waybel_0('#skF_8'(B_101),'#skF_6')
      | v2_struct_0('#skF_8'(B_101))
      | r3_waybel_9('#skF_6',B_282,C_283)
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_282,'#skF_6')
      | v2_struct_0(B_282)
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_208,c_652])).

tff(c_660,plain,(
    ! [B_101,B_282,C_283] :
      ( r2_waybel_0('#skF_6',B_101,'#skF_2'('#skF_6',B_282,C_283))
      | ~ r3_waybel_9('#skF_6','#skF_8'(B_101),C_283)
      | ~ l1_waybel_0('#skF_8'(B_101),'#skF_6')
      | v2_struct_0('#skF_8'(B_101))
      | r3_waybel_9('#skF_6',B_282,C_283)
      | ~ m1_subset_1(C_283,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_282,'#skF_6')
      | v2_struct_0(B_282)
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_228,c_656])).

tff(c_662,plain,(
    ! [B_286,B_287,C_288] :
      ( r2_waybel_0('#skF_6',B_286,'#skF_2'('#skF_6',B_287,C_288))
      | ~ r3_waybel_9('#skF_6','#skF_8'(B_286),C_288)
      | ~ l1_waybel_0('#skF_8'(B_286),'#skF_6')
      | v2_struct_0('#skF_8'(B_286))
      | r3_waybel_9('#skF_6',B_287,C_288)
      | ~ m1_subset_1(C_288,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_287,'#skF_6')
      | v2_struct_0(B_287)
      | ~ l1_waybel_0(B_286,'#skF_6')
      | ~ v7_waybel_0(B_286)
      | ~ v4_orders_2(B_286)
      | v2_struct_0(B_286) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_660])).

tff(c_668,plain,(
    ! [B_286,B_287,B_2] :
      ( r2_waybel_0('#skF_6',B_286,'#skF_2'('#skF_6',B_287,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_286)),B_2)))
      | r3_waybel_9('#skF_6',B_287,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_286)),B_2))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_286)),B_2),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_287,'#skF_6')
      | v2_struct_0(B_287)
      | ~ l1_waybel_0(B_286,'#skF_6')
      | ~ v7_waybel_0(B_286)
      | ~ v4_orders_2(B_286)
      | v2_struct_0(B_286)
      | ~ l1_waybel_0('#skF_8'(B_286),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_286))
      | ~ v4_orders_2('#skF_8'(B_286))
      | v2_struct_0('#skF_8'(B_286))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'(B_286)),B_2) ) ),
    inference(resolution,[status(thm)],[c_420,c_662])).

tff(c_678,plain,(
    ! [B_286,B_287,B_2] :
      ( r2_waybel_0('#skF_6',B_286,'#skF_2'('#skF_6',B_287,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_286)),B_2)))
      | r3_waybel_9('#skF_6',B_287,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_286)),B_2))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_286)),B_2),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_287,'#skF_6')
      | v2_struct_0(B_287)
      | ~ l1_waybel_0(B_286,'#skF_6')
      | ~ v7_waybel_0(B_286)
      | ~ v4_orders_2(B_286)
      | v2_struct_0(B_286)
      | ~ l1_waybel_0('#skF_8'(B_286),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_286))
      | ~ v4_orders_2('#skF_8'(B_286))
      | v2_struct_0('#skF_8'(B_286))
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'(B_286)),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_668])).

tff(c_688,plain,(
    ! [B_293,B_294,B_295] :
      ( r2_waybel_0('#skF_6',B_293,'#skF_2'('#skF_6',B_294,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_293)),B_295)))
      | r3_waybel_9('#skF_6',B_294,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_293)),B_295))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_293)),B_295),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_294,'#skF_6')
      | v2_struct_0(B_294)
      | ~ l1_waybel_0(B_293,'#skF_6')
      | ~ v7_waybel_0(B_293)
      | ~ v4_orders_2(B_293)
      | v2_struct_0(B_293)
      | ~ l1_waybel_0('#skF_8'(B_293),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_293))
      | ~ v4_orders_2('#skF_8'(B_293))
      | v2_struct_0('#skF_8'(B_293))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'(B_293)),B_295) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_678])).

tff(c_40,plain,(
    ! [A_39,B_51,C_57] :
      ( ~ r2_waybel_0(A_39,B_51,'#skF_2'(A_39,B_51,C_57))
      | r3_waybel_9(A_39,B_51,C_57)
      | ~ m1_subset_1(C_57,u1_struct_0(A_39))
      | ~ l1_waybel_0(B_51,A_39)
      | v2_struct_0(B_51)
      | ~ l1_pre_topc(A_39)
      | ~ v2_pre_topc(A_39)
      | v2_struct_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_692,plain,(
    ! [B_294,B_295] :
      ( ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | r3_waybel_9('#skF_6',B_294,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_294)),B_295))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_294)),B_295),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_294,'#skF_6')
      | ~ v7_waybel_0(B_294)
      | ~ v4_orders_2(B_294)
      | v2_struct_0(B_294)
      | ~ l1_waybel_0('#skF_8'(B_294),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_294))
      | ~ v4_orders_2('#skF_8'(B_294))
      | v2_struct_0('#skF_8'(B_294))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'(B_294)),B_295) ) ),
    inference(resolution,[status(thm)],[c_688,c_40])).

tff(c_697,plain,(
    ! [B_294,B_295] :
      ( v2_struct_0('#skF_6')
      | r3_waybel_9('#skF_6',B_294,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_294)),B_295))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_294)),B_295),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_294,'#skF_6')
      | ~ v7_waybel_0(B_294)
      | ~ v4_orders_2(B_294)
      | v2_struct_0(B_294)
      | ~ l1_waybel_0('#skF_8'(B_294),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_294))
      | ~ v4_orders_2('#skF_8'(B_294))
      | v2_struct_0('#skF_8'(B_294))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'(B_294)),B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_692])).

tff(c_703,plain,(
    ! [B_296,B_297] :
      ( r3_waybel_9('#skF_6',B_296,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_296)),B_297))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_296)),B_297),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0(B_296,'#skF_6')
      | ~ v7_waybel_0(B_296)
      | ~ v4_orders_2(B_296)
      | v2_struct_0(B_296)
      | ~ l1_waybel_0('#skF_8'(B_296),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_296))
      | ~ v4_orders_2('#skF_8'(B_296))
      | v2_struct_0('#skF_8'(B_296))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'(B_296)),B_297) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_697])).

tff(c_706,plain,(
    ! [B_296,B_2] :
      ( r3_waybel_9('#skF_6',B_296,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_296)),B_2))
      | ~ l1_waybel_0(B_296,'#skF_6')
      | ~ v7_waybel_0(B_296)
      | ~ v4_orders_2(B_296)
      | v2_struct_0(B_296)
      | ~ l1_waybel_0('#skF_8'(B_296),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_296))
      | ~ v4_orders_2('#skF_8'(B_296))
      | v2_struct_0('#skF_8'(B_296))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'(B_296)),B_2) ) ),
    inference(resolution,[status(thm)],[c_312,c_703])).

tff(c_709,plain,(
    ! [B_296,B_2] :
      ( r3_waybel_9('#skF_6',B_296,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_296)),B_2))
      | ~ l1_waybel_0(B_296,'#skF_6')
      | ~ v7_waybel_0(B_296)
      | ~ v4_orders_2(B_296)
      | v2_struct_0(B_296)
      | ~ l1_waybel_0('#skF_8'(B_296),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_296))
      | ~ v4_orders_2('#skF_8'(B_296))
      | v2_struct_0('#skF_8'(B_296))
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'(B_296)),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_706])).

tff(c_711,plain,(
    ! [B_298,B_299] :
      ( r3_waybel_9('#skF_6',B_298,'#skF_1'(k10_yellow_6('#skF_6','#skF_8'(B_298)),B_299))
      | ~ l1_waybel_0(B_298,'#skF_6')
      | ~ v7_waybel_0(B_298)
      | ~ v4_orders_2(B_298)
      | v2_struct_0(B_298)
      | ~ l1_waybel_0('#skF_8'(B_298),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_298))
      | ~ v4_orders_2('#skF_8'(B_298))
      | v2_struct_0('#skF_8'(B_298))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'(B_298)),B_299) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_709])).

tff(c_50,plain,(
    ! [A_82,C_92] :
      ( ~ r3_waybel_9(A_82,'#skF_5'(A_82),C_92)
      | ~ m1_subset_1(C_92,u1_struct_0(A_82))
      | v1_compts_1(A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_718,plain,(
    ! [B_299] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_5'('#skF_6'))
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(resolution,[status(thm)],[c_711,c_50])).

tff(c_722,plain,(
    ! [B_299] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | v1_compts_1('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_5'('#skF_6'))
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_718])).

tff(c_723,plain,(
    ! [B_299] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_5'('#skF_6'))
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_722])).

tff(c_724,plain,(
    ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_723])).

tff(c_728,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_227,c_724])).

tff(c_729,plain,(
    ~ v4_orders_2('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_728])).

tff(c_736,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_729])).

tff(c_739,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_736])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_739])).

tff(c_742,plain,
    ( ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_728])).

tff(c_744,plain,(
    ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_742])).

tff(c_769,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_744])).

tff(c_772,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_769])).

tff(c_774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_772])).

tff(c_775,plain,
    ( ~ v7_waybel_0('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_742])).

tff(c_777,plain,(
    ~ v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_775])).

tff(c_780,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_777])).

tff(c_783,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_780])).

tff(c_785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_783])).

tff(c_786,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_775])).

tff(c_58,plain,(
    ! [A_82] :
      ( ~ v2_struct_0('#skF_5'(A_82))
      | v1_compts_1(A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_794,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_786,c_58])).

tff(c_797,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_794])).

tff(c_799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_797])).

tff(c_800,plain,(
    ! [B_299] :
      ( ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_802,plain,(
    ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_800])).

tff(c_827,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_802])).

tff(c_830,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_827])).

tff(c_832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_830])).

tff(c_834,plain,(
    l1_waybel_0('#skF_5'('#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_800])).

tff(c_239,plain,(
    ! [C_151,A_152,B_153] :
      ( v7_waybel_0(C_151)
      | ~ m2_yellow_6(C_151,A_152,B_153)
      | ~ l1_waybel_0(B_153,A_152)
      | ~ v7_waybel_0(B_153)
      | ~ v4_orders_2(B_153)
      | v2_struct_0(B_153)
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_242,plain,(
    ! [B_101] :
      ( v7_waybel_0('#skF_8'(B_101))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_208,c_239])).

tff(c_245,plain,(
    ! [B_101] :
      ( v7_waybel_0('#skF_8'(B_101))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_242])).

tff(c_246,plain,(
    ! [B_101] :
      ( v7_waybel_0('#skF_8'(B_101))
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_245])).

tff(c_833,plain,(
    ! [B_299] :
      ( ~ v7_waybel_0('#skF_5'('#skF_6'))
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(splitRight,[status(thm)],[c_800])).

tff(c_835,plain,(
    ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_833])).

tff(c_838,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_246,c_835])).

tff(c_841,plain,
    ( ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_834,c_838])).

tff(c_842,plain,(
    ~ v4_orders_2('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_841])).

tff(c_849,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_842])).

tff(c_852,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_849])).

tff(c_854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_852])).

tff(c_855,plain,
    ( ~ v7_waybel_0('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_841])).

tff(c_857,plain,(
    ~ v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_855])).

tff(c_882,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_857])).

tff(c_885,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_882])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_885])).

tff(c_888,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_855])).

tff(c_892,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_888,c_58])).

tff(c_895,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_892])).

tff(c_897,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_895])).

tff(c_898,plain,(
    ! [B_299] :
      ( ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v4_orders_2('#skF_5'('#skF_6'))
      | ~ v7_waybel_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_900,plain,(
    ~ v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_898])).

tff(c_907,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_900])).

tff(c_910,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_907])).

tff(c_912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_910])).

tff(c_914,plain,(
    v7_waybel_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_898])).

tff(c_248,plain,(
    ! [C_155,A_156,B_157] :
      ( l1_waybel_0(C_155,A_156)
      | ~ m2_yellow_6(C_155,A_156,B_157)
      | ~ l1_waybel_0(B_157,A_156)
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157)
      | ~ l1_struct_0(A_156)
      | v2_struct_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_251,plain,(
    ! [B_101] :
      ( l1_waybel_0('#skF_8'(B_101),'#skF_6')
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_208,c_248])).

tff(c_254,plain,(
    ! [B_101] :
      ( l1_waybel_0('#skF_8'(B_101),'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_251])).

tff(c_255,plain,(
    ! [B_101] :
      ( l1_waybel_0('#skF_8'(B_101),'#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_254])).

tff(c_913,plain,(
    ! [B_299] :
      ( ~ v4_orders_2('#skF_5'('#skF_6'))
      | ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | v2_struct_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(splitRight,[status(thm)],[c_898])).

tff(c_915,plain,(
    ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_913])).

tff(c_940,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_255,c_915])).

tff(c_943,plain,
    ( ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_834,c_940])).

tff(c_944,plain,(
    ~ v4_orders_2('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_943])).

tff(c_947,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_944])).

tff(c_950,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_947])).

tff(c_952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_950])).

tff(c_953,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_943])).

tff(c_957,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_953,c_58])).

tff(c_960,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_957])).

tff(c_962,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_960])).

tff(c_963,plain,(
    ! [B_299] :
      ( ~ v4_orders_2('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_5'('#skF_6'))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_969,plain,(
    ~ v4_orders_2('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_963])).

tff(c_972,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_969])).

tff(c_975,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_972])).

tff(c_977,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_975])).

tff(c_979,plain,(
    v4_orders_2('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_978,plain,(
    ! [B_299] :
      ( v2_struct_0('#skF_5'('#skF_6'))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(splitRight,[status(thm)],[c_963])).

tff(c_1002,plain,(
    v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_978])).

tff(c_229,plain,(
    ! [C_146,A_147,B_148] :
      ( ~ v2_struct_0(C_146)
      | ~ m2_yellow_6(C_146,A_147,B_148)
      | ~ l1_waybel_0(B_148,A_147)
      | ~ v7_waybel_0(B_148)
      | ~ v4_orders_2(B_148)
      | v2_struct_0(B_148)
      | ~ l1_struct_0(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_232,plain,(
    ! [B_101] :
      ( ~ v2_struct_0('#skF_8'(B_101))
      | ~ l1_struct_0('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_208,c_229])).

tff(c_235,plain,(
    ! [B_101] :
      ( ~ v2_struct_0('#skF_8'(B_101))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_232])).

tff(c_236,plain,(
    ! [B_101] :
      ( ~ v2_struct_0('#skF_8'(B_101))
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_235])).

tff(c_1005,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1002,c_236])).

tff(c_1008,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_914,c_834,c_1005])).

tff(c_1011,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1008,c_58])).

tff(c_1014,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1011])).

tff(c_1016,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_1014])).

tff(c_1017,plain,(
    ! [B_299] :
      ( v2_struct_0('#skF_5'('#skF_6'))
      | ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299),u1_struct_0('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_299) ) ),
    inference(splitRight,[status(thm)],[c_978])).

tff(c_1023,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1017])).

tff(c_1026,plain,
    ( v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1023,c_58])).

tff(c_1029,plain,
    ( v1_compts_1('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1026])).

tff(c_1031,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_108,c_1029])).

tff(c_1033,plain,(
    ~ v2_struct_0('#skF_5'('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1017])).

tff(c_1018,plain,(
    ~ v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_978])).

tff(c_801,plain,(
    v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_723])).

tff(c_899,plain,(
    v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_964,plain,(
    l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_913])).

tff(c_1048,plain,(
    ! [B_347] :
      ( ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_347),u1_struct_0('#skF_6'))
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_347) ) ),
    inference(splitRight,[status(thm)],[c_1017])).

tff(c_1052,plain,(
    ! [B_2] :
      ( ~ l1_waybel_0('#skF_8'('#skF_5'('#skF_6')),'#skF_6')
      | ~ v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ v4_orders_2('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_2) ) ),
    inference(resolution,[status(thm)],[c_312,c_1048])).

tff(c_1055,plain,(
    ! [B_2] :
      ( v2_struct_0('#skF_8'('#skF_5'('#skF_6')))
      | v2_struct_0('#skF_6')
      | r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_801,c_899,c_964,c_1052])).

tff(c_1058,plain,(
    ! [B_348] : r1_tarski(k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))),B_348) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1018,c_1055])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [B_108,A_109] :
      ( B_108 = A_109
      | ~ r1_tarski(B_108,A_109)
      | ~ r1_tarski(A_109,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_120,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_111])).

tff(c_1103,plain,(
    k10_yellow_6('#skF_6','#skF_8'('#skF_5'('#skF_6'))) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1058,c_120])).

tff(c_92,plain,(
    ! [B_101] :
      ( v1_compts_1('#skF_6')
      | v3_yellow_6('#skF_8'(B_101),'#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_206,plain,(
    ! [B_101] :
      ( v3_yellow_6('#skF_8'(B_101),'#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_92])).

tff(c_262,plain,(
    ! [A_163,B_164] :
      ( k10_yellow_6(A_163,B_164) != k1_xboole_0
      | ~ v3_yellow_6(B_164,A_163)
      | ~ l1_waybel_0(B_164,A_163)
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_268,plain,(
    ! [B_101] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_101)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(B_101),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_101))
      | ~ v4_orders_2('#skF_8'(B_101))
      | v2_struct_0('#skF_8'(B_101))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(resolution,[status(thm)],[c_206,c_262])).

tff(c_272,plain,(
    ! [B_101] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_101)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(B_101),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_101))
      | ~ v4_orders_2('#skF_8'(B_101))
      | v2_struct_0('#skF_8'(B_101))
      | v2_struct_0('#skF_6')
      | ~ l1_waybel_0(B_101,'#skF_6')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_268])).

tff(c_281,plain,(
    ! [B_169] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_169)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_8'(B_169),'#skF_6')
      | ~ v7_waybel_0('#skF_8'(B_169))
      | ~ v4_orders_2('#skF_8'(B_169))
      | v2_struct_0('#skF_8'(B_169))
      | ~ l1_waybel_0(B_169,'#skF_6')
      | ~ v7_waybel_0(B_169)
      | ~ v4_orders_2(B_169)
      | v2_struct_0(B_169) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_272])).

tff(c_286,plain,(
    ! [B_170] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_170)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_8'(B_170))
      | ~ v4_orders_2('#skF_8'(B_170))
      | v2_struct_0('#skF_8'(B_170))
      | ~ l1_waybel_0(B_170,'#skF_6')
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170) ) ),
    inference(resolution,[status(thm)],[c_255,c_281])).

tff(c_291,plain,(
    ! [B_171] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_171)) != k1_xboole_0
      | ~ v4_orders_2('#skF_8'(B_171))
      | v2_struct_0('#skF_8'(B_171))
      | ~ l1_waybel_0(B_171,'#skF_6')
      | ~ v7_waybel_0(B_171)
      | ~ v4_orders_2(B_171)
      | v2_struct_0(B_171) ) ),
    inference(resolution,[status(thm)],[c_246,c_286])).

tff(c_296,plain,(
    ! [B_172] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_172)) != k1_xboole_0
      | v2_struct_0('#skF_8'(B_172))
      | ~ l1_waybel_0(B_172,'#skF_6')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172) ) ),
    inference(resolution,[status(thm)],[c_227,c_291])).

tff(c_300,plain,(
    ! [B_172] :
      ( k10_yellow_6('#skF_6','#skF_8'(B_172)) != k1_xboole_0
      | ~ l1_waybel_0(B_172,'#skF_6')
      | ~ v7_waybel_0(B_172)
      | ~ v4_orders_2(B_172)
      | v2_struct_0(B_172) ) ),
    inference(resolution,[status(thm)],[c_296,c_236])).

tff(c_1147,plain,
    ( ~ l1_waybel_0('#skF_5'('#skF_6'),'#skF_6')
    | ~ v7_waybel_0('#skF_5'('#skF_6'))
    | ~ v4_orders_2('#skF_5'('#skF_6'))
    | v2_struct_0('#skF_5'('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1103,c_300])).

tff(c_1194,plain,(
    v2_struct_0('#skF_5'('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_979,c_914,c_834,c_1147])).

tff(c_1196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1033,c_1194])).

tff(c_1197,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1198,plain,(
    v1_compts_1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,
    ( v4_orders_2('#skF_7')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_1203,plain,(
    v4_orders_2('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_76])).

tff(c_74,plain,
    ( v7_waybel_0('#skF_7')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_1200,plain,(
    v7_waybel_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_74])).

tff(c_72,plain,
    ( l1_waybel_0('#skF_7','#skF_6')
    | ~ v1_compts_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_1205,plain,(
    l1_waybel_0('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_72])).

tff(c_60,plain,(
    ! [A_82,B_89] :
      ( r3_waybel_9(A_82,B_89,'#skF_4'(A_82,B_89))
      | ~ l1_waybel_0(B_89,A_82)
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | ~ v1_compts_1(A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_62,plain,(
    ! [A_82,B_89] :
      ( m1_subset_1('#skF_4'(A_82,B_89),u1_struct_0(A_82))
      | ~ l1_waybel_0(B_89,A_82)
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | ~ v1_compts_1(A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_1363,plain,(
    ! [A_431,B_432,C_433] :
      ( m2_yellow_6('#skF_3'(A_431,B_432,C_433),A_431,B_432)
      | ~ r3_waybel_9(A_431,B_432,C_433)
      | ~ m1_subset_1(C_433,u1_struct_0(A_431))
      | ~ l1_waybel_0(B_432,A_431)
      | ~ v7_waybel_0(B_432)
      | ~ v4_orders_2(B_432)
      | v2_struct_0(B_432)
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

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

tff(c_1454,plain,(
    ! [A_452,B_453,C_454] :
      ( l1_waybel_0('#skF_3'(A_452,B_453,C_454),A_452)
      | ~ l1_struct_0(A_452)
      | ~ r3_waybel_9(A_452,B_453,C_454)
      | ~ m1_subset_1(C_454,u1_struct_0(A_452))
      | ~ l1_waybel_0(B_453,A_452)
      | ~ v7_waybel_0(B_453)
      | ~ v4_orders_2(B_453)
      | v2_struct_0(B_453)
      | ~ l1_pre_topc(A_452)
      | ~ v2_pre_topc(A_452)
      | v2_struct_0(A_452) ) ),
    inference(resolution,[status(thm)],[c_1363,c_24])).

tff(c_1723,plain,(
    ! [A_513,B_514,B_515] :
      ( l1_waybel_0('#skF_3'(A_513,B_514,'#skF_4'(A_513,B_515)),A_513)
      | ~ l1_struct_0(A_513)
      | ~ r3_waybel_9(A_513,B_514,'#skF_4'(A_513,B_515))
      | ~ l1_waybel_0(B_514,A_513)
      | ~ v7_waybel_0(B_514)
      | ~ v4_orders_2(B_514)
      | v2_struct_0(B_514)
      | ~ l1_waybel_0(B_515,A_513)
      | ~ v7_waybel_0(B_515)
      | ~ v4_orders_2(B_515)
      | v2_struct_0(B_515)
      | ~ v1_compts_1(A_513)
      | ~ l1_pre_topc(A_513)
      | ~ v2_pre_topc(A_513)
      | v2_struct_0(A_513) ) ),
    inference(resolution,[status(thm)],[c_62,c_1454])).

tff(c_34,plain,(
    ! [B_38,A_36] :
      ( v3_yellow_6(B_38,A_36)
      | k10_yellow_6(A_36,B_38) = k1_xboole_0
      | ~ l1_waybel_0(B_38,A_36)
      | ~ v7_waybel_0(B_38)
      | ~ v4_orders_2(B_38)
      | v2_struct_0(B_38)
      | ~ l1_pre_topc(A_36)
      | ~ v2_pre_topc(A_36)
      | v2_struct_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_70,plain,(
    ! [C_100] :
      ( ~ v3_yellow_6(C_100,'#skF_6')
      | ~ m2_yellow_6(C_100,'#skF_6','#skF_7')
      | ~ v1_compts_1('#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_269])).

tff(c_1207,plain,(
    ! [C_100] :
      ( ~ v3_yellow_6(C_100,'#skF_6')
      | ~ m2_yellow_6(C_100,'#skF_6','#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_70])).

tff(c_1379,plain,(
    ! [C_433] :
      ( ~ v3_yellow_6('#skF_3'('#skF_6','#skF_7',C_433),'#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7',C_433)
      | ~ m1_subset_1(C_433,u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1363,c_1207])).

tff(c_1386,plain,(
    ! [C_433] :
      ( ~ v3_yellow_6('#skF_3'('#skF_6','#skF_7',C_433),'#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7',C_433)
      | ~ m1_subset_1(C_433,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1203,c_1200,c_1205,c_1379])).

tff(c_1388,plain,(
    ! [C_434] :
      ( ~ v3_yellow_6('#skF_3'('#skF_6','#skF_7',C_434),'#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7',C_434)
      | ~ m1_subset_1(C_434,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1197,c_1386])).

tff(c_1391,plain,(
    ! [C_434] :
      ( ~ r3_waybel_9('#skF_6','#skF_7',C_434)
      | ~ m1_subset_1(C_434,u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7',C_434)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_3'('#skF_6','#skF_7',C_434),'#skF_6')
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7',C_434))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7',C_434))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7',C_434))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34,c_1388])).

tff(c_1394,plain,(
    ! [C_434] :
      ( ~ r3_waybel_9('#skF_6','#skF_7',C_434)
      | ~ m1_subset_1(C_434,u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7',C_434)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_3'('#skF_6','#skF_7',C_434),'#skF_6')
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7',C_434))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7',C_434))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7',C_434))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1391])).

tff(c_1413,plain,(
    ! [C_442] :
      ( ~ r3_waybel_9('#skF_6','#skF_7',C_442)
      | ~ m1_subset_1(C_442,u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7',C_442)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_3'('#skF_6','#skF_7',C_442),'#skF_6')
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7',C_442))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7',C_442))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7',C_442)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1394])).

tff(c_1421,plain,(
    ! [B_89] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)),'#skF_6')
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_1413])).

tff(c_1428,plain,(
    ! [B_89] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)),'#skF_6')
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1198,c_1421])).

tff(c_1429,plain,(
    ! [B_89] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)),'#skF_6')
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1428])).

tff(c_1727,plain,(
    ! [B_515] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515)))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_515))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_515,'#skF_6')
      | ~ v7_waybel_0(B_515)
      | ~ v4_orders_2(B_515)
      | v2_struct_0(B_515)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1723,c_1429])).

tff(c_1730,plain,(
    ! [B_515] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515)))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_515))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_515,'#skF_6')
      | ~ v7_waybel_0(B_515)
      | ~ v4_orders_2(B_515)
      | v2_struct_0(B_515)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1198,c_1203,c_1200,c_1205,c_1727])).

tff(c_1731,plain,(
    ! [B_515] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515)))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_515)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_515))
      | ~ l1_waybel_0(B_515,'#skF_6')
      | ~ v7_waybel_0(B_515)
      | ~ v4_orders_2(B_515)
      | v2_struct_0(B_515) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1197,c_1730])).

tff(c_1741,plain,(
    ~ l1_struct_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1731])).

tff(c_1748,plain,(
    ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_1741])).

tff(c_1752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1748])).

tff(c_1754,plain,(
    l1_struct_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1731])).

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

tff(c_1406,plain,(
    ! [A_439,B_440,C_441] :
      ( v4_orders_2('#skF_3'(A_439,B_440,C_441))
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
    inference(resolution,[status(thm)],[c_1363,c_28])).

tff(c_1412,plain,(
    ! [A_82,B_440,B_89] :
      ( v4_orders_2('#skF_3'(A_82,B_440,'#skF_4'(A_82,B_89)))
      | ~ l1_struct_0(A_82)
      | ~ r3_waybel_9(A_82,B_440,'#skF_4'(A_82,B_89))
      | ~ l1_waybel_0(B_440,A_82)
      | ~ v7_waybel_0(B_440)
      | ~ v4_orders_2(B_440)
      | v2_struct_0(B_440)
      | ~ l1_waybel_0(B_89,A_82)
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | ~ v1_compts_1(A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_62,c_1406])).

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

tff(c_1431,plain,(
    ! [A_446,B_447,C_448] :
      ( v7_waybel_0('#skF_3'(A_446,B_447,C_448))
      | ~ l1_struct_0(A_446)
      | ~ r3_waybel_9(A_446,B_447,C_448)
      | ~ m1_subset_1(C_448,u1_struct_0(A_446))
      | ~ l1_waybel_0(B_447,A_446)
      | ~ v7_waybel_0(B_447)
      | ~ v4_orders_2(B_447)
      | v2_struct_0(B_447)
      | ~ l1_pre_topc(A_446)
      | ~ v2_pre_topc(A_446)
      | v2_struct_0(A_446) ) ),
    inference(resolution,[status(thm)],[c_1363,c_26])).

tff(c_1437,plain,(
    ! [A_82,B_447,B_89] :
      ( v7_waybel_0('#skF_3'(A_82,B_447,'#skF_4'(A_82,B_89)))
      | ~ l1_struct_0(A_82)
      | ~ r3_waybel_9(A_82,B_447,'#skF_4'(A_82,B_89))
      | ~ l1_waybel_0(B_447,A_82)
      | ~ v7_waybel_0(B_447)
      | ~ v4_orders_2(B_447)
      | v2_struct_0(B_447)
      | ~ l1_waybel_0(B_89,A_82)
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | ~ v1_compts_1(A_82)
      | ~ l1_pre_topc(A_82)
      | ~ v2_pre_topc(A_82)
      | v2_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_62,c_1431])).

tff(c_1755,plain,(
    ! [B_525] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_525))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_525)))
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_525)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_525)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_525))
      | ~ l1_waybel_0(B_525,'#skF_6')
      | ~ v7_waybel_0(B_525)
      | ~ v4_orders_2(B_525)
      | v2_struct_0(B_525) ) ),
    inference(splitRight,[status(thm)],[c_1731])).

tff(c_1759,plain,(
    ! [B_89] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))) = k1_xboole_0
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1437,c_1755])).

tff(c_1762,plain,(
    ! [B_89] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))) = k1_xboole_0
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1198,c_1203,c_1200,c_1205,c_1754,c_1759])).

tff(c_1764,plain,(
    ! [B_526] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_526))) = k1_xboole_0
      | ~ v4_orders_2('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_526)))
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_526)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_526))
      | ~ l1_waybel_0(B_526,'#skF_6')
      | ~ v7_waybel_0(B_526)
      | ~ v4_orders_2(B_526)
      | v2_struct_0(B_526) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1197,c_1762])).

tff(c_1768,plain,(
    ! [B_89] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))) = k1_xboole_0
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ l1_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1412,c_1764])).

tff(c_1771,plain,(
    ! [B_89] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))) = k1_xboole_0
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1198,c_1203,c_1200,c_1205,c_1754,c_1768])).

tff(c_1773,plain,(
    ! [B_527] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_527))) = k1_xboole_0
      | v2_struct_0('#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_527)))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_527))
      | ~ l1_waybel_0(B_527,'#skF_6')
      | ~ v7_waybel_0(B_527)
      | ~ v4_orders_2(B_527)
      | v2_struct_0(B_527) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1197,c_1771])).

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

tff(c_1382,plain,(
    ! [A_431,B_432,C_433] :
      ( ~ v2_struct_0('#skF_3'(A_431,B_432,C_433))
      | ~ l1_struct_0(A_431)
      | ~ r3_waybel_9(A_431,B_432,C_433)
      | ~ m1_subset_1(C_433,u1_struct_0(A_431))
      | ~ l1_waybel_0(B_432,A_431)
      | ~ v7_waybel_0(B_432)
      | ~ v4_orders_2(B_432)
      | v2_struct_0(B_432)
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431) ) ),
    inference(resolution,[status(thm)],[c_1363,c_30])).

tff(c_1775,plain,(
    ! [B_527] :
      ( ~ l1_struct_0('#skF_6')
      | ~ m1_subset_1('#skF_4'('#skF_6',B_527),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_527))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_527))
      | ~ l1_waybel_0(B_527,'#skF_6')
      | ~ v7_waybel_0(B_527)
      | ~ v4_orders_2(B_527)
      | v2_struct_0(B_527) ) ),
    inference(resolution,[status(thm)],[c_1773,c_1382])).

tff(c_1778,plain,(
    ! [B_527] :
      ( ~ m1_subset_1('#skF_4'('#skF_6',B_527),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6')
      | k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_527))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_527))
      | ~ l1_waybel_0(B_527,'#skF_6')
      | ~ v7_waybel_0(B_527)
      | ~ v4_orders_2(B_527)
      | v2_struct_0(B_527) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1203,c_1200,c_1205,c_1754,c_1775])).

tff(c_1780,plain,(
    ! [B_528] :
      ( ~ m1_subset_1('#skF_4'('#skF_6',B_528),u1_struct_0('#skF_6'))
      | k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_528))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_528))
      | ~ l1_waybel_0(B_528,'#skF_6')
      | ~ v7_waybel_0(B_528)
      | ~ v4_orders_2(B_528)
      | v2_struct_0(B_528) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1197,c_1778])).

tff(c_1784,plain,(
    ! [B_89] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_1780])).

tff(c_1787,plain,(
    ! [B_89] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1198,c_1784])).

tff(c_1789,plain,(
    ! [B_529] :
      ( k10_yellow_6('#skF_6','#skF_3'('#skF_6','#skF_7','#skF_4'('#skF_6',B_529))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_529))
      | ~ l1_waybel_0(B_529,'#skF_6')
      | ~ v7_waybel_0(B_529)
      | ~ v4_orders_2(B_529)
      | v2_struct_0(B_529) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1787])).

tff(c_1438,plain,(
    ! [C_449,A_450,B_451] :
      ( r2_hidden(C_449,k10_yellow_6(A_450,'#skF_3'(A_450,B_451,C_449)))
      | ~ r3_waybel_9(A_450,B_451,C_449)
      | ~ m1_subset_1(C_449,u1_struct_0(A_450))
      | ~ l1_waybel_0(B_451,A_450)
      | ~ v7_waybel_0(B_451)
      | ~ v4_orders_2(B_451)
      | v2_struct_0(B_451)
      | ~ l1_pre_topc(A_450)
      | ~ v2_pre_topc(A_450)
      | v2_struct_0(A_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1453,plain,(
    ! [A_450,B_451,C_449] :
      ( ~ r1_tarski(k10_yellow_6(A_450,'#skF_3'(A_450,B_451,C_449)),C_449)
      | ~ r3_waybel_9(A_450,B_451,C_449)
      | ~ m1_subset_1(C_449,u1_struct_0(A_450))
      | ~ l1_waybel_0(B_451,A_450)
      | ~ v7_waybel_0(B_451)
      | ~ v4_orders_2(B_451)
      | v2_struct_0(B_451)
      | ~ l1_pre_topc(A_450)
      | ~ v2_pre_topc(A_450)
      | v2_struct_0(A_450) ) ),
    inference(resolution,[status(thm)],[c_1438,c_18])).

tff(c_1807,plain,(
    ! [B_529] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_4'('#skF_6',B_529))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_529))
      | ~ m1_subset_1('#skF_4'('#skF_6',B_529),u1_struct_0('#skF_6'))
      | ~ l1_waybel_0('#skF_7','#skF_6')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_529))
      | ~ l1_waybel_0(B_529,'#skF_6')
      | ~ v7_waybel_0(B_529)
      | ~ v4_orders_2(B_529)
      | v2_struct_0(B_529) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1789,c_1453])).

tff(c_1839,plain,(
    ! [B_529] :
      ( ~ m1_subset_1('#skF_4'('#skF_6',B_529),u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_6')
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_529))
      | ~ l1_waybel_0(B_529,'#skF_6')
      | ~ v7_waybel_0(B_529)
      | ~ v4_orders_2(B_529)
      | v2_struct_0(B_529) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1203,c_1200,c_1205,c_14,c_1807])).

tff(c_1860,plain,(
    ! [B_530] :
      ( ~ m1_subset_1('#skF_4'('#skF_6',B_530),u1_struct_0('#skF_6'))
      | ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_530))
      | ~ l1_waybel_0(B_530,'#skF_6')
      | ~ v7_waybel_0(B_530)
      | ~ v4_orders_2(B_530)
      | v2_struct_0(B_530) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1197,c_1839])).

tff(c_1864,plain,(
    ! [B_89] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | ~ v1_compts_1('#skF_6')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_1860])).

tff(c_1867,plain,(
    ! [B_89] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_89))
      | ~ l1_waybel_0(B_89,'#skF_6')
      | ~ v7_waybel_0(B_89)
      | ~ v4_orders_2(B_89)
      | v2_struct_0(B_89)
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1198,c_1864])).

tff(c_1869,plain,(
    ! [B_531] :
      ( ~ r3_waybel_9('#skF_6','#skF_7','#skF_4'('#skF_6',B_531))
      | ~ l1_waybel_0(B_531,'#skF_6')
      | ~ v7_waybel_0(B_531)
      | ~ v4_orders_2(B_531)
      | v2_struct_0(B_531) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1867])).

tff(c_1873,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_6')
    | ~ v7_waybel_0('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ v1_compts_1('#skF_6')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_1869])).

tff(c_1876,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1198,c_1203,c_1200,c_1205,c_1873])).

tff(c_1878,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1197,c_1876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:08:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.39/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.07  
% 5.77/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.77/2.07  %$ r3_waybel_9 > r2_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_8 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.77/2.07  
% 5.77/2.07  %Foreground sorts:
% 5.77/2.07  
% 5.77/2.07  
% 5.77/2.07  %Background operators:
% 5.77/2.07  
% 5.77/2.07  
% 5.77/2.07  %Foreground operators:
% 5.77/2.07  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.77/2.07  tff('#skF_5', type, '#skF_5': $i > $i).
% 5.77/2.07  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 5.77/2.07  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.77/2.07  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 5.77/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.77/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.77/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.77/2.07  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 5.77/2.07  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 5.77/2.07  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.77/2.07  tff('#skF_8', type, '#skF_8': $i > $i).
% 5.77/2.07  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.77/2.07  tff('#skF_7', type, '#skF_7': $i).
% 5.77/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.77/2.07  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 5.77/2.07  tff('#skF_6', type, '#skF_6': $i).
% 5.77/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.77/2.07  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.77/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.77/2.07  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.77/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.77/2.07  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.77/2.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.77/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.77/2.07  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.77/2.07  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.77/2.07  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.77/2.07  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 5.77/2.07  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.77/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.77/2.07  
% 5.98/2.12  tff(f_269, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow19)).
% 5.98/2.12  tff(f_244, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_yellow19)).
% 5.98/2.12  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.98/2.12  tff(f_99, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 5.98/2.12  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.98/2.12  tff(f_73, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 5.98/2.12  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.98/2.12  tff(f_191, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_waybel_9)).
% 5.98/2.12  tff(f_167, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r3_waybel_9(A, B, C) <=> (![D]: (m1_connsp_2(D, A, C) => r2_waybel_0(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_waybel_9)).
% 5.98/2.12  tff(f_122, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (r2_waybel_0(A, C, D) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_6)).
% 5.98/2.12  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.98/2.12  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.98/2.12  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_yellow_6)).
% 5.98/2.12  tff(f_220, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 5.98/2.12  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.98/2.12  tff(c_68, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_78, plain, (~v2_struct_0('#skF_7') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_108, plain, (~v1_compts_1('#skF_6')), inference(splitLeft, [status(thm)], [c_78])).
% 5.98/2.12  tff(c_66, plain, (v2_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_64, plain, (l1_pre_topc('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_56, plain, (![A_82]: (v4_orders_2('#skF_5'(A_82)) | v1_compts_1(A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.98/2.12  tff(c_54, plain, (![A_82]: (v7_waybel_0('#skF_5'(A_82)) | v1_compts_1(A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.98/2.12  tff(c_52, plain, (![A_82]: (l1_waybel_0('#skF_5'(A_82), A_82) | v1_compts_1(A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.98/2.12  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.98/2.12  tff(c_104, plain, (![B_101]: (v1_compts_1('#skF_6') | m2_yellow_6('#skF_8'(B_101), '#skF_6', B_101) | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_208, plain, (![B_101]: (m2_yellow_6('#skF_8'(B_101), '#skF_6', B_101) | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(negUnitSimplification, [status(thm)], [c_108, c_104])).
% 5.98/2.12  tff(c_212, plain, (![C_143, A_144, B_145]: (v4_orders_2(C_143) | ~m2_yellow_6(C_143, A_144, B_145) | ~l1_waybel_0(B_145, A_144) | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.98/2.12  tff(c_215, plain, (![B_101]: (v4_orders_2('#skF_8'(B_101)) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(resolution, [status(thm)], [c_208, c_212])).
% 5.98/2.12  tff(c_218, plain, (![B_101]: (v4_orders_2('#skF_8'(B_101)) | ~l1_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(negUnitSimplification, [status(thm)], [c_68, c_215])).
% 5.98/2.12  tff(c_219, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_218])).
% 5.98/2.12  tff(c_222, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_219])).
% 5.98/2.12  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_222])).
% 5.98/2.12  tff(c_227, plain, (![B_101]: (v4_orders_2('#skF_8'(B_101)) | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(splitRight, [status(thm)], [c_218])).
% 5.98/2.12  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.98/2.12  tff(c_258, plain, (![A_161, B_162]: (m1_subset_1(k10_yellow_6(A_161, B_162), k1_zfmisc_1(u1_struct_0(A_161))) | ~l1_waybel_0(B_162, A_161) | ~v7_waybel_0(B_162) | ~v4_orders_2(B_162) | v2_struct_0(B_162) | ~l1_pre_topc(A_161) | ~v2_pre_topc(A_161) | v2_struct_0(A_161))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.98/2.12  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.98/2.12  tff(c_302, plain, (![A_174, A_175, B_176]: (m1_subset_1(A_174, u1_struct_0(A_175)) | ~r2_hidden(A_174, k10_yellow_6(A_175, B_176)) | ~l1_waybel_0(B_176, A_175) | ~v7_waybel_0(B_176) | ~v4_orders_2(B_176) | v2_struct_0(B_176) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175))), inference(resolution, [status(thm)], [c_258, c_16])).
% 5.98/2.12  tff(c_312, plain, (![A_175, B_176, B_2]: (m1_subset_1('#skF_1'(k10_yellow_6(A_175, B_176), B_2), u1_struct_0(A_175)) | ~l1_waybel_0(B_176, A_175) | ~v7_waybel_0(B_176) | ~v4_orders_2(B_176) | v2_struct_0(B_176) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175) | r1_tarski(k10_yellow_6(A_175, B_176), B_2))), inference(resolution, [status(thm)], [c_6, c_302])).
% 5.98/2.12  tff(c_320, plain, (![A_191, B_192, C_193]: (r3_waybel_9(A_191, B_192, C_193) | ~r2_hidden(C_193, k10_yellow_6(A_191, B_192)) | ~m1_subset_1(C_193, u1_struct_0(A_191)) | ~l1_waybel_0(B_192, A_191) | ~v7_waybel_0(B_192) | ~v4_orders_2(B_192) | v2_struct_0(B_192) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_191])).
% 5.98/2.12  tff(c_417, plain, (![A_234, B_235, B_236]: (r3_waybel_9(A_234, B_235, '#skF_1'(k10_yellow_6(A_234, B_235), B_236)) | ~m1_subset_1('#skF_1'(k10_yellow_6(A_234, B_235), B_236), u1_struct_0(A_234)) | ~l1_waybel_0(B_235, A_234) | ~v7_waybel_0(B_235) | ~v4_orders_2(B_235) | v2_struct_0(B_235) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234) | r1_tarski(k10_yellow_6(A_234, B_235), B_236))), inference(resolution, [status(thm)], [c_6, c_320])).
% 5.98/2.12  tff(c_420, plain, (![A_175, B_176, B_2]: (r3_waybel_9(A_175, B_176, '#skF_1'(k10_yellow_6(A_175, B_176), B_2)) | ~l1_waybel_0(B_176, A_175) | ~v7_waybel_0(B_176) | ~v4_orders_2(B_176) | v2_struct_0(B_176) | ~l1_pre_topc(A_175) | ~v2_pre_topc(A_175) | v2_struct_0(A_175) | r1_tarski(k10_yellow_6(A_175, B_176), B_2))), inference(resolution, [status(thm)], [c_312, c_417])).
% 5.98/2.12  tff(c_228, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_218])).
% 5.98/2.12  tff(c_42, plain, (![A_39, B_51, C_57]: (m1_connsp_2('#skF_2'(A_39, B_51, C_57), A_39, C_57) | r3_waybel_9(A_39, B_51, C_57) | ~m1_subset_1(C_57, u1_struct_0(A_39)) | ~l1_waybel_0(B_51, A_39) | v2_struct_0(B_51) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.98/2.12  tff(c_316, plain, (![A_187, B_188, D_189, C_190]: (r2_waybel_0(A_187, B_188, D_189) | ~m1_connsp_2(D_189, A_187, C_190) | ~r3_waybel_9(A_187, B_188, C_190) | ~m1_subset_1(C_190, u1_struct_0(A_187)) | ~l1_waybel_0(B_188, A_187) | v2_struct_0(B_188) | ~l1_pre_topc(A_187) | ~v2_pre_topc(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.98/2.12  tff(c_404, plain, (![A_226, B_227, B_228, C_229]: (r2_waybel_0(A_226, B_227, '#skF_2'(A_226, B_228, C_229)) | ~r3_waybel_9(A_226, B_227, C_229) | ~l1_waybel_0(B_227, A_226) | v2_struct_0(B_227) | r3_waybel_9(A_226, B_228, C_229) | ~m1_subset_1(C_229, u1_struct_0(A_226)) | ~l1_waybel_0(B_228, A_226) | v2_struct_0(B_228) | ~l1_pre_topc(A_226) | ~v2_pre_topc(A_226) | v2_struct_0(A_226))), inference(resolution, [status(thm)], [c_42, c_316])).
% 5.98/2.12  tff(c_32, plain, (![A_21, B_29, D_35, C_33]: (r2_waybel_0(A_21, B_29, D_35) | ~r2_waybel_0(A_21, C_33, D_35) | ~m2_yellow_6(C_33, A_21, B_29) | ~l1_waybel_0(B_29, A_21) | ~v7_waybel_0(B_29) | ~v4_orders_2(B_29) | v2_struct_0(B_29) | ~l1_struct_0(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.98/2.12  tff(c_652, plain, (![A_285, B_281, C_283, B_284, B_282]: (r2_waybel_0(A_285, B_284, '#skF_2'(A_285, B_282, C_283)) | ~m2_yellow_6(B_281, A_285, B_284) | ~l1_waybel_0(B_284, A_285) | ~v7_waybel_0(B_284) | ~v4_orders_2(B_284) | v2_struct_0(B_284) | ~l1_struct_0(A_285) | ~r3_waybel_9(A_285, B_281, C_283) | ~l1_waybel_0(B_281, A_285) | v2_struct_0(B_281) | r3_waybel_9(A_285, B_282, C_283) | ~m1_subset_1(C_283, u1_struct_0(A_285)) | ~l1_waybel_0(B_282, A_285) | v2_struct_0(B_282) | ~l1_pre_topc(A_285) | ~v2_pre_topc(A_285) | v2_struct_0(A_285))), inference(resolution, [status(thm)], [c_404, c_32])).
% 5.98/2.12  tff(c_656, plain, (![B_101, B_282, C_283]: (r2_waybel_0('#skF_6', B_101, '#skF_2'('#skF_6', B_282, C_283)) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_8'(B_101), C_283) | ~l1_waybel_0('#skF_8'(B_101), '#skF_6') | v2_struct_0('#skF_8'(B_101)) | r3_waybel_9('#skF_6', B_282, C_283) | ~m1_subset_1(C_283, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_282, '#skF_6') | v2_struct_0(B_282) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(resolution, [status(thm)], [c_208, c_652])).
% 5.98/2.12  tff(c_660, plain, (![B_101, B_282, C_283]: (r2_waybel_0('#skF_6', B_101, '#skF_2'('#skF_6', B_282, C_283)) | ~r3_waybel_9('#skF_6', '#skF_8'(B_101), C_283) | ~l1_waybel_0('#skF_8'(B_101), '#skF_6') | v2_struct_0('#skF_8'(B_101)) | r3_waybel_9('#skF_6', B_282, C_283) | ~m1_subset_1(C_283, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_282, '#skF_6') | v2_struct_0(B_282) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_228, c_656])).
% 5.98/2.12  tff(c_662, plain, (![B_286, B_287, C_288]: (r2_waybel_0('#skF_6', B_286, '#skF_2'('#skF_6', B_287, C_288)) | ~r3_waybel_9('#skF_6', '#skF_8'(B_286), C_288) | ~l1_waybel_0('#skF_8'(B_286), '#skF_6') | v2_struct_0('#skF_8'(B_286)) | r3_waybel_9('#skF_6', B_287, C_288) | ~m1_subset_1(C_288, u1_struct_0('#skF_6')) | ~l1_waybel_0(B_287, '#skF_6') | v2_struct_0(B_287) | ~l1_waybel_0(B_286, '#skF_6') | ~v7_waybel_0(B_286) | ~v4_orders_2(B_286) | v2_struct_0(B_286))), inference(negUnitSimplification, [status(thm)], [c_68, c_660])).
% 5.98/2.12  tff(c_668, plain, (![B_286, B_287, B_2]: (r2_waybel_0('#skF_6', B_286, '#skF_2'('#skF_6', B_287, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_286)), B_2))) | r3_waybel_9('#skF_6', B_287, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_286)), B_2)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_286)), B_2), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_287, '#skF_6') | v2_struct_0(B_287) | ~l1_waybel_0(B_286, '#skF_6') | ~v7_waybel_0(B_286) | ~v4_orders_2(B_286) | v2_struct_0(B_286) | ~l1_waybel_0('#skF_8'(B_286), '#skF_6') | ~v7_waybel_0('#skF_8'(B_286)) | ~v4_orders_2('#skF_8'(B_286)) | v2_struct_0('#skF_8'(B_286)) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'(B_286)), B_2))), inference(resolution, [status(thm)], [c_420, c_662])).
% 5.98/2.12  tff(c_678, plain, (![B_286, B_287, B_2]: (r2_waybel_0('#skF_6', B_286, '#skF_2'('#skF_6', B_287, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_286)), B_2))) | r3_waybel_9('#skF_6', B_287, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_286)), B_2)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_286)), B_2), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_287, '#skF_6') | v2_struct_0(B_287) | ~l1_waybel_0(B_286, '#skF_6') | ~v7_waybel_0(B_286) | ~v4_orders_2(B_286) | v2_struct_0(B_286) | ~l1_waybel_0('#skF_8'(B_286), '#skF_6') | ~v7_waybel_0('#skF_8'(B_286)) | ~v4_orders_2('#skF_8'(B_286)) | v2_struct_0('#skF_8'(B_286)) | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'(B_286)), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_668])).
% 5.98/2.12  tff(c_688, plain, (![B_293, B_294, B_295]: (r2_waybel_0('#skF_6', B_293, '#skF_2'('#skF_6', B_294, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_293)), B_295))) | r3_waybel_9('#skF_6', B_294, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_293)), B_295)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_293)), B_295), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_294, '#skF_6') | v2_struct_0(B_294) | ~l1_waybel_0(B_293, '#skF_6') | ~v7_waybel_0(B_293) | ~v4_orders_2(B_293) | v2_struct_0(B_293) | ~l1_waybel_0('#skF_8'(B_293), '#skF_6') | ~v7_waybel_0('#skF_8'(B_293)) | ~v4_orders_2('#skF_8'(B_293)) | v2_struct_0('#skF_8'(B_293)) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'(B_293)), B_295))), inference(negUnitSimplification, [status(thm)], [c_68, c_678])).
% 5.98/2.12  tff(c_40, plain, (![A_39, B_51, C_57]: (~r2_waybel_0(A_39, B_51, '#skF_2'(A_39, B_51, C_57)) | r3_waybel_9(A_39, B_51, C_57) | ~m1_subset_1(C_57, u1_struct_0(A_39)) | ~l1_waybel_0(B_51, A_39) | v2_struct_0(B_51) | ~l1_pre_topc(A_39) | ~v2_pre_topc(A_39) | v2_struct_0(A_39))), inference(cnfTransformation, [status(thm)], [f_167])).
% 5.98/2.12  tff(c_692, plain, (![B_294, B_295]: (~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | r3_waybel_9('#skF_6', B_294, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_294)), B_295)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_294)), B_295), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_294, '#skF_6') | ~v7_waybel_0(B_294) | ~v4_orders_2(B_294) | v2_struct_0(B_294) | ~l1_waybel_0('#skF_8'(B_294), '#skF_6') | ~v7_waybel_0('#skF_8'(B_294)) | ~v4_orders_2('#skF_8'(B_294)) | v2_struct_0('#skF_8'(B_294)) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'(B_294)), B_295))), inference(resolution, [status(thm)], [c_688, c_40])).
% 5.98/2.12  tff(c_697, plain, (![B_294, B_295]: (v2_struct_0('#skF_6') | r3_waybel_9('#skF_6', B_294, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_294)), B_295)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_294)), B_295), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_294, '#skF_6') | ~v7_waybel_0(B_294) | ~v4_orders_2(B_294) | v2_struct_0(B_294) | ~l1_waybel_0('#skF_8'(B_294), '#skF_6') | ~v7_waybel_0('#skF_8'(B_294)) | ~v4_orders_2('#skF_8'(B_294)) | v2_struct_0('#skF_8'(B_294)) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'(B_294)), B_295))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_692])).
% 5.98/2.12  tff(c_703, plain, (![B_296, B_297]: (r3_waybel_9('#skF_6', B_296, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_296)), B_297)) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_296)), B_297), u1_struct_0('#skF_6')) | ~l1_waybel_0(B_296, '#skF_6') | ~v7_waybel_0(B_296) | ~v4_orders_2(B_296) | v2_struct_0(B_296) | ~l1_waybel_0('#skF_8'(B_296), '#skF_6') | ~v7_waybel_0('#skF_8'(B_296)) | ~v4_orders_2('#skF_8'(B_296)) | v2_struct_0('#skF_8'(B_296)) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'(B_296)), B_297))), inference(negUnitSimplification, [status(thm)], [c_68, c_697])).
% 5.98/2.12  tff(c_706, plain, (![B_296, B_2]: (r3_waybel_9('#skF_6', B_296, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_296)), B_2)) | ~l1_waybel_0(B_296, '#skF_6') | ~v7_waybel_0(B_296) | ~v4_orders_2(B_296) | v2_struct_0(B_296) | ~l1_waybel_0('#skF_8'(B_296), '#skF_6') | ~v7_waybel_0('#skF_8'(B_296)) | ~v4_orders_2('#skF_8'(B_296)) | v2_struct_0('#skF_8'(B_296)) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'(B_296)), B_2))), inference(resolution, [status(thm)], [c_312, c_703])).
% 5.98/2.12  tff(c_709, plain, (![B_296, B_2]: (r3_waybel_9('#skF_6', B_296, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_296)), B_2)) | ~l1_waybel_0(B_296, '#skF_6') | ~v7_waybel_0(B_296) | ~v4_orders_2(B_296) | v2_struct_0(B_296) | ~l1_waybel_0('#skF_8'(B_296), '#skF_6') | ~v7_waybel_0('#skF_8'(B_296)) | ~v4_orders_2('#skF_8'(B_296)) | v2_struct_0('#skF_8'(B_296)) | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'(B_296)), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_706])).
% 5.98/2.12  tff(c_711, plain, (![B_298, B_299]: (r3_waybel_9('#skF_6', B_298, '#skF_1'(k10_yellow_6('#skF_6', '#skF_8'(B_298)), B_299)) | ~l1_waybel_0(B_298, '#skF_6') | ~v7_waybel_0(B_298) | ~v4_orders_2(B_298) | v2_struct_0(B_298) | ~l1_waybel_0('#skF_8'(B_298), '#skF_6') | ~v7_waybel_0('#skF_8'(B_298)) | ~v4_orders_2('#skF_8'(B_298)) | v2_struct_0('#skF_8'(B_298)) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'(B_298)), B_299))), inference(negUnitSimplification, [status(thm)], [c_68, c_709])).
% 5.98/2.12  tff(c_50, plain, (![A_82, C_92]: (~r3_waybel_9(A_82, '#skF_5'(A_82), C_92) | ~m1_subset_1(C_92, u1_struct_0(A_82)) | v1_compts_1(A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.98/2.12  tff(c_718, plain, (![B_299]: (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6')) | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(resolution, [status(thm)], [c_711, c_50])).
% 5.98/2.12  tff(c_722, plain, (![B_299]: (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | v1_compts_1('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6')) | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_718])).
% 5.98/2.12  tff(c_723, plain, (![B_299]: (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6')) | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_722])).
% 5.98/2.12  tff(c_724, plain, (~v4_orders_2('#skF_8'('#skF_5'('#skF_6')))), inference(splitLeft, [status(thm)], [c_723])).
% 5.98/2.12  tff(c_728, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_227, c_724])).
% 5.98/2.12  tff(c_729, plain, (~v4_orders_2('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_728])).
% 5.98/2.12  tff(c_736, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_729])).
% 5.98/2.12  tff(c_739, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_736])).
% 5.98/2.12  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_739])).
% 5.98/2.12  tff(c_742, plain, (~v7_waybel_0('#skF_5'('#skF_6')) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_728])).
% 5.98/2.12  tff(c_744, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_742])).
% 5.98/2.12  tff(c_769, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_744])).
% 5.98/2.12  tff(c_772, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_769])).
% 5.98/2.12  tff(c_774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_772])).
% 5.98/2.12  tff(c_775, plain, (~v7_waybel_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_742])).
% 5.98/2.12  tff(c_777, plain, (~v7_waybel_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_775])).
% 5.98/2.12  tff(c_780, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_777])).
% 5.98/2.12  tff(c_783, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_780])).
% 5.98/2.12  tff(c_785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_783])).
% 5.98/2.12  tff(c_786, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_775])).
% 5.98/2.12  tff(c_58, plain, (![A_82]: (~v2_struct_0('#skF_5'(A_82)) | v1_compts_1(A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.98/2.12  tff(c_794, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_786, c_58])).
% 5.98/2.12  tff(c_797, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_794])).
% 5.98/2.12  tff(c_799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_797])).
% 5.98/2.12  tff(c_800, plain, (![B_299]: (~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v4_orders_2('#skF_5'('#skF_6')) | ~v7_waybel_0('#skF_5'('#skF_6')) | ~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(splitRight, [status(thm)], [c_723])).
% 5.98/2.12  tff(c_802, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitLeft, [status(thm)], [c_800])).
% 5.98/2.12  tff(c_827, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_52, c_802])).
% 5.98/2.12  tff(c_830, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_827])).
% 5.98/2.12  tff(c_832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_830])).
% 5.98/2.12  tff(c_834, plain, (l1_waybel_0('#skF_5'('#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_800])).
% 5.98/2.12  tff(c_239, plain, (![C_151, A_152, B_153]: (v7_waybel_0(C_151) | ~m2_yellow_6(C_151, A_152, B_153) | ~l1_waybel_0(B_153, A_152) | ~v7_waybel_0(B_153) | ~v4_orders_2(B_153) | v2_struct_0(B_153) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.98/2.12  tff(c_242, plain, (![B_101]: (v7_waybel_0('#skF_8'(B_101)) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(resolution, [status(thm)], [c_208, c_239])).
% 5.98/2.12  tff(c_245, plain, (![B_101]: (v7_waybel_0('#skF_8'(B_101)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_242])).
% 5.98/2.12  tff(c_246, plain, (![B_101]: (v7_waybel_0('#skF_8'(B_101)) | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(negUnitSimplification, [status(thm)], [c_68, c_245])).
% 5.98/2.12  tff(c_833, plain, (![B_299]: (~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(splitRight, [status(thm)], [c_800])).
% 5.98/2.12  tff(c_835, plain, (~v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitLeft, [status(thm)], [c_833])).
% 5.98/2.12  tff(c_838, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_246, c_835])).
% 5.98/2.12  tff(c_841, plain, (~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_834, c_838])).
% 5.98/2.12  tff(c_842, plain, (~v4_orders_2('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_841])).
% 5.98/2.12  tff(c_849, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_842])).
% 5.98/2.12  tff(c_852, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_849])).
% 5.98/2.12  tff(c_854, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_852])).
% 5.98/2.12  tff(c_855, plain, (~v7_waybel_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_841])).
% 5.98/2.12  tff(c_857, plain, (~v7_waybel_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_855])).
% 5.98/2.12  tff(c_882, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_857])).
% 5.98/2.12  tff(c_885, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_882])).
% 5.98/2.12  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_885])).
% 5.98/2.12  tff(c_888, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_855])).
% 5.98/2.12  tff(c_892, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_888, c_58])).
% 5.98/2.12  tff(c_895, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_892])).
% 5.98/2.12  tff(c_897, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_895])).
% 5.98/2.12  tff(c_898, plain, (![B_299]: (~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v4_orders_2('#skF_5'('#skF_6')) | ~v7_waybel_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(splitRight, [status(thm)], [c_833])).
% 5.98/2.12  tff(c_900, plain, (~v7_waybel_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_898])).
% 5.98/2.12  tff(c_907, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_54, c_900])).
% 5.98/2.12  tff(c_910, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_907])).
% 5.98/2.12  tff(c_912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_910])).
% 5.98/2.12  tff(c_914, plain, (v7_waybel_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_898])).
% 5.98/2.12  tff(c_248, plain, (![C_155, A_156, B_157]: (l1_waybel_0(C_155, A_156) | ~m2_yellow_6(C_155, A_156, B_157) | ~l1_waybel_0(B_157, A_156) | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157) | ~l1_struct_0(A_156) | v2_struct_0(A_156))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.98/2.12  tff(c_251, plain, (![B_101]: (l1_waybel_0('#skF_8'(B_101), '#skF_6') | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(resolution, [status(thm)], [c_208, c_248])).
% 5.98/2.12  tff(c_254, plain, (![B_101]: (l1_waybel_0('#skF_8'(B_101), '#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_251])).
% 5.98/2.12  tff(c_255, plain, (![B_101]: (l1_waybel_0('#skF_8'(B_101), '#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(negUnitSimplification, [status(thm)], [c_68, c_254])).
% 5.98/2.12  tff(c_913, plain, (![B_299]: (~v4_orders_2('#skF_5'('#skF_6')) | ~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | v2_struct_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(splitRight, [status(thm)], [c_898])).
% 5.98/2.12  tff(c_915, plain, (~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6')), inference(splitLeft, [status(thm)], [c_913])).
% 5.98/2.12  tff(c_940, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_255, c_915])).
% 5.98/2.12  tff(c_943, plain, (~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_914, c_834, c_940])).
% 5.98/2.12  tff(c_944, plain, (~v4_orders_2('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_943])).
% 5.98/2.12  tff(c_947, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_944])).
% 5.98/2.12  tff(c_950, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_947])).
% 5.98/2.12  tff(c_952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_950])).
% 5.98/2.12  tff(c_953, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_943])).
% 5.98/2.12  tff(c_957, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_953, c_58])).
% 5.98/2.12  tff(c_960, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_957])).
% 5.98/2.12  tff(c_962, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_960])).
% 5.98/2.12  tff(c_963, plain, (![B_299]: (~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_5'('#skF_6')) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(splitRight, [status(thm)], [c_913])).
% 5.98/2.12  tff(c_969, plain, (~v4_orders_2('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_963])).
% 5.98/2.12  tff(c_972, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_969])).
% 5.98/2.12  tff(c_975, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_972])).
% 5.98/2.12  tff(c_977, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_975])).
% 5.98/2.12  tff(c_979, plain, (v4_orders_2('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_963])).
% 5.98/2.12  tff(c_978, plain, (![B_299]: (v2_struct_0('#skF_5'('#skF_6')) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(splitRight, [status(thm)], [c_963])).
% 5.98/2.12  tff(c_1002, plain, (v2_struct_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitLeft, [status(thm)], [c_978])).
% 5.98/2.12  tff(c_229, plain, (![C_146, A_147, B_148]: (~v2_struct_0(C_146) | ~m2_yellow_6(C_146, A_147, B_148) | ~l1_waybel_0(B_148, A_147) | ~v7_waybel_0(B_148) | ~v4_orders_2(B_148) | v2_struct_0(B_148) | ~l1_struct_0(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.98/2.12  tff(c_232, plain, (![B_101]: (~v2_struct_0('#skF_8'(B_101)) | ~l1_struct_0('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(resolution, [status(thm)], [c_208, c_229])).
% 5.98/2.12  tff(c_235, plain, (![B_101]: (~v2_struct_0('#skF_8'(B_101)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_232])).
% 5.98/2.12  tff(c_236, plain, (![B_101]: (~v2_struct_0('#skF_8'(B_101)) | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(negUnitSimplification, [status(thm)], [c_68, c_235])).
% 5.98/2.12  tff(c_1005, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(resolution, [status(thm)], [c_1002, c_236])).
% 5.98/2.12  tff(c_1008, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_979, c_914, c_834, c_1005])).
% 5.98/2.12  tff(c_1011, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1008, c_58])).
% 5.98/2.12  tff(c_1014, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1011])).
% 5.98/2.12  tff(c_1016, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_1014])).
% 5.98/2.12  tff(c_1017, plain, (![B_299]: (v2_struct_0('#skF_5'('#skF_6')) | ~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299), u1_struct_0('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_299))), inference(splitRight, [status(thm)], [c_978])).
% 5.98/2.12  tff(c_1023, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(splitLeft, [status(thm)], [c_1017])).
% 5.98/2.12  tff(c_1026, plain, (v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_1023, c_58])).
% 5.98/2.12  tff(c_1029, plain, (v1_compts_1('#skF_6') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1026])).
% 5.98/2.12  tff(c_1031, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_108, c_1029])).
% 5.98/2.12  tff(c_1033, plain, (~v2_struct_0('#skF_5'('#skF_6'))), inference(splitRight, [status(thm)], [c_1017])).
% 5.98/2.12  tff(c_1018, plain, (~v2_struct_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitRight, [status(thm)], [c_978])).
% 5.98/2.12  tff(c_801, plain, (v4_orders_2('#skF_8'('#skF_5'('#skF_6')))), inference(splitRight, [status(thm)], [c_723])).
% 5.98/2.12  tff(c_899, plain, (v7_waybel_0('#skF_8'('#skF_5'('#skF_6')))), inference(splitRight, [status(thm)], [c_833])).
% 5.98/2.12  tff(c_964, plain, (l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6')), inference(splitRight, [status(thm)], [c_913])).
% 5.98/2.12  tff(c_1048, plain, (![B_347]: (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_347), u1_struct_0('#skF_6')) | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_347))), inference(splitRight, [status(thm)], [c_1017])).
% 5.98/2.12  tff(c_1052, plain, (![B_2]: (~l1_waybel_0('#skF_8'('#skF_5'('#skF_6')), '#skF_6') | ~v7_waybel_0('#skF_8'('#skF_5'('#skF_6'))) | ~v4_orders_2('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_2))), inference(resolution, [status(thm)], [c_312, c_1048])).
% 5.98/2.12  tff(c_1055, plain, (![B_2]: (v2_struct_0('#skF_8'('#skF_5'('#skF_6'))) | v2_struct_0('#skF_6') | r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_2))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_801, c_899, c_964, c_1052])).
% 5.98/2.12  tff(c_1058, plain, (![B_348]: (r1_tarski(k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6'))), B_348))), inference(negUnitSimplification, [status(thm)], [c_68, c_1018, c_1055])).
% 5.98/2.12  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.98/2.12  tff(c_111, plain, (![B_108, A_109]: (B_108=A_109 | ~r1_tarski(B_108, A_109) | ~r1_tarski(A_109, B_108))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.98/2.12  tff(c_120, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_111])).
% 5.98/2.12  tff(c_1103, plain, (k10_yellow_6('#skF_6', '#skF_8'('#skF_5'('#skF_6')))=k1_xboole_0), inference(resolution, [status(thm)], [c_1058, c_120])).
% 5.98/2.12  tff(c_92, plain, (![B_101]: (v1_compts_1('#skF_6') | v3_yellow_6('#skF_8'(B_101), '#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_206, plain, (![B_101]: (v3_yellow_6('#skF_8'(B_101), '#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(negUnitSimplification, [status(thm)], [c_108, c_92])).
% 5.98/2.12  tff(c_262, plain, (![A_163, B_164]: (k10_yellow_6(A_163, B_164)!=k1_xboole_0 | ~v3_yellow_6(B_164, A_163) | ~l1_waybel_0(B_164, A_163) | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.98/2.12  tff(c_268, plain, (![B_101]: (k10_yellow_6('#skF_6', '#skF_8'(B_101))!=k1_xboole_0 | ~l1_waybel_0('#skF_8'(B_101), '#skF_6') | ~v7_waybel_0('#skF_8'(B_101)) | ~v4_orders_2('#skF_8'(B_101)) | v2_struct_0('#skF_8'(B_101)) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(resolution, [status(thm)], [c_206, c_262])).
% 5.98/2.12  tff(c_272, plain, (![B_101]: (k10_yellow_6('#skF_6', '#skF_8'(B_101))!=k1_xboole_0 | ~l1_waybel_0('#skF_8'(B_101), '#skF_6') | ~v7_waybel_0('#skF_8'(B_101)) | ~v4_orders_2('#skF_8'(B_101)) | v2_struct_0('#skF_8'(B_101)) | v2_struct_0('#skF_6') | ~l1_waybel_0(B_101, '#skF_6') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_268])).
% 5.98/2.12  tff(c_281, plain, (![B_169]: (k10_yellow_6('#skF_6', '#skF_8'(B_169))!=k1_xboole_0 | ~l1_waybel_0('#skF_8'(B_169), '#skF_6') | ~v7_waybel_0('#skF_8'(B_169)) | ~v4_orders_2('#skF_8'(B_169)) | v2_struct_0('#skF_8'(B_169)) | ~l1_waybel_0(B_169, '#skF_6') | ~v7_waybel_0(B_169) | ~v4_orders_2(B_169) | v2_struct_0(B_169))), inference(negUnitSimplification, [status(thm)], [c_68, c_272])).
% 5.98/2.12  tff(c_286, plain, (![B_170]: (k10_yellow_6('#skF_6', '#skF_8'(B_170))!=k1_xboole_0 | ~v7_waybel_0('#skF_8'(B_170)) | ~v4_orders_2('#skF_8'(B_170)) | v2_struct_0('#skF_8'(B_170)) | ~l1_waybel_0(B_170, '#skF_6') | ~v7_waybel_0(B_170) | ~v4_orders_2(B_170) | v2_struct_0(B_170))), inference(resolution, [status(thm)], [c_255, c_281])).
% 5.98/2.12  tff(c_291, plain, (![B_171]: (k10_yellow_6('#skF_6', '#skF_8'(B_171))!=k1_xboole_0 | ~v4_orders_2('#skF_8'(B_171)) | v2_struct_0('#skF_8'(B_171)) | ~l1_waybel_0(B_171, '#skF_6') | ~v7_waybel_0(B_171) | ~v4_orders_2(B_171) | v2_struct_0(B_171))), inference(resolution, [status(thm)], [c_246, c_286])).
% 5.98/2.12  tff(c_296, plain, (![B_172]: (k10_yellow_6('#skF_6', '#skF_8'(B_172))!=k1_xboole_0 | v2_struct_0('#skF_8'(B_172)) | ~l1_waybel_0(B_172, '#skF_6') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172))), inference(resolution, [status(thm)], [c_227, c_291])).
% 5.98/2.12  tff(c_300, plain, (![B_172]: (k10_yellow_6('#skF_6', '#skF_8'(B_172))!=k1_xboole_0 | ~l1_waybel_0(B_172, '#skF_6') | ~v7_waybel_0(B_172) | ~v4_orders_2(B_172) | v2_struct_0(B_172))), inference(resolution, [status(thm)], [c_296, c_236])).
% 5.98/2.12  tff(c_1147, plain, (~l1_waybel_0('#skF_5'('#skF_6'), '#skF_6') | ~v7_waybel_0('#skF_5'('#skF_6')) | ~v4_orders_2('#skF_5'('#skF_6')) | v2_struct_0('#skF_5'('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1103, c_300])).
% 5.98/2.12  tff(c_1194, plain, (v2_struct_0('#skF_5'('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_979, c_914, c_834, c_1147])).
% 5.98/2.12  tff(c_1196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1033, c_1194])).
% 5.98/2.12  tff(c_1197, plain, (~v2_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 5.98/2.12  tff(c_1198, plain, (v1_compts_1('#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 5.98/2.12  tff(c_76, plain, (v4_orders_2('#skF_7') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_1203, plain, (v4_orders_2('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_76])).
% 5.98/2.12  tff(c_74, plain, (v7_waybel_0('#skF_7') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_1200, plain, (v7_waybel_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_74])).
% 5.98/2.12  tff(c_72, plain, (l1_waybel_0('#skF_7', '#skF_6') | ~v1_compts_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_1205, plain, (l1_waybel_0('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_72])).
% 5.98/2.12  tff(c_60, plain, (![A_82, B_89]: (r3_waybel_9(A_82, B_89, '#skF_4'(A_82, B_89)) | ~l1_waybel_0(B_89, A_82) | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | ~v1_compts_1(A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.98/2.12  tff(c_62, plain, (![A_82, B_89]: (m1_subset_1('#skF_4'(A_82, B_89), u1_struct_0(A_82)) | ~l1_waybel_0(B_89, A_82) | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | ~v1_compts_1(A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(cnfTransformation, [status(thm)], [f_244])).
% 5.98/2.12  tff(c_1363, plain, (![A_431, B_432, C_433]: (m2_yellow_6('#skF_3'(A_431, B_432, C_433), A_431, B_432) | ~r3_waybel_9(A_431, B_432, C_433) | ~m1_subset_1(C_433, u1_struct_0(A_431)) | ~l1_waybel_0(B_432, A_431) | ~v7_waybel_0(B_432) | ~v4_orders_2(B_432) | v2_struct_0(B_432) | ~l1_pre_topc(A_431) | ~v2_pre_topc(A_431) | v2_struct_0(A_431))), inference(cnfTransformation, [status(thm)], [f_220])).
% 5.98/2.12  tff(c_24, plain, (![C_20, A_17, B_18]: (l1_waybel_0(C_20, A_17) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.98/2.12  tff(c_1454, plain, (![A_452, B_453, C_454]: (l1_waybel_0('#skF_3'(A_452, B_453, C_454), A_452) | ~l1_struct_0(A_452) | ~r3_waybel_9(A_452, B_453, C_454) | ~m1_subset_1(C_454, u1_struct_0(A_452)) | ~l1_waybel_0(B_453, A_452) | ~v7_waybel_0(B_453) | ~v4_orders_2(B_453) | v2_struct_0(B_453) | ~l1_pre_topc(A_452) | ~v2_pre_topc(A_452) | v2_struct_0(A_452))), inference(resolution, [status(thm)], [c_1363, c_24])).
% 5.98/2.12  tff(c_1723, plain, (![A_513, B_514, B_515]: (l1_waybel_0('#skF_3'(A_513, B_514, '#skF_4'(A_513, B_515)), A_513) | ~l1_struct_0(A_513) | ~r3_waybel_9(A_513, B_514, '#skF_4'(A_513, B_515)) | ~l1_waybel_0(B_514, A_513) | ~v7_waybel_0(B_514) | ~v4_orders_2(B_514) | v2_struct_0(B_514) | ~l1_waybel_0(B_515, A_513) | ~v7_waybel_0(B_515) | ~v4_orders_2(B_515) | v2_struct_0(B_515) | ~v1_compts_1(A_513) | ~l1_pre_topc(A_513) | ~v2_pre_topc(A_513) | v2_struct_0(A_513))), inference(resolution, [status(thm)], [c_62, c_1454])).
% 5.98/2.12  tff(c_34, plain, (![B_38, A_36]: (v3_yellow_6(B_38, A_36) | k10_yellow_6(A_36, B_38)=k1_xboole_0 | ~l1_waybel_0(B_38, A_36) | ~v7_waybel_0(B_38) | ~v4_orders_2(B_38) | v2_struct_0(B_38) | ~l1_pre_topc(A_36) | ~v2_pre_topc(A_36) | v2_struct_0(A_36))), inference(cnfTransformation, [status(thm)], [f_144])).
% 5.98/2.12  tff(c_70, plain, (![C_100]: (~v3_yellow_6(C_100, '#skF_6') | ~m2_yellow_6(C_100, '#skF_6', '#skF_7') | ~v1_compts_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_269])).
% 5.98/2.12  tff(c_1207, plain, (![C_100]: (~v3_yellow_6(C_100, '#skF_6') | ~m2_yellow_6(C_100, '#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1198, c_70])).
% 5.98/2.12  tff(c_1379, plain, (![C_433]: (~v3_yellow_6('#skF_3'('#skF_6', '#skF_7', C_433), '#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', C_433) | ~m1_subset_1(C_433, u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1363, c_1207])).
% 5.98/2.12  tff(c_1386, plain, (![C_433]: (~v3_yellow_6('#skF_3'('#skF_6', '#skF_7', C_433), '#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', C_433) | ~m1_subset_1(C_433, u1_struct_0('#skF_6')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1203, c_1200, c_1205, c_1379])).
% 5.98/2.12  tff(c_1388, plain, (![C_434]: (~v3_yellow_6('#skF_3'('#skF_6', '#skF_7', C_434), '#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', C_434) | ~m1_subset_1(C_434, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_1197, c_1386])).
% 5.98/2.12  tff(c_1391, plain, (![C_434]: (~r3_waybel_9('#skF_6', '#skF_7', C_434) | ~m1_subset_1(C_434, u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', C_434))=k1_xboole_0 | ~l1_waybel_0('#skF_3'('#skF_6', '#skF_7', C_434), '#skF_6') | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', C_434)) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', C_434)) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', C_434)) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_34, c_1388])).
% 5.98/2.12  tff(c_1394, plain, (![C_434]: (~r3_waybel_9('#skF_6', '#skF_7', C_434) | ~m1_subset_1(C_434, u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', C_434))=k1_xboole_0 | ~l1_waybel_0('#skF_3'('#skF_6', '#skF_7', C_434), '#skF_6') | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', C_434)) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', C_434)) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', C_434)) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1391])).
% 5.98/2.12  tff(c_1413, plain, (![C_442]: (~r3_waybel_9('#skF_6', '#skF_7', C_442) | ~m1_subset_1(C_442, u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', C_442))=k1_xboole_0 | ~l1_waybel_0('#skF_3'('#skF_6', '#skF_7', C_442), '#skF_6') | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', C_442)) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', C_442)) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', C_442)))), inference(negUnitSimplification, [status(thm)], [c_68, c_1394])).
% 5.98/2.12  tff(c_1421, plain, (![B_89]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)))=k1_xboole_0 | ~l1_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)), '#skF_6') | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_1413])).
% 5.98/2.12  tff(c_1428, plain, (![B_89]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)))=k1_xboole_0 | ~l1_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)), '#skF_6') | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1198, c_1421])).
% 5.98/2.12  tff(c_1429, plain, (![B_89]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)))=k1_xboole_0 | ~l1_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)), '#skF_6') | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89))), inference(negUnitSimplification, [status(thm)], [c_68, c_1428])).
% 5.98/2.12  tff(c_1727, plain, (![B_515]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515)))=k1_xboole_0 | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515))) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515)) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_515, '#skF_6') | ~v7_waybel_0(B_515) | ~v4_orders_2(B_515) | v2_struct_0(B_515) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1723, c_1429])).
% 5.98/2.12  tff(c_1730, plain, (![B_515]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515)))=k1_xboole_0 | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515))) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_515, '#skF_6') | ~v7_waybel_0(B_515) | ~v4_orders_2(B_515) | v2_struct_0(B_515) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1198, c_1203, c_1200, c_1205, c_1727])).
% 5.98/2.12  tff(c_1731, plain, (![B_515]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515)))=k1_xboole_0 | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515))) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_515)) | ~l1_waybel_0(B_515, '#skF_6') | ~v7_waybel_0(B_515) | ~v4_orders_2(B_515) | v2_struct_0(B_515))), inference(negUnitSimplification, [status(thm)], [c_68, c_1197, c_1730])).
% 5.98/2.12  tff(c_1741, plain, (~l1_struct_0('#skF_6')), inference(splitLeft, [status(thm)], [c_1731])).
% 5.98/2.12  tff(c_1748, plain, (~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_20, c_1741])).
% 5.98/2.12  tff(c_1752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_1748])).
% 5.98/2.12  tff(c_1754, plain, (l1_struct_0('#skF_6')), inference(splitRight, [status(thm)], [c_1731])).
% 5.98/2.12  tff(c_28, plain, (![C_20, A_17, B_18]: (v4_orders_2(C_20) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.98/2.12  tff(c_1406, plain, (![A_439, B_440, C_441]: (v4_orders_2('#skF_3'(A_439, B_440, C_441)) | ~l1_struct_0(A_439) | ~r3_waybel_9(A_439, B_440, C_441) | ~m1_subset_1(C_441, u1_struct_0(A_439)) | ~l1_waybel_0(B_440, A_439) | ~v7_waybel_0(B_440) | ~v4_orders_2(B_440) | v2_struct_0(B_440) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439) | v2_struct_0(A_439))), inference(resolution, [status(thm)], [c_1363, c_28])).
% 5.98/2.12  tff(c_1412, plain, (![A_82, B_440, B_89]: (v4_orders_2('#skF_3'(A_82, B_440, '#skF_4'(A_82, B_89))) | ~l1_struct_0(A_82) | ~r3_waybel_9(A_82, B_440, '#skF_4'(A_82, B_89)) | ~l1_waybel_0(B_440, A_82) | ~v7_waybel_0(B_440) | ~v4_orders_2(B_440) | v2_struct_0(B_440) | ~l1_waybel_0(B_89, A_82) | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | ~v1_compts_1(A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(resolution, [status(thm)], [c_62, c_1406])).
% 5.98/2.12  tff(c_26, plain, (![C_20, A_17, B_18]: (v7_waybel_0(C_20) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.98/2.12  tff(c_1431, plain, (![A_446, B_447, C_448]: (v7_waybel_0('#skF_3'(A_446, B_447, C_448)) | ~l1_struct_0(A_446) | ~r3_waybel_9(A_446, B_447, C_448) | ~m1_subset_1(C_448, u1_struct_0(A_446)) | ~l1_waybel_0(B_447, A_446) | ~v7_waybel_0(B_447) | ~v4_orders_2(B_447) | v2_struct_0(B_447) | ~l1_pre_topc(A_446) | ~v2_pre_topc(A_446) | v2_struct_0(A_446))), inference(resolution, [status(thm)], [c_1363, c_26])).
% 5.98/2.12  tff(c_1437, plain, (![A_82, B_447, B_89]: (v7_waybel_0('#skF_3'(A_82, B_447, '#skF_4'(A_82, B_89))) | ~l1_struct_0(A_82) | ~r3_waybel_9(A_82, B_447, '#skF_4'(A_82, B_89)) | ~l1_waybel_0(B_447, A_82) | ~v7_waybel_0(B_447) | ~v4_orders_2(B_447) | v2_struct_0(B_447) | ~l1_waybel_0(B_89, A_82) | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | ~v1_compts_1(A_82) | ~l1_pre_topc(A_82) | ~v2_pre_topc(A_82) | v2_struct_0(A_82))), inference(resolution, [status(thm)], [c_62, c_1431])).
% 5.98/2.12  tff(c_1755, plain, (![B_525]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_525)))=k1_xboole_0 | ~v7_waybel_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_525))) | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_525))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_525))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_525)) | ~l1_waybel_0(B_525, '#skF_6') | ~v7_waybel_0(B_525) | ~v4_orders_2(B_525) | v2_struct_0(B_525))), inference(splitRight, [status(thm)], [c_1731])).
% 5.98/2.12  tff(c_1759, plain, (![B_89]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)))=k1_xboole_0 | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1437, c_1755])).
% 5.98/2.12  tff(c_1762, plain, (![B_89]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)))=k1_xboole_0 | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1198, c_1203, c_1200, c_1205, c_1754, c_1759])).
% 5.98/2.12  tff(c_1764, plain, (![B_526]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_526)))=k1_xboole_0 | ~v4_orders_2('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_526))) | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_526))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_526)) | ~l1_waybel_0(B_526, '#skF_6') | ~v7_waybel_0(B_526) | ~v4_orders_2(B_526) | v2_struct_0(B_526))), inference(negUnitSimplification, [status(thm)], [c_68, c_1197, c_1762])).
% 5.98/2.12  tff(c_1768, plain, (![B_89]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)))=k1_xboole_0 | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~l1_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1412, c_1764])).
% 5.98/2.12  tff(c_1771, plain, (![B_89]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)))=k1_xboole_0 | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1198, c_1203, c_1200, c_1205, c_1754, c_1768])).
% 5.98/2.12  tff(c_1773, plain, (![B_527]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_527)))=k1_xboole_0 | v2_struct_0('#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_527))) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_527)) | ~l1_waybel_0(B_527, '#skF_6') | ~v7_waybel_0(B_527) | ~v4_orders_2(B_527) | v2_struct_0(B_527))), inference(negUnitSimplification, [status(thm)], [c_68, c_1197, c_1771])).
% 5.98/2.12  tff(c_30, plain, (![C_20, A_17, B_18]: (~v2_struct_0(C_20) | ~m2_yellow_6(C_20, A_17, B_18) | ~l1_waybel_0(B_18, A_17) | ~v7_waybel_0(B_18) | ~v4_orders_2(B_18) | v2_struct_0(B_18) | ~l1_struct_0(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.98/2.12  tff(c_1382, plain, (![A_431, B_432, C_433]: (~v2_struct_0('#skF_3'(A_431, B_432, C_433)) | ~l1_struct_0(A_431) | ~r3_waybel_9(A_431, B_432, C_433) | ~m1_subset_1(C_433, u1_struct_0(A_431)) | ~l1_waybel_0(B_432, A_431) | ~v7_waybel_0(B_432) | ~v4_orders_2(B_432) | v2_struct_0(B_432) | ~l1_pre_topc(A_431) | ~v2_pre_topc(A_431) | v2_struct_0(A_431))), inference(resolution, [status(thm)], [c_1363, c_30])).
% 5.98/2.12  tff(c_1775, plain, (![B_527]: (~l1_struct_0('#skF_6') | ~m1_subset_1('#skF_4'('#skF_6', B_527), u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_527)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_527)) | ~l1_waybel_0(B_527, '#skF_6') | ~v7_waybel_0(B_527) | ~v4_orders_2(B_527) | v2_struct_0(B_527))), inference(resolution, [status(thm)], [c_1773, c_1382])).
% 5.98/2.12  tff(c_1778, plain, (![B_527]: (~m1_subset_1('#skF_4'('#skF_6', B_527), u1_struct_0('#skF_6')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_527)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_527)) | ~l1_waybel_0(B_527, '#skF_6') | ~v7_waybel_0(B_527) | ~v4_orders_2(B_527) | v2_struct_0(B_527))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1203, c_1200, c_1205, c_1754, c_1775])).
% 5.98/2.12  tff(c_1780, plain, (![B_528]: (~m1_subset_1('#skF_4'('#skF_6', B_528), u1_struct_0('#skF_6')) | k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_528)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_528)) | ~l1_waybel_0(B_528, '#skF_6') | ~v7_waybel_0(B_528) | ~v4_orders_2(B_528) | v2_struct_0(B_528))), inference(negUnitSimplification, [status(thm)], [c_68, c_1197, c_1778])).
% 5.98/2.12  tff(c_1784, plain, (![B_89]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_1780])).
% 5.98/2.12  tff(c_1787, plain, (![B_89]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1198, c_1784])).
% 5.98/2.12  tff(c_1789, plain, (![B_529]: (k10_yellow_6('#skF_6', '#skF_3'('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_529)))=k1_xboole_0 | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_529)) | ~l1_waybel_0(B_529, '#skF_6') | ~v7_waybel_0(B_529) | ~v4_orders_2(B_529) | v2_struct_0(B_529))), inference(negUnitSimplification, [status(thm)], [c_68, c_1787])).
% 5.98/2.12  tff(c_1438, plain, (![C_449, A_450, B_451]: (r2_hidden(C_449, k10_yellow_6(A_450, '#skF_3'(A_450, B_451, C_449))) | ~r3_waybel_9(A_450, B_451, C_449) | ~m1_subset_1(C_449, u1_struct_0(A_450)) | ~l1_waybel_0(B_451, A_450) | ~v7_waybel_0(B_451) | ~v4_orders_2(B_451) | v2_struct_0(B_451) | ~l1_pre_topc(A_450) | ~v2_pre_topc(A_450) | v2_struct_0(A_450))), inference(cnfTransformation, [status(thm)], [f_220])).
% 5.98/2.12  tff(c_18, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.98/2.12  tff(c_1453, plain, (![A_450, B_451, C_449]: (~r1_tarski(k10_yellow_6(A_450, '#skF_3'(A_450, B_451, C_449)), C_449) | ~r3_waybel_9(A_450, B_451, C_449) | ~m1_subset_1(C_449, u1_struct_0(A_450)) | ~l1_waybel_0(B_451, A_450) | ~v7_waybel_0(B_451) | ~v4_orders_2(B_451) | v2_struct_0(B_451) | ~l1_pre_topc(A_450) | ~v2_pre_topc(A_450) | v2_struct_0(A_450))), inference(resolution, [status(thm)], [c_1438, c_18])).
% 5.98/2.12  tff(c_1807, plain, (![B_529]: (~r1_tarski(k1_xboole_0, '#skF_4'('#skF_6', B_529)) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_529)) | ~m1_subset_1('#skF_4'('#skF_6', B_529), u1_struct_0('#skF_6')) | ~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_529)) | ~l1_waybel_0(B_529, '#skF_6') | ~v7_waybel_0(B_529) | ~v4_orders_2(B_529) | v2_struct_0(B_529))), inference(superposition, [status(thm), theory('equality')], [c_1789, c_1453])).
% 5.98/2.12  tff(c_1839, plain, (![B_529]: (~m1_subset_1('#skF_4'('#skF_6', B_529), u1_struct_0('#skF_6')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_529)) | ~l1_waybel_0(B_529, '#skF_6') | ~v7_waybel_0(B_529) | ~v4_orders_2(B_529) | v2_struct_0(B_529))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1203, c_1200, c_1205, c_14, c_1807])).
% 5.98/2.12  tff(c_1860, plain, (![B_530]: (~m1_subset_1('#skF_4'('#skF_6', B_530), u1_struct_0('#skF_6')) | ~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_530)) | ~l1_waybel_0(B_530, '#skF_6') | ~v7_waybel_0(B_530) | ~v4_orders_2(B_530) | v2_struct_0(B_530))), inference(negUnitSimplification, [status(thm)], [c_68, c_1197, c_1839])).
% 5.98/2.12  tff(c_1864, plain, (![B_89]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_1860])).
% 5.98/2.12  tff(c_1867, plain, (![B_89]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_89)) | ~l1_waybel_0(B_89, '#skF_6') | ~v7_waybel_0(B_89) | ~v4_orders_2(B_89) | v2_struct_0(B_89) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1198, c_1864])).
% 5.98/2.12  tff(c_1869, plain, (![B_531]: (~r3_waybel_9('#skF_6', '#skF_7', '#skF_4'('#skF_6', B_531)) | ~l1_waybel_0(B_531, '#skF_6') | ~v7_waybel_0(B_531) | ~v4_orders_2(B_531) | v2_struct_0(B_531))), inference(negUnitSimplification, [status(thm)], [c_68, c_1867])).
% 5.98/2.12  tff(c_1873, plain, (~l1_waybel_0('#skF_7', '#skF_6') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~v1_compts_1('#skF_6') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_60, c_1869])).
% 5.98/2.12  tff(c_1876, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1198, c_1203, c_1200, c_1205, c_1873])).
% 5.98/2.12  tff(c_1878, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1197, c_1876])).
% 5.98/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.98/2.12  
% 5.98/2.12  Inference rules
% 5.98/2.12  ----------------------
% 5.98/2.12  #Ref     : 0
% 5.98/2.12  #Sup     : 322
% 5.98/2.12  #Fact    : 0
% 5.98/2.12  #Define  : 0
% 5.98/2.12  #Split   : 21
% 5.98/2.12  #Chain   : 0
% 5.98/2.12  #Close   : 0
% 5.98/2.12  
% 5.98/2.12  Ordering : KBO
% 6.03/2.12  
% 6.03/2.12  Simplification rules
% 6.03/2.12  ----------------------
% 6.03/2.12  #Subsume      : 128
% 6.03/2.12  #Demod        : 332
% 6.03/2.12  #Tautology    : 77
% 6.03/2.12  #SimpNegUnit  : 84
% 6.03/2.12  #BackRed      : 1
% 6.03/2.12  
% 6.03/2.12  #Partial instantiations: 0
% 6.03/2.12  #Strategies tried      : 1
% 6.03/2.12  
% 6.03/2.12  Timing (in seconds)
% 6.03/2.12  ----------------------
% 6.03/2.13  Preprocessing        : 0.39
% 6.03/2.13  Parsing              : 0.21
% 6.03/2.13  CNF conversion       : 0.03
% 6.03/2.13  Main loop            : 0.84
% 6.03/2.13  Inferencing          : 0.34
% 6.03/2.13  Reduction            : 0.22
% 6.03/2.13  Demodulation         : 0.14
% 6.03/2.13  BG Simplification    : 0.04
% 6.03/2.13  Subsumption          : 0.20
% 6.03/2.13  Abstraction          : 0.03
% 6.03/2.13  MUC search           : 0.00
% 6.03/2.13  Cooper               : 0.00
% 6.03/2.13  Total                : 1.32
% 6.03/2.13  Index Insertion      : 0.00
% 6.03/2.13  Index Deletion       : 0.00
% 6.03/2.13  Index Matching       : 0.00
% 6.03/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
