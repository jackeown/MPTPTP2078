%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:41 EST 2020

% Result     : Theorem 5.89s
% Output     : CNFRefutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :  253 (3378 expanded)
%              Number of leaves         :   48 (1119 expanded)
%              Depth                    :   37
%              Number of atoms          : 1313 (24283 expanded)
%              Number of equality atoms :   61 ( 992 expanded)
%              Maximal formula depth    :   22 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_waybel_9 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k6_yellow_6 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r3_waybel_9,type,(
    r3_waybel_9: ( $i * $i * $i ) > $o )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff(k6_yellow_6,type,(
    k6_yellow_6: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_299,negated_conjecture,(
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

tff(f_274,axiom,(
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

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_76,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_94,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_166,axiom,(
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

tff(f_193,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_120,axiom,(
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

tff(f_142,axiom,(
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

tff(f_246,axiom,(
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

tff(f_222,axiom,(
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

tff(c_78,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_88,plain,
    ( ~ v2_struct_0('#skF_9')
    | ~ v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_116,plain,(
    ~ v1_compts_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_76,plain,(
    v2_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_74,plain,(
    l1_pre_topc('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_66,plain,(
    ! [A_144] :
      ( v4_orders_2('#skF_7'(A_144))
      | v1_compts_1(A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_114,plain,(
    ! [B_163] :
      ( v1_compts_1('#skF_8')
      | m2_yellow_6('#skF_10'(B_163),'#skF_8',B_163)
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_142,plain,(
    ! [B_163] :
      ( m2_yellow_6('#skF_10'(B_163),'#skF_8',B_163)
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_114])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_9,B_53,C_75] :
      ( m1_subset_1('#skF_2'(A_9,B_53,C_75),u1_struct_0(A_9))
      | k10_yellow_6(A_9,B_53) = C_75
      | ~ m1_subset_1(C_75,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_waybel_0(B_53,A_9)
      | ~ v7_waybel_0(B_53)
      | ~ v4_orders_2(B_53)
      | v2_struct_0(B_53)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1(k10_yellow_6(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_waybel_0(B_94,A_93)
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_321,plain,(
    ! [A_267,B_268,D_269] :
      ( m1_connsp_2('#skF_1'(A_267,B_268,k10_yellow_6(A_267,B_268),D_269),A_267,D_269)
      | r2_hidden(D_269,k10_yellow_6(A_267,B_268))
      | ~ m1_subset_1(D_269,u1_struct_0(A_267))
      | ~ m1_subset_1(k10_yellow_6(A_267,B_268),k1_zfmisc_1(u1_struct_0(A_267)))
      | ~ l1_waybel_0(B_268,A_267)
      | ~ v7_waybel_0(B_268)
      | ~ v4_orders_2(B_268)
      | v2_struct_0(B_268)
      | ~ l1_pre_topc(A_267)
      | ~ v2_pre_topc(A_267)
      | v2_struct_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_324,plain,(
    ! [A_93,B_94,D_269] :
      ( m1_connsp_2('#skF_1'(A_93,B_94,k10_yellow_6(A_93,B_94),D_269),A_93,D_269)
      | r2_hidden(D_269,k10_yellow_6(A_93,B_94))
      | ~ m1_subset_1(D_269,u1_struct_0(A_93))
      | ~ l1_waybel_0(B_94,A_93)
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_32,c_321])).

tff(c_329,plain,(
    ! [A_273,B_274,C_275,E_276] :
      ( r2_hidden('#skF_2'(A_273,B_274,C_275),C_275)
      | r1_waybel_0(A_273,B_274,E_276)
      | ~ m1_connsp_2(E_276,A_273,'#skF_2'(A_273,B_274,C_275))
      | k10_yellow_6(A_273,B_274) = C_275
      | ~ m1_subset_1(C_275,k1_zfmisc_1(u1_struct_0(A_273)))
      | ~ l1_waybel_0(B_274,A_273)
      | ~ v7_waybel_0(B_274)
      | ~ v4_orders_2(B_274)
      | v2_struct_0(B_274)
      | ~ l1_pre_topc(A_273)
      | ~ v2_pre_topc(A_273)
      | v2_struct_0(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_460,plain,(
    ! [A_383,B_384,C_385,B_386] :
      ( r2_hidden('#skF_2'(A_383,B_384,C_385),C_385)
      | r1_waybel_0(A_383,B_384,'#skF_1'(A_383,B_386,k10_yellow_6(A_383,B_386),'#skF_2'(A_383,B_384,C_385)))
      | k10_yellow_6(A_383,B_384) = C_385
      | ~ m1_subset_1(C_385,k1_zfmisc_1(u1_struct_0(A_383)))
      | ~ l1_waybel_0(B_384,A_383)
      | ~ v7_waybel_0(B_384)
      | ~ v4_orders_2(B_384)
      | v2_struct_0(B_384)
      | r2_hidden('#skF_2'(A_383,B_384,C_385),k10_yellow_6(A_383,B_386))
      | ~ m1_subset_1('#skF_2'(A_383,B_384,C_385),u1_struct_0(A_383))
      | ~ l1_waybel_0(B_386,A_383)
      | ~ v7_waybel_0(B_386)
      | ~ v4_orders_2(B_386)
      | v2_struct_0(B_386)
      | ~ l1_pre_topc(A_383)
      | ~ v2_pre_topc(A_383)
      | v2_struct_0(A_383) ) ),
    inference(resolution,[status(thm)],[c_324,c_329])).

tff(c_28,plain,(
    ! [A_9,B_53,D_86] :
      ( ~ r1_waybel_0(A_9,B_53,'#skF_1'(A_9,B_53,k10_yellow_6(A_9,B_53),D_86))
      | r2_hidden(D_86,k10_yellow_6(A_9,B_53))
      | ~ m1_subset_1(D_86,u1_struct_0(A_9))
      | ~ m1_subset_1(k10_yellow_6(A_9,B_53),k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_waybel_0(B_53,A_9)
      | ~ v7_waybel_0(B_53)
      | ~ v4_orders_2(B_53)
      | v2_struct_0(B_53)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_484,plain,(
    ! [A_387,B_388,C_389] :
      ( ~ m1_subset_1(k10_yellow_6(A_387,B_388),k1_zfmisc_1(u1_struct_0(A_387)))
      | r2_hidden('#skF_2'(A_387,B_388,C_389),C_389)
      | k10_yellow_6(A_387,B_388) = C_389
      | ~ m1_subset_1(C_389,k1_zfmisc_1(u1_struct_0(A_387)))
      | r2_hidden('#skF_2'(A_387,B_388,C_389),k10_yellow_6(A_387,B_388))
      | ~ m1_subset_1('#skF_2'(A_387,B_388,C_389),u1_struct_0(A_387))
      | ~ l1_waybel_0(B_388,A_387)
      | ~ v7_waybel_0(B_388)
      | ~ v4_orders_2(B_388)
      | v2_struct_0(B_388)
      | ~ l1_pre_topc(A_387)
      | ~ v2_pre_topc(A_387)
      | v2_struct_0(A_387) ) ),
    inference(resolution,[status(thm)],[c_460,c_28])).

tff(c_504,plain,(
    ! [A_390,B_391,C_392] :
      ( r2_hidden('#skF_2'(A_390,B_391,C_392),C_392)
      | k10_yellow_6(A_390,B_391) = C_392
      | ~ m1_subset_1(C_392,k1_zfmisc_1(u1_struct_0(A_390)))
      | r2_hidden('#skF_2'(A_390,B_391,C_392),k10_yellow_6(A_390,B_391))
      | ~ m1_subset_1('#skF_2'(A_390,B_391,C_392),u1_struct_0(A_390))
      | ~ l1_waybel_0(B_391,A_390)
      | ~ v7_waybel_0(B_391)
      | ~ v4_orders_2(B_391)
      | v2_struct_0(B_391)
      | ~ l1_pre_topc(A_390)
      | ~ v2_pre_topc(A_390)
      | v2_struct_0(A_390) ) ),
    inference(resolution,[status(thm)],[c_32,c_484])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_731,plain,(
    ! [C_423,A_424,B_425] :
      ( ~ r1_tarski(C_423,'#skF_2'(A_424,B_425,C_423))
      | k10_yellow_6(A_424,B_425) = C_423
      | ~ m1_subset_1(C_423,k1_zfmisc_1(u1_struct_0(A_424)))
      | r2_hidden('#skF_2'(A_424,B_425,C_423),k10_yellow_6(A_424,B_425))
      | ~ m1_subset_1('#skF_2'(A_424,B_425,C_423),u1_struct_0(A_424))
      | ~ l1_waybel_0(B_425,A_424)
      | ~ v7_waybel_0(B_425)
      | ~ v4_orders_2(B_425)
      | v2_struct_0(B_425)
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(resolution,[status(thm)],[c_504,c_8])).

tff(c_734,plain,(
    ! [A_424,B_425] :
      ( k10_yellow_6(A_424,B_425) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_424)))
      | r2_hidden('#skF_2'(A_424,B_425,k1_xboole_0),k10_yellow_6(A_424,B_425))
      | ~ m1_subset_1('#skF_2'(A_424,B_425,k1_xboole_0),u1_struct_0(A_424))
      | ~ l1_waybel_0(B_425,A_424)
      | ~ v7_waybel_0(B_425)
      | ~ v4_orders_2(B_425)
      | v2_struct_0(B_425)
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(resolution,[status(thm)],[c_2,c_731])).

tff(c_741,plain,(
    ! [A_429,B_430] :
      ( k10_yellow_6(A_429,B_430) = k1_xboole_0
      | r2_hidden('#skF_2'(A_429,B_430,k1_xboole_0),k10_yellow_6(A_429,B_430))
      | ~ m1_subset_1('#skF_2'(A_429,B_430,k1_xboole_0),u1_struct_0(A_429))
      | ~ l1_waybel_0(B_430,A_429)
      | ~ v7_waybel_0(B_430)
      | ~ v4_orders_2(B_430)
      | v2_struct_0(B_430)
      | ~ l1_pre_topc(A_429)
      | ~ v2_pre_topc(A_429)
      | v2_struct_0(A_429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_734])).

tff(c_46,plain,(
    ! [A_102,B_106,C_108] :
      ( r3_waybel_9(A_102,B_106,C_108)
      | ~ r2_hidden(C_108,k10_yellow_6(A_102,B_106))
      | ~ m1_subset_1(C_108,u1_struct_0(A_102))
      | ~ l1_waybel_0(B_106,A_102)
      | ~ v7_waybel_0(B_106)
      | ~ v4_orders_2(B_106)
      | v2_struct_0(B_106)
      | ~ l1_pre_topc(A_102)
      | ~ v2_pre_topc(A_102)
      | v2_struct_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_762,plain,(
    ! [A_431,B_432] :
      ( r3_waybel_9(A_431,B_432,'#skF_2'(A_431,B_432,k1_xboole_0))
      | k10_yellow_6(A_431,B_432) = k1_xboole_0
      | ~ m1_subset_1('#skF_2'(A_431,B_432,k1_xboole_0),u1_struct_0(A_431))
      | ~ l1_waybel_0(B_432,A_431)
      | ~ v7_waybel_0(B_432)
      | ~ v4_orders_2(B_432)
      | v2_struct_0(B_432)
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431) ) ),
    inference(resolution,[status(thm)],[c_741,c_46])).

tff(c_765,plain,(
    ! [A_9,B_53] :
      ( r3_waybel_9(A_9,B_53,'#skF_2'(A_9,B_53,k1_xboole_0))
      | k10_yellow_6(A_9,B_53) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_waybel_0(B_53,A_9)
      | ~ v7_waybel_0(B_53)
      | ~ v4_orders_2(B_53)
      | v2_struct_0(B_53)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_762])).

tff(c_769,plain,(
    ! [A_433,B_434] :
      ( r3_waybel_9(A_433,B_434,'#skF_2'(A_433,B_434,k1_xboole_0))
      | k10_yellow_6(A_433,B_434) = k1_xboole_0
      | ~ l1_waybel_0(B_434,A_433)
      | ~ v7_waybel_0(B_434)
      | ~ v4_orders_2(B_434)
      | v2_struct_0(B_434)
      | ~ l1_pre_topc(A_433)
      | ~ v2_pre_topc(A_433)
      | v2_struct_0(A_433) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_765])).

tff(c_48,plain,(
    ! [A_109,B_117,D_123,C_121] :
      ( r3_waybel_9(A_109,B_117,D_123)
      | ~ r3_waybel_9(A_109,C_121,D_123)
      | ~ m1_subset_1(D_123,u1_struct_0(A_109))
      | ~ m2_yellow_6(C_121,A_109,B_117)
      | ~ l1_waybel_0(B_117,A_109)
      | ~ v7_waybel_0(B_117)
      | ~ v4_orders_2(B_117)
      | v2_struct_0(B_117)
      | ~ l1_pre_topc(A_109)
      | ~ v2_pre_topc(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_823,plain,(
    ! [A_448,B_449,B_450] :
      ( r3_waybel_9(A_448,B_449,'#skF_2'(A_448,B_450,k1_xboole_0))
      | ~ m1_subset_1('#skF_2'(A_448,B_450,k1_xboole_0),u1_struct_0(A_448))
      | ~ m2_yellow_6(B_450,A_448,B_449)
      | ~ l1_waybel_0(B_449,A_448)
      | ~ v7_waybel_0(B_449)
      | ~ v4_orders_2(B_449)
      | v2_struct_0(B_449)
      | k10_yellow_6(A_448,B_450) = k1_xboole_0
      | ~ l1_waybel_0(B_450,A_448)
      | ~ v7_waybel_0(B_450)
      | ~ v4_orders_2(B_450)
      | v2_struct_0(B_450)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448)
      | v2_struct_0(A_448) ) ),
    inference(resolution,[status(thm)],[c_769,c_48])).

tff(c_826,plain,(
    ! [A_9,B_449,B_53] :
      ( r3_waybel_9(A_9,B_449,'#skF_2'(A_9,B_53,k1_xboole_0))
      | ~ m2_yellow_6(B_53,A_9,B_449)
      | ~ l1_waybel_0(B_449,A_9)
      | ~ v7_waybel_0(B_449)
      | ~ v4_orders_2(B_449)
      | v2_struct_0(B_449)
      | k10_yellow_6(A_9,B_53) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_waybel_0(B_53,A_9)
      | ~ v7_waybel_0(B_53)
      | ~ v4_orders_2(B_53)
      | v2_struct_0(B_53)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_823])).

tff(c_830,plain,(
    ! [A_451,B_452,B_453] :
      ( r3_waybel_9(A_451,B_452,'#skF_2'(A_451,B_453,k1_xboole_0))
      | ~ m2_yellow_6(B_453,A_451,B_452)
      | ~ l1_waybel_0(B_452,A_451)
      | ~ v7_waybel_0(B_452)
      | ~ v4_orders_2(B_452)
      | v2_struct_0(B_452)
      | k10_yellow_6(A_451,B_453) = k1_xboole_0
      | ~ l1_waybel_0(B_453,A_451)
      | ~ v7_waybel_0(B_453)
      | ~ v4_orders_2(B_453)
      | v2_struct_0(B_453)
      | ~ l1_pre_topc(A_451)
      | ~ v2_pre_topc(A_451)
      | v2_struct_0(A_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_826])).

tff(c_58,plain,(
    ! [A_144,C_154] :
      ( ~ r3_waybel_9(A_144,'#skF_7'(A_144),C_154)
      | ~ m1_subset_1(C_154,u1_struct_0(A_144))
      | v1_compts_1(A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_839,plain,(
    ! [A_454,B_455] :
      ( ~ m1_subset_1('#skF_2'(A_454,B_455,k1_xboole_0),u1_struct_0(A_454))
      | v1_compts_1(A_454)
      | ~ m2_yellow_6(B_455,A_454,'#skF_7'(A_454))
      | ~ l1_waybel_0('#skF_7'(A_454),A_454)
      | ~ v7_waybel_0('#skF_7'(A_454))
      | ~ v4_orders_2('#skF_7'(A_454))
      | v2_struct_0('#skF_7'(A_454))
      | k10_yellow_6(A_454,B_455) = k1_xboole_0
      | ~ l1_waybel_0(B_455,A_454)
      | ~ v7_waybel_0(B_455)
      | ~ v4_orders_2(B_455)
      | v2_struct_0(B_455)
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454) ) ),
    inference(resolution,[status(thm)],[c_830,c_58])).

tff(c_843,plain,(
    ! [A_9,B_53] :
      ( v1_compts_1(A_9)
      | ~ m2_yellow_6(B_53,A_9,'#skF_7'(A_9))
      | ~ l1_waybel_0('#skF_7'(A_9),A_9)
      | ~ v7_waybel_0('#skF_7'(A_9))
      | ~ v4_orders_2('#skF_7'(A_9))
      | v2_struct_0('#skF_7'(A_9))
      | k10_yellow_6(A_9,B_53) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_waybel_0(B_53,A_9)
      | ~ v7_waybel_0(B_53)
      | ~ v4_orders_2(B_53)
      | v2_struct_0(B_53)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_839])).

tff(c_847,plain,(
    ! [A_456,B_457] :
      ( v1_compts_1(A_456)
      | ~ m2_yellow_6(B_457,A_456,'#skF_7'(A_456))
      | ~ l1_waybel_0('#skF_7'(A_456),A_456)
      | ~ v7_waybel_0('#skF_7'(A_456))
      | ~ v4_orders_2('#skF_7'(A_456))
      | v2_struct_0('#skF_7'(A_456))
      | k10_yellow_6(A_456,B_457) = k1_xboole_0
      | ~ l1_waybel_0(B_457,A_456)
      | ~ v7_waybel_0(B_457)
      | ~ v4_orders_2(B_457)
      | v2_struct_0(B_457)
      | ~ l1_pre_topc(A_456)
      | ~ v2_pre_topc(A_456)
      | v2_struct_0(A_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_843])).

tff(c_855,plain,
    ( v1_compts_1('#skF_8')
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_10'('#skF_7'('#skF_8')),'#skF_8')
    | ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_142,c_847])).

tff(c_859,plain,
    ( v1_compts_1('#skF_8')
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_10'('#skF_7'('#skF_8')),'#skF_8')
    | ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_8')
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_855])).

tff(c_860,plain,
    ( k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_10'('#skF_7'('#skF_8')),'#skF_8')
    | ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_859])).

tff(c_861,plain,(
    ~ v4_orders_2('#skF_7'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_860])).

tff(c_871,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_861])).

tff(c_874,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_871])).

tff(c_876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_874])).

tff(c_878,plain,(
    v4_orders_2('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_860])).

tff(c_64,plain,(
    ! [A_144] :
      ( v7_waybel_0('#skF_7'(A_144))
      | v1_compts_1(A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_62,plain,(
    ! [A_144] :
      ( l1_waybel_0('#skF_7'(A_144),A_144)
      | v1_compts_1(A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_145,plain,(
    ! [C_185,A_186,B_187] :
      ( v7_waybel_0(C_185)
      | ~ m2_yellow_6(C_185,A_186,B_187)
      | ~ l1_waybel_0(B_187,A_186)
      | ~ v7_waybel_0(B_187)
      | ~ v4_orders_2(B_187)
      | v2_struct_0(B_187)
      | ~ l1_struct_0(A_186)
      | v2_struct_0(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_148,plain,(
    ! [B_163] :
      ( v7_waybel_0('#skF_10'(B_163))
      | ~ l1_struct_0('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(resolution,[status(thm)],[c_142,c_145])).

tff(c_151,plain,(
    ! [B_163] :
      ( v7_waybel_0('#skF_10'(B_163))
      | ~ l1_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_148])).

tff(c_152,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_155,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_152])).

tff(c_159,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_155])).

tff(c_161,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_181,plain,(
    ! [C_197,A_198,B_199] :
      ( l1_waybel_0(C_197,A_198)
      | ~ m2_yellow_6(C_197,A_198,B_199)
      | ~ l1_waybel_0(B_199,A_198)
      | ~ v7_waybel_0(B_199)
      | ~ v4_orders_2(B_199)
      | v2_struct_0(B_199)
      | ~ l1_struct_0(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_184,plain,(
    ! [B_163] :
      ( l1_waybel_0('#skF_10'(B_163),'#skF_8')
      | ~ l1_struct_0('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(resolution,[status(thm)],[c_142,c_181])).

tff(c_187,plain,(
    ! [B_163] :
      ( l1_waybel_0('#skF_10'(B_163),'#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_184])).

tff(c_188,plain,(
    ! [B_163] :
      ( l1_waybel_0('#skF_10'(B_163),'#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_187])).

tff(c_877,plain,
    ( ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ l1_waybel_0('#skF_10'('#skF_7'('#skF_8')),'#skF_8')
    | v2_struct_0('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_860])).

tff(c_879,plain,(
    ~ l1_waybel_0('#skF_10'('#skF_7'('#skF_8')),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_877])).

tff(c_882,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_188,c_879])).

tff(c_885,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_882])).

tff(c_886,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_885])).

tff(c_889,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_886])).

tff(c_892,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_889])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_892])).

tff(c_895,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_885])).

tff(c_897,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_895])).

tff(c_900,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_897])).

tff(c_903,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_900])).

tff(c_905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_903])).

tff(c_906,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_895])).

tff(c_68,plain,(
    ! [A_144] :
      ( ~ v2_struct_0('#skF_7'(A_144))
      | v1_compts_1(A_144)
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_274])).

tff(c_917,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_906,c_68])).

tff(c_920,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_917])).

tff(c_922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_920])).

tff(c_923,plain,
    ( ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_877])).

tff(c_925,plain,(
    ~ v7_waybel_0('#skF_7'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_923])).

tff(c_928,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_925])).

tff(c_931,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_928])).

tff(c_933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_931])).

tff(c_935,plain,(
    v7_waybel_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_160,plain,(
    ! [B_163] :
      ( v7_waybel_0('#skF_10'(B_163))
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_934,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_936,plain,(
    ~ v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_934])).

tff(c_939,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_160,c_936])).

tff(c_942,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_935,c_939])).

tff(c_943,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_942])).

tff(c_946,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_943])).

tff(c_949,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_946])).

tff(c_951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_949])).

tff(c_952,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_942])).

tff(c_963,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_952,c_68])).

tff(c_966,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_963])).

tff(c_968,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_966])).

tff(c_969,plain,
    ( ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_934])).

tff(c_971,plain,(
    ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_969])).

tff(c_974,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_971])).

tff(c_977,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_974])).

tff(c_979,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_977])).

tff(c_981,plain,(
    l1_waybel_0('#skF_7'('#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_172,plain,(
    ! [C_193,A_194,B_195] :
      ( v4_orders_2(C_193)
      | ~ m2_yellow_6(C_193,A_194,B_195)
      | ~ l1_waybel_0(B_195,A_194)
      | ~ v7_waybel_0(B_195)
      | ~ v4_orders_2(B_195)
      | v2_struct_0(B_195)
      | ~ l1_struct_0(A_194)
      | v2_struct_0(A_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_175,plain,(
    ! [B_163] :
      ( v4_orders_2('#skF_10'(B_163))
      | ~ l1_struct_0('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(resolution,[status(thm)],[c_142,c_172])).

tff(c_178,plain,(
    ! [B_163] :
      ( v4_orders_2('#skF_10'(B_163))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_175])).

tff(c_179,plain,(
    ! [B_163] :
      ( v4_orders_2('#skF_10'(B_163))
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_178])).

tff(c_980,plain,
    ( ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_969])).

tff(c_982,plain,(
    ~ v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_980])).

tff(c_985,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_179,c_982])).

tff(c_988,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_935,c_981,c_985])).

tff(c_991,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_988,c_68])).

tff(c_994,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_991])).

tff(c_996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_994])).

tff(c_997,plain,
    ( k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0
    | v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_980])).

tff(c_1006,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_997])).

tff(c_1009,plain,
    ( v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_1006,c_68])).

tff(c_1012,plain,
    ( v1_compts_1('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1009])).

tff(c_1014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116,c_1012])).

tff(c_1016,plain,(
    ~ v2_struct_0('#skF_7'('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_997])).

tff(c_1015,plain,
    ( v2_struct_0('#skF_10'('#skF_7'('#skF_8')))
    | k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_997])).

tff(c_1017,plain,(
    k10_yellow_6('#skF_8','#skF_10'('#skF_7'('#skF_8'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1015])).

tff(c_102,plain,(
    ! [B_163] :
      ( v1_compts_1('#skF_8')
      | v3_yellow_6('#skF_10'(B_163),'#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_138,plain,(
    ! [B_163] :
      ( v3_yellow_6('#skF_10'(B_163),'#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_102])).

tff(c_195,plain,(
    ! [A_205,B_206] :
      ( k10_yellow_6(A_205,B_206) != k1_xboole_0
      | ~ v3_yellow_6(B_206,A_205)
      | ~ l1_waybel_0(B_206,A_205)
      | ~ v7_waybel_0(B_206)
      | ~ v4_orders_2(B_206)
      | v2_struct_0(B_206)
      | ~ l1_pre_topc(A_205)
      | ~ v2_pre_topc(A_205)
      | v2_struct_0(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_201,plain,(
    ! [B_163] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_163)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_10'(B_163),'#skF_8')
      | ~ v7_waybel_0('#skF_10'(B_163))
      | ~ v4_orders_2('#skF_10'(B_163))
      | v2_struct_0('#skF_10'(B_163))
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(resolution,[status(thm)],[c_138,c_195])).

tff(c_205,plain,(
    ! [B_163] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_163)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_10'(B_163),'#skF_8')
      | ~ v7_waybel_0('#skF_10'(B_163))
      | ~ v4_orders_2('#skF_10'(B_163))
      | v2_struct_0('#skF_10'(B_163))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_201])).

tff(c_222,plain,(
    ! [B_218] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_218)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_10'(B_218),'#skF_8')
      | ~ v7_waybel_0('#skF_10'(B_218))
      | ~ v4_orders_2('#skF_10'(B_218))
      | v2_struct_0('#skF_10'(B_218))
      | ~ l1_waybel_0(B_218,'#skF_8')
      | ~ v7_waybel_0(B_218)
      | ~ v4_orders_2(B_218)
      | v2_struct_0(B_218) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_205])).

tff(c_227,plain,(
    ! [B_219] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_219)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_10'(B_219))
      | ~ v4_orders_2('#skF_10'(B_219))
      | v2_struct_0('#skF_10'(B_219))
      | ~ l1_waybel_0(B_219,'#skF_8')
      | ~ v7_waybel_0(B_219)
      | ~ v4_orders_2(B_219)
      | v2_struct_0(B_219) ) ),
    inference(resolution,[status(thm)],[c_188,c_222])).

tff(c_232,plain,(
    ! [B_220] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_220)) != k1_xboole_0
      | ~ v4_orders_2('#skF_10'(B_220))
      | v2_struct_0('#skF_10'(B_220))
      | ~ l1_waybel_0(B_220,'#skF_8')
      | ~ v7_waybel_0(B_220)
      | ~ v4_orders_2(B_220)
      | v2_struct_0(B_220) ) ),
    inference(resolution,[status(thm)],[c_160,c_227])).

tff(c_237,plain,(
    ! [B_221] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_221)) != k1_xboole_0
      | v2_struct_0('#skF_10'(B_221))
      | ~ l1_waybel_0(B_221,'#skF_8')
      | ~ v7_waybel_0(B_221)
      | ~ v4_orders_2(B_221)
      | v2_struct_0(B_221) ) ),
    inference(resolution,[status(thm)],[c_179,c_232])).

tff(c_163,plain,(
    ! [C_189,A_190,B_191] :
      ( ~ v2_struct_0(C_189)
      | ~ m2_yellow_6(C_189,A_190,B_191)
      | ~ l1_waybel_0(B_191,A_190)
      | ~ v7_waybel_0(B_191)
      | ~ v4_orders_2(B_191)
      | v2_struct_0(B_191)
      | ~ l1_struct_0(A_190)
      | v2_struct_0(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_166,plain,(
    ! [B_163] :
      ( ~ v2_struct_0('#skF_10'(B_163))
      | ~ l1_struct_0('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(resolution,[status(thm)],[c_142,c_163])).

tff(c_169,plain,(
    ! [B_163] :
      ( ~ v2_struct_0('#skF_10'(B_163))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_166])).

tff(c_170,plain,(
    ! [B_163] :
      ( ~ v2_struct_0('#skF_10'(B_163))
      | ~ l1_waybel_0(B_163,'#skF_8')
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_169])).

tff(c_241,plain,(
    ! [B_221] :
      ( k10_yellow_6('#skF_8','#skF_10'(B_221)) != k1_xboole_0
      | ~ l1_waybel_0(B_221,'#skF_8')
      | ~ v7_waybel_0(B_221)
      | ~ v4_orders_2(B_221)
      | v2_struct_0(B_221) ) ),
    inference(resolution,[status(thm)],[c_237,c_170])).

tff(c_1062,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_241])).

tff(c_1118,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_935,c_981,c_1062])).

tff(c_1120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1016,c_1118])).

tff(c_1121,plain,(
    v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_1015])).

tff(c_1125,plain,
    ( ~ l1_waybel_0('#skF_7'('#skF_8'),'#skF_8')
    | ~ v7_waybel_0('#skF_7'('#skF_8'))
    | ~ v4_orders_2('#skF_7'('#skF_8'))
    | v2_struct_0('#skF_7'('#skF_8')) ),
    inference(resolution,[status(thm)],[c_1121,c_170])).

tff(c_1128,plain,(
    v2_struct_0('#skF_7'('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_935,c_981,c_1125])).

tff(c_1130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1016,c_1128])).

tff(c_1131,plain,(
    ~ v2_struct_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1132,plain,(
    v1_compts_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_86,plain,
    ( v4_orders_2('#skF_9')
    | ~ v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_1134,plain,(
    v4_orders_2('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_86])).

tff(c_84,plain,
    ( v7_waybel_0('#skF_9')
    | ~ v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_1137,plain,(
    v7_waybel_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_84])).

tff(c_82,plain,
    ( l1_waybel_0('#skF_9','#skF_8')
    | ~ v1_compts_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_1140,plain,(
    l1_waybel_0('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_82])).

tff(c_54,plain,(
    ! [A_138,B_142] :
      ( r3_waybel_9(A_138,B_142,'#skF_5'(A_138,B_142))
      | ~ l1_waybel_0(B_142,A_138)
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_56,plain,(
    ! [A_138,B_142] :
      ( m1_subset_1('#skF_5'(A_138,B_142),u1_struct_0(A_138))
      | ~ l1_waybel_0(B_142,A_138)
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_1199,plain,(
    ! [A_524,B_525,C_526] :
      ( m2_yellow_6('#skF_4'(A_524,B_525,C_526),A_524,B_525)
      | ~ r3_waybel_9(A_524,B_525,C_526)
      | ~ m1_subset_1(C_526,u1_struct_0(A_524))
      | ~ l1_waybel_0(B_525,A_524)
      | ~ v7_waybel_0(B_525)
      | ~ v4_orders_2(B_525)
      | v2_struct_0(B_525)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_34,plain,(
    ! [C_98,A_95,B_96] :
      ( l1_waybel_0(C_98,A_95)
      | ~ m2_yellow_6(C_98,A_95,B_96)
      | ~ l1_waybel_0(B_96,A_95)
      | ~ v7_waybel_0(B_96)
      | ~ v4_orders_2(B_96)
      | v2_struct_0(B_96)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1299,plain,(
    ! [A_548,B_549,C_550] :
      ( l1_waybel_0('#skF_4'(A_548,B_549,C_550),A_548)
      | ~ l1_struct_0(A_548)
      | ~ r3_waybel_9(A_548,B_549,C_550)
      | ~ m1_subset_1(C_550,u1_struct_0(A_548))
      | ~ l1_waybel_0(B_549,A_548)
      | ~ v7_waybel_0(B_549)
      | ~ v4_orders_2(B_549)
      | v2_struct_0(B_549)
      | ~ l1_pre_topc(A_548)
      | ~ v2_pre_topc(A_548)
      | v2_struct_0(A_548) ) ),
    inference(resolution,[status(thm)],[c_1199,c_34])).

tff(c_1351,plain,(
    ! [A_595,B_596,B_597] :
      ( l1_waybel_0('#skF_4'(A_595,B_596,'#skF_5'(A_595,B_597)),A_595)
      | ~ l1_struct_0(A_595)
      | ~ r3_waybel_9(A_595,B_596,'#skF_5'(A_595,B_597))
      | ~ l1_waybel_0(B_596,A_595)
      | ~ v7_waybel_0(B_596)
      | ~ v4_orders_2(B_596)
      | v2_struct_0(B_596)
      | ~ l1_waybel_0(B_597,A_595)
      | ~ v7_waybel_0(B_597)
      | ~ v4_orders_2(B_597)
      | v2_struct_0(B_597)
      | ~ v1_compts_1(A_595)
      | ~ l1_pre_topc(A_595)
      | ~ v2_pre_topc(A_595)
      | v2_struct_0(A_595) ) ),
    inference(resolution,[status(thm)],[c_56,c_1299])).

tff(c_42,plain,(
    ! [B_101,A_99] :
      ( v3_yellow_6(B_101,A_99)
      | k10_yellow_6(A_99,B_101) = k1_xboole_0
      | ~ l1_waybel_0(B_101,A_99)
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101)
      | ~ l1_pre_topc(A_99)
      | ~ v2_pre_topc(A_99)
      | v2_struct_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_80,plain,(
    ! [C_162] :
      ( ~ v3_yellow_6(C_162,'#skF_8')
      | ~ m2_yellow_6(C_162,'#skF_8','#skF_9')
      | ~ v1_compts_1('#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_299])).

tff(c_1142,plain,(
    ! [C_162] :
      ( ~ v3_yellow_6(C_162,'#skF_8')
      | ~ m2_yellow_6(C_162,'#skF_8','#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1132,c_80])).

tff(c_1215,plain,(
    ! [C_526] :
      ( ~ v3_yellow_6('#skF_4'('#skF_8','#skF_9',C_526),'#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9',C_526)
      | ~ m1_subset_1(C_526,u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1199,c_1142])).

tff(c_1222,plain,(
    ! [C_526] :
      ( ~ v3_yellow_6('#skF_4'('#skF_8','#skF_9',C_526),'#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9',C_526)
      | ~ m1_subset_1(C_526,u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1134,c_1137,c_1140,c_1215])).

tff(c_1224,plain,(
    ! [C_527] :
      ( ~ v3_yellow_6('#skF_4'('#skF_8','#skF_9',C_527),'#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9',C_527)
      | ~ m1_subset_1(C_527,u1_struct_0('#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1131,c_1222])).

tff(c_1227,plain,(
    ! [C_527] :
      ( ~ r3_waybel_9('#skF_8','#skF_9',C_527)
      | ~ m1_subset_1(C_527,u1_struct_0('#skF_8'))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9',C_527)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9',C_527),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9',C_527))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9',C_527))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9',C_527))
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_42,c_1224])).

tff(c_1230,plain,(
    ! [C_527] :
      ( ~ r3_waybel_9('#skF_8','#skF_9',C_527)
      | ~ m1_subset_1(C_527,u1_struct_0('#skF_8'))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9',C_527)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9',C_527),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9',C_527))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9',C_527))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9',C_527))
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1227])).

tff(c_1240,plain,(
    ! [C_534] :
      ( ~ r3_waybel_9('#skF_8','#skF_9',C_534)
      | ~ m1_subset_1(C_534,u1_struct_0('#skF_8'))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9',C_534)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9',C_534),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9',C_534))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9',C_534))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9',C_534)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1230])).

tff(c_1248,plain,(
    ! [B_142] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_1240])).

tff(c_1255,plain,(
    ! [B_142] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1132,c_1248])).

tff(c_1256,plain,(
    ! [B_142] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)),'#skF_8')
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1255])).

tff(c_1355,plain,(
    ! [B_597] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_597))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_597,'#skF_8')
      | ~ v7_waybel_0(B_597)
      | ~ v4_orders_2(B_597)
      | v2_struct_0(B_597)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1351,c_1256])).

tff(c_1358,plain,(
    ! [B_597] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_597))
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_597,'#skF_8')
      | ~ v7_waybel_0(B_597)
      | ~ v4_orders_2(B_597)
      | v2_struct_0(B_597)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1132,c_1134,c_1137,c_1140,c_1355])).

tff(c_1359,plain,(
    ! [B_597] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_597)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_597))
      | ~ l1_waybel_0(B_597,'#skF_8')
      | ~ v7_waybel_0(B_597)
      | ~ v4_orders_2(B_597)
      | v2_struct_0(B_597) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1131,c_1358])).

tff(c_1396,plain,(
    ~ l1_struct_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1359])).

tff(c_1400,plain,(
    ~ l1_pre_topc('#skF_8') ),
    inference(resolution,[status(thm)],[c_10,c_1396])).

tff(c_1404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1400])).

tff(c_1406,plain,(
    l1_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1359])).

tff(c_38,plain,(
    ! [C_98,A_95,B_96] :
      ( v4_orders_2(C_98)
      | ~ m2_yellow_6(C_98,A_95,B_96)
      | ~ l1_waybel_0(B_96,A_95)
      | ~ v7_waybel_0(B_96)
      | ~ v4_orders_2(B_96)
      | v2_struct_0(B_96)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1257,plain,(
    ! [A_535,B_536,C_537] :
      ( v4_orders_2('#skF_4'(A_535,B_536,C_537))
      | ~ l1_struct_0(A_535)
      | ~ r3_waybel_9(A_535,B_536,C_537)
      | ~ m1_subset_1(C_537,u1_struct_0(A_535))
      | ~ l1_waybel_0(B_536,A_535)
      | ~ v7_waybel_0(B_536)
      | ~ v4_orders_2(B_536)
      | v2_struct_0(B_536)
      | ~ l1_pre_topc(A_535)
      | ~ v2_pre_topc(A_535)
      | v2_struct_0(A_535) ) ),
    inference(resolution,[status(thm)],[c_1199,c_38])).

tff(c_1263,plain,(
    ! [A_138,B_536,B_142] :
      ( v4_orders_2('#skF_4'(A_138,B_536,'#skF_5'(A_138,B_142)))
      | ~ l1_struct_0(A_138)
      | ~ r3_waybel_9(A_138,B_536,'#skF_5'(A_138,B_142))
      | ~ l1_waybel_0(B_536,A_138)
      | ~ v7_waybel_0(B_536)
      | ~ v4_orders_2(B_536)
      | v2_struct_0(B_536)
      | ~ l1_waybel_0(B_142,A_138)
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_56,c_1257])).

tff(c_36,plain,(
    ! [C_98,A_95,B_96] :
      ( v7_waybel_0(C_98)
      | ~ m2_yellow_6(C_98,A_95,B_96)
      | ~ l1_waybel_0(B_96,A_95)
      | ~ v7_waybel_0(B_96)
      | ~ v4_orders_2(B_96)
      | v2_struct_0(B_96)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1233,plain,(
    ! [A_531,B_532,C_533] :
      ( v7_waybel_0('#skF_4'(A_531,B_532,C_533))
      | ~ l1_struct_0(A_531)
      | ~ r3_waybel_9(A_531,B_532,C_533)
      | ~ m1_subset_1(C_533,u1_struct_0(A_531))
      | ~ l1_waybel_0(B_532,A_531)
      | ~ v7_waybel_0(B_532)
      | ~ v4_orders_2(B_532)
      | v2_struct_0(B_532)
      | ~ l1_pre_topc(A_531)
      | ~ v2_pre_topc(A_531)
      | v2_struct_0(A_531) ) ),
    inference(resolution,[status(thm)],[c_1199,c_36])).

tff(c_1239,plain,(
    ! [A_138,B_532,B_142] :
      ( v7_waybel_0('#skF_4'(A_138,B_532,'#skF_5'(A_138,B_142)))
      | ~ l1_struct_0(A_138)
      | ~ r3_waybel_9(A_138,B_532,'#skF_5'(A_138,B_142))
      | ~ l1_waybel_0(B_532,A_138)
      | ~ v7_waybel_0(B_532)
      | ~ v4_orders_2(B_532)
      | v2_struct_0(B_532)
      | ~ l1_waybel_0(B_142,A_138)
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_56,c_1233])).

tff(c_1407,plain,(
    ! [B_620] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_620))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_620)))
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_620)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_620)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_620))
      | ~ l1_waybel_0(B_620,'#skF_8')
      | ~ v7_waybel_0(B_620)
      | ~ v4_orders_2(B_620)
      | v2_struct_0(B_620) ) ),
    inference(splitRight,[status(thm)],[c_1359])).

tff(c_1411,plain,(
    ! [B_142] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1239,c_1407])).

tff(c_1414,plain,(
    ! [B_142] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1132,c_1134,c_1137,c_1140,c_1406,c_1411])).

tff(c_1416,plain,(
    ! [B_621] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_621))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_621)))
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_621)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_621))
      | ~ l1_waybel_0(B_621,'#skF_8')
      | ~ v7_waybel_0(B_621)
      | ~ v4_orders_2(B_621)
      | v2_struct_0(B_621) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1131,c_1414])).

tff(c_1420,plain,(
    ! [B_142] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ l1_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1263,c_1416])).

tff(c_1423,plain,(
    ! [B_142] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | v2_struct_0('#skF_9')
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1132,c_1134,c_1137,c_1140,c_1406,c_1420])).

tff(c_1425,plain,(
    ! [B_622] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_622))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_622)))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_622))
      | ~ l1_waybel_0(B_622,'#skF_8')
      | ~ v7_waybel_0(B_622)
      | ~ v4_orders_2(B_622)
      | v2_struct_0(B_622) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1131,c_1423])).

tff(c_40,plain,(
    ! [C_98,A_95,B_96] :
      ( ~ v2_struct_0(C_98)
      | ~ m2_yellow_6(C_98,A_95,B_96)
      | ~ l1_waybel_0(B_96,A_95)
      | ~ v7_waybel_0(B_96)
      | ~ v4_orders_2(B_96)
      | v2_struct_0(B_96)
      | ~ l1_struct_0(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1217,plain,(
    ! [A_524,B_525,C_526] :
      ( ~ v2_struct_0('#skF_4'(A_524,B_525,C_526))
      | ~ l1_struct_0(A_524)
      | ~ r3_waybel_9(A_524,B_525,C_526)
      | ~ m1_subset_1(C_526,u1_struct_0(A_524))
      | ~ l1_waybel_0(B_525,A_524)
      | ~ v7_waybel_0(B_525)
      | ~ v4_orders_2(B_525)
      | v2_struct_0(B_525)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(resolution,[status(thm)],[c_1199,c_40])).

tff(c_1427,plain,(
    ! [B_622] :
      ( ~ l1_struct_0('#skF_8')
      | ~ m1_subset_1('#skF_5'('#skF_8',B_622),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_622))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_622))
      | ~ l1_waybel_0(B_622,'#skF_8')
      | ~ v7_waybel_0(B_622)
      | ~ v4_orders_2(B_622)
      | v2_struct_0(B_622) ) ),
    inference(resolution,[status(thm)],[c_1425,c_1217])).

tff(c_1430,plain,(
    ! [B_622] :
      ( ~ m1_subset_1('#skF_5'('#skF_8',B_622),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_622))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_622))
      | ~ l1_waybel_0(B_622,'#skF_8')
      | ~ v7_waybel_0(B_622)
      | ~ v4_orders_2(B_622)
      | v2_struct_0(B_622) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1134,c_1137,c_1140,c_1406,c_1427])).

tff(c_1437,plain,(
    ! [B_627] :
      ( ~ m1_subset_1('#skF_5'('#skF_8',B_627),u1_struct_0('#skF_8'))
      | k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_627))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_627))
      | ~ l1_waybel_0(B_627,'#skF_8')
      | ~ v7_waybel_0(B_627)
      | ~ v4_orders_2(B_627)
      | v2_struct_0(B_627) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1131,c_1430])).

tff(c_1441,plain,(
    ! [B_142] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_1437])).

tff(c_1444,plain,(
    ! [B_142] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1132,c_1441])).

tff(c_1446,plain,(
    ! [B_628] :
      ( k10_yellow_6('#skF_8','#skF_4'('#skF_8','#skF_9','#skF_5'('#skF_8',B_628))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_628))
      | ~ l1_waybel_0(B_628,'#skF_8')
      | ~ v7_waybel_0(B_628)
      | ~ v4_orders_2(B_628)
      | v2_struct_0(B_628) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1444])).

tff(c_1286,plain,(
    ! [C_545,A_546,B_547] :
      ( r2_hidden(C_545,k10_yellow_6(A_546,'#skF_4'(A_546,B_547,C_545)))
      | ~ r3_waybel_9(A_546,B_547,C_545)
      | ~ m1_subset_1(C_545,u1_struct_0(A_546))
      | ~ l1_waybel_0(B_547,A_546)
      | ~ v7_waybel_0(B_547)
      | ~ v4_orders_2(B_547)
      | v2_struct_0(B_547)
      | ~ l1_pre_topc(A_546)
      | ~ v2_pre_topc(A_546)
      | v2_struct_0(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_1298,plain,(
    ! [A_546,B_547,C_545] :
      ( ~ r1_tarski(k10_yellow_6(A_546,'#skF_4'(A_546,B_547,C_545)),C_545)
      | ~ r3_waybel_9(A_546,B_547,C_545)
      | ~ m1_subset_1(C_545,u1_struct_0(A_546))
      | ~ l1_waybel_0(B_547,A_546)
      | ~ v7_waybel_0(B_547)
      | ~ v4_orders_2(B_547)
      | v2_struct_0(B_547)
      | ~ l1_pre_topc(A_546)
      | ~ v2_pre_topc(A_546)
      | v2_struct_0(A_546) ) ),
    inference(resolution,[status(thm)],[c_1286,c_8])).

tff(c_1459,plain,(
    ! [B_628] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_5'('#skF_8',B_628))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_628))
      | ~ m1_subset_1('#skF_5'('#skF_8',B_628),u1_struct_0('#skF_8'))
      | ~ l1_waybel_0('#skF_9','#skF_8')
      | ~ v7_waybel_0('#skF_9')
      | ~ v4_orders_2('#skF_9')
      | v2_struct_0('#skF_9')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_628))
      | ~ l1_waybel_0(B_628,'#skF_8')
      | ~ v7_waybel_0(B_628)
      | ~ v4_orders_2(B_628)
      | v2_struct_0(B_628) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1446,c_1298])).

tff(c_1486,plain,(
    ! [B_628] :
      ( ~ m1_subset_1('#skF_5'('#skF_8',B_628),u1_struct_0('#skF_8'))
      | v2_struct_0('#skF_9')
      | v2_struct_0('#skF_8')
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_628))
      | ~ l1_waybel_0(B_628,'#skF_8')
      | ~ v7_waybel_0(B_628)
      | ~ v4_orders_2(B_628)
      | v2_struct_0(B_628) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1134,c_1137,c_1140,c_2,c_1459])).

tff(c_1501,plain,(
    ! [B_629] :
      ( ~ m1_subset_1('#skF_5'('#skF_8',B_629),u1_struct_0('#skF_8'))
      | ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_629))
      | ~ l1_waybel_0(B_629,'#skF_8')
      | ~ v7_waybel_0(B_629)
      | ~ v4_orders_2(B_629)
      | v2_struct_0(B_629) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1131,c_1486])).

tff(c_1505,plain,(
    ! [B_142] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ v1_compts_1('#skF_8')
      | ~ l1_pre_topc('#skF_8')
      | ~ v2_pre_topc('#skF_8')
      | v2_struct_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_56,c_1501])).

tff(c_1508,plain,(
    ! [B_142] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_142))
      | ~ l1_waybel_0(B_142,'#skF_8')
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | v2_struct_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1132,c_1505])).

tff(c_1510,plain,(
    ! [B_630] :
      ( ~ r3_waybel_9('#skF_8','#skF_9','#skF_5'('#skF_8',B_630))
      | ~ l1_waybel_0(B_630,'#skF_8')
      | ~ v7_waybel_0(B_630)
      | ~ v4_orders_2(B_630)
      | v2_struct_0(B_630) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1508])).

tff(c_1518,plain,
    ( ~ l1_waybel_0('#skF_9','#skF_8')
    | ~ v7_waybel_0('#skF_9')
    | ~ v4_orders_2('#skF_9')
    | v2_struct_0('#skF_9')
    | ~ v1_compts_1('#skF_8')
    | ~ l1_pre_topc('#skF_8')
    | ~ v2_pre_topc('#skF_8')
    | v2_struct_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_1510])).

tff(c_1525,plain,
    ( v2_struct_0('#skF_9')
    | v2_struct_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_1132,c_1134,c_1137,c_1140,c_1518])).

tff(c_1527,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1131,c_1525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.89/2.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.03  
% 5.89/2.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.89/2.03  %$ r3_waybel_9 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k6_yellow_6 > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_6 > #skF_4 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 5.89/2.03  
% 5.89/2.03  %Foreground sorts:
% 5.89/2.03  
% 5.89/2.03  
% 5.89/2.03  %Background operators:
% 5.89/2.03  
% 5.89/2.03  
% 5.89/2.03  %Foreground operators:
% 5.89/2.03  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.89/2.03  tff('#skF_7', type, '#skF_7': $i > $i).
% 5.89/2.03  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 5.89/2.03  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.89/2.03  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.89/2.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.89/2.03  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.89/2.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.89/2.03  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 5.89/2.03  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 5.89/2.03  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.89/2.03  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 5.89/2.03  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.89/2.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.89/2.03  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 5.89/2.03  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 5.89/2.03  tff('#skF_10', type, '#skF_10': $i > $i).
% 5.89/2.03  tff(k6_yellow_6, type, k6_yellow_6: $i > $i).
% 5.89/2.03  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.89/2.03  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.89/2.03  tff('#skF_9', type, '#skF_9': $i).
% 5.89/2.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.89/2.03  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.89/2.03  tff('#skF_8', type, '#skF_8': $i).
% 5.89/2.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.89/2.03  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 5.89/2.03  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.89/2.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.89/2.03  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.89/2.03  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.89/2.03  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.89/2.03  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 5.89/2.03  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.89/2.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.89/2.03  
% 6.28/2.08  tff(f_299, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_yellow19)).
% 6.28/2.08  tff(f_274, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => ~(r2_hidden(B, k6_yellow_6(A)) & (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~r3_waybel_9(A, B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_yellow19)).
% 6.28/2.08  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.28/2.08  tff(f_76, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_yellow_6)).
% 6.28/2.08  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.28/2.08  tff(f_94, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 6.28/2.08  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.28/2.08  tff(f_166, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_waybel_9)).
% 6.28/2.08  tff(f_193, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_waybel_9)).
% 6.28/2.08  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.28/2.08  tff(f_120, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 6.28/2.08  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_yellow_6)).
% 6.28/2.08  tff(f_246, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l37_yellow19)).
% 6.28/2.08  tff(f_222, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_waybel_9)).
% 6.28/2.08  tff(c_78, plain, (~v2_struct_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_88, plain, (~v2_struct_0('#skF_9') | ~v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_116, plain, (~v1_compts_1('#skF_8')), inference(splitLeft, [status(thm)], [c_88])).
% 6.28/2.08  tff(c_76, plain, (v2_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_74, plain, (l1_pre_topc('#skF_8')), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_66, plain, (![A_144]: (v4_orders_2('#skF_7'(A_144)) | v1_compts_1(A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_274])).
% 6.28/2.08  tff(c_114, plain, (![B_163]: (v1_compts_1('#skF_8') | m2_yellow_6('#skF_10'(B_163), '#skF_8', B_163) | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_142, plain, (![B_163]: (m2_yellow_6('#skF_10'(B_163), '#skF_8', B_163) | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(negUnitSimplification, [status(thm)], [c_116, c_114])).
% 6.28/2.08  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.28/2.08  tff(c_12, plain, (![A_9, B_53, C_75]: (m1_subset_1('#skF_2'(A_9, B_53, C_75), u1_struct_0(A_9)) | k10_yellow_6(A_9, B_53)=C_75 | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.28/2.08  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.28/2.08  tff(c_32, plain, (![A_93, B_94]: (m1_subset_1(k10_yellow_6(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.28/2.08  tff(c_321, plain, (![A_267, B_268, D_269]: (m1_connsp_2('#skF_1'(A_267, B_268, k10_yellow_6(A_267, B_268), D_269), A_267, D_269) | r2_hidden(D_269, k10_yellow_6(A_267, B_268)) | ~m1_subset_1(D_269, u1_struct_0(A_267)) | ~m1_subset_1(k10_yellow_6(A_267, B_268), k1_zfmisc_1(u1_struct_0(A_267))) | ~l1_waybel_0(B_268, A_267) | ~v7_waybel_0(B_268) | ~v4_orders_2(B_268) | v2_struct_0(B_268) | ~l1_pre_topc(A_267) | ~v2_pre_topc(A_267) | v2_struct_0(A_267))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.28/2.08  tff(c_324, plain, (![A_93, B_94, D_269]: (m1_connsp_2('#skF_1'(A_93, B_94, k10_yellow_6(A_93, B_94), D_269), A_93, D_269) | r2_hidden(D_269, k10_yellow_6(A_93, B_94)) | ~m1_subset_1(D_269, u1_struct_0(A_93)) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_32, c_321])).
% 6.28/2.08  tff(c_329, plain, (![A_273, B_274, C_275, E_276]: (r2_hidden('#skF_2'(A_273, B_274, C_275), C_275) | r1_waybel_0(A_273, B_274, E_276) | ~m1_connsp_2(E_276, A_273, '#skF_2'(A_273, B_274, C_275)) | k10_yellow_6(A_273, B_274)=C_275 | ~m1_subset_1(C_275, k1_zfmisc_1(u1_struct_0(A_273))) | ~l1_waybel_0(B_274, A_273) | ~v7_waybel_0(B_274) | ~v4_orders_2(B_274) | v2_struct_0(B_274) | ~l1_pre_topc(A_273) | ~v2_pre_topc(A_273) | v2_struct_0(A_273))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.28/2.08  tff(c_460, plain, (![A_383, B_384, C_385, B_386]: (r2_hidden('#skF_2'(A_383, B_384, C_385), C_385) | r1_waybel_0(A_383, B_384, '#skF_1'(A_383, B_386, k10_yellow_6(A_383, B_386), '#skF_2'(A_383, B_384, C_385))) | k10_yellow_6(A_383, B_384)=C_385 | ~m1_subset_1(C_385, k1_zfmisc_1(u1_struct_0(A_383))) | ~l1_waybel_0(B_384, A_383) | ~v7_waybel_0(B_384) | ~v4_orders_2(B_384) | v2_struct_0(B_384) | r2_hidden('#skF_2'(A_383, B_384, C_385), k10_yellow_6(A_383, B_386)) | ~m1_subset_1('#skF_2'(A_383, B_384, C_385), u1_struct_0(A_383)) | ~l1_waybel_0(B_386, A_383) | ~v7_waybel_0(B_386) | ~v4_orders_2(B_386) | v2_struct_0(B_386) | ~l1_pre_topc(A_383) | ~v2_pre_topc(A_383) | v2_struct_0(A_383))), inference(resolution, [status(thm)], [c_324, c_329])).
% 6.28/2.08  tff(c_28, plain, (![A_9, B_53, D_86]: (~r1_waybel_0(A_9, B_53, '#skF_1'(A_9, B_53, k10_yellow_6(A_9, B_53), D_86)) | r2_hidden(D_86, k10_yellow_6(A_9, B_53)) | ~m1_subset_1(D_86, u1_struct_0(A_9)) | ~m1_subset_1(k10_yellow_6(A_9, B_53), k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.28/2.08  tff(c_484, plain, (![A_387, B_388, C_389]: (~m1_subset_1(k10_yellow_6(A_387, B_388), k1_zfmisc_1(u1_struct_0(A_387))) | r2_hidden('#skF_2'(A_387, B_388, C_389), C_389) | k10_yellow_6(A_387, B_388)=C_389 | ~m1_subset_1(C_389, k1_zfmisc_1(u1_struct_0(A_387))) | r2_hidden('#skF_2'(A_387, B_388, C_389), k10_yellow_6(A_387, B_388)) | ~m1_subset_1('#skF_2'(A_387, B_388, C_389), u1_struct_0(A_387)) | ~l1_waybel_0(B_388, A_387) | ~v7_waybel_0(B_388) | ~v4_orders_2(B_388) | v2_struct_0(B_388) | ~l1_pre_topc(A_387) | ~v2_pre_topc(A_387) | v2_struct_0(A_387))), inference(resolution, [status(thm)], [c_460, c_28])).
% 6.28/2.08  tff(c_504, plain, (![A_390, B_391, C_392]: (r2_hidden('#skF_2'(A_390, B_391, C_392), C_392) | k10_yellow_6(A_390, B_391)=C_392 | ~m1_subset_1(C_392, k1_zfmisc_1(u1_struct_0(A_390))) | r2_hidden('#skF_2'(A_390, B_391, C_392), k10_yellow_6(A_390, B_391)) | ~m1_subset_1('#skF_2'(A_390, B_391, C_392), u1_struct_0(A_390)) | ~l1_waybel_0(B_391, A_390) | ~v7_waybel_0(B_391) | ~v4_orders_2(B_391) | v2_struct_0(B_391) | ~l1_pre_topc(A_390) | ~v2_pre_topc(A_390) | v2_struct_0(A_390))), inference(resolution, [status(thm)], [c_32, c_484])).
% 6.28/2.08  tff(c_8, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.28/2.08  tff(c_731, plain, (![C_423, A_424, B_425]: (~r1_tarski(C_423, '#skF_2'(A_424, B_425, C_423)) | k10_yellow_6(A_424, B_425)=C_423 | ~m1_subset_1(C_423, k1_zfmisc_1(u1_struct_0(A_424))) | r2_hidden('#skF_2'(A_424, B_425, C_423), k10_yellow_6(A_424, B_425)) | ~m1_subset_1('#skF_2'(A_424, B_425, C_423), u1_struct_0(A_424)) | ~l1_waybel_0(B_425, A_424) | ~v7_waybel_0(B_425) | ~v4_orders_2(B_425) | v2_struct_0(B_425) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424) | v2_struct_0(A_424))), inference(resolution, [status(thm)], [c_504, c_8])).
% 6.28/2.08  tff(c_734, plain, (![A_424, B_425]: (k10_yellow_6(A_424, B_425)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_424))) | r2_hidden('#skF_2'(A_424, B_425, k1_xboole_0), k10_yellow_6(A_424, B_425)) | ~m1_subset_1('#skF_2'(A_424, B_425, k1_xboole_0), u1_struct_0(A_424)) | ~l1_waybel_0(B_425, A_424) | ~v7_waybel_0(B_425) | ~v4_orders_2(B_425) | v2_struct_0(B_425) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424) | v2_struct_0(A_424))), inference(resolution, [status(thm)], [c_2, c_731])).
% 6.28/2.08  tff(c_741, plain, (![A_429, B_430]: (k10_yellow_6(A_429, B_430)=k1_xboole_0 | r2_hidden('#skF_2'(A_429, B_430, k1_xboole_0), k10_yellow_6(A_429, B_430)) | ~m1_subset_1('#skF_2'(A_429, B_430, k1_xboole_0), u1_struct_0(A_429)) | ~l1_waybel_0(B_430, A_429) | ~v7_waybel_0(B_430) | ~v4_orders_2(B_430) | v2_struct_0(B_430) | ~l1_pre_topc(A_429) | ~v2_pre_topc(A_429) | v2_struct_0(A_429))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_734])).
% 6.28/2.08  tff(c_46, plain, (![A_102, B_106, C_108]: (r3_waybel_9(A_102, B_106, C_108) | ~r2_hidden(C_108, k10_yellow_6(A_102, B_106)) | ~m1_subset_1(C_108, u1_struct_0(A_102)) | ~l1_waybel_0(B_106, A_102) | ~v7_waybel_0(B_106) | ~v4_orders_2(B_106) | v2_struct_0(B_106) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.28/2.08  tff(c_762, plain, (![A_431, B_432]: (r3_waybel_9(A_431, B_432, '#skF_2'(A_431, B_432, k1_xboole_0)) | k10_yellow_6(A_431, B_432)=k1_xboole_0 | ~m1_subset_1('#skF_2'(A_431, B_432, k1_xboole_0), u1_struct_0(A_431)) | ~l1_waybel_0(B_432, A_431) | ~v7_waybel_0(B_432) | ~v4_orders_2(B_432) | v2_struct_0(B_432) | ~l1_pre_topc(A_431) | ~v2_pre_topc(A_431) | v2_struct_0(A_431))), inference(resolution, [status(thm)], [c_741, c_46])).
% 6.28/2.08  tff(c_765, plain, (![A_9, B_53]: (r3_waybel_9(A_9, B_53, '#skF_2'(A_9, B_53, k1_xboole_0)) | k10_yellow_6(A_9, B_53)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_762])).
% 6.28/2.08  tff(c_769, plain, (![A_433, B_434]: (r3_waybel_9(A_433, B_434, '#skF_2'(A_433, B_434, k1_xboole_0)) | k10_yellow_6(A_433, B_434)=k1_xboole_0 | ~l1_waybel_0(B_434, A_433) | ~v7_waybel_0(B_434) | ~v4_orders_2(B_434) | v2_struct_0(B_434) | ~l1_pre_topc(A_433) | ~v2_pre_topc(A_433) | v2_struct_0(A_433))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_765])).
% 6.28/2.08  tff(c_48, plain, (![A_109, B_117, D_123, C_121]: (r3_waybel_9(A_109, B_117, D_123) | ~r3_waybel_9(A_109, C_121, D_123) | ~m1_subset_1(D_123, u1_struct_0(A_109)) | ~m2_yellow_6(C_121, A_109, B_117) | ~l1_waybel_0(B_117, A_109) | ~v7_waybel_0(B_117) | ~v4_orders_2(B_117) | v2_struct_0(B_117) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.28/2.08  tff(c_823, plain, (![A_448, B_449, B_450]: (r3_waybel_9(A_448, B_449, '#skF_2'(A_448, B_450, k1_xboole_0)) | ~m1_subset_1('#skF_2'(A_448, B_450, k1_xboole_0), u1_struct_0(A_448)) | ~m2_yellow_6(B_450, A_448, B_449) | ~l1_waybel_0(B_449, A_448) | ~v7_waybel_0(B_449) | ~v4_orders_2(B_449) | v2_struct_0(B_449) | k10_yellow_6(A_448, B_450)=k1_xboole_0 | ~l1_waybel_0(B_450, A_448) | ~v7_waybel_0(B_450) | ~v4_orders_2(B_450) | v2_struct_0(B_450) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448) | v2_struct_0(A_448))), inference(resolution, [status(thm)], [c_769, c_48])).
% 6.28/2.08  tff(c_826, plain, (![A_9, B_449, B_53]: (r3_waybel_9(A_9, B_449, '#skF_2'(A_9, B_53, k1_xboole_0)) | ~m2_yellow_6(B_53, A_9, B_449) | ~l1_waybel_0(B_449, A_9) | ~v7_waybel_0(B_449) | ~v4_orders_2(B_449) | v2_struct_0(B_449) | k10_yellow_6(A_9, B_53)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_823])).
% 6.28/2.08  tff(c_830, plain, (![A_451, B_452, B_453]: (r3_waybel_9(A_451, B_452, '#skF_2'(A_451, B_453, k1_xboole_0)) | ~m2_yellow_6(B_453, A_451, B_452) | ~l1_waybel_0(B_452, A_451) | ~v7_waybel_0(B_452) | ~v4_orders_2(B_452) | v2_struct_0(B_452) | k10_yellow_6(A_451, B_453)=k1_xboole_0 | ~l1_waybel_0(B_453, A_451) | ~v7_waybel_0(B_453) | ~v4_orders_2(B_453) | v2_struct_0(B_453) | ~l1_pre_topc(A_451) | ~v2_pre_topc(A_451) | v2_struct_0(A_451))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_826])).
% 6.28/2.08  tff(c_58, plain, (![A_144, C_154]: (~r3_waybel_9(A_144, '#skF_7'(A_144), C_154) | ~m1_subset_1(C_154, u1_struct_0(A_144)) | v1_compts_1(A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_274])).
% 6.28/2.08  tff(c_839, plain, (![A_454, B_455]: (~m1_subset_1('#skF_2'(A_454, B_455, k1_xboole_0), u1_struct_0(A_454)) | v1_compts_1(A_454) | ~m2_yellow_6(B_455, A_454, '#skF_7'(A_454)) | ~l1_waybel_0('#skF_7'(A_454), A_454) | ~v7_waybel_0('#skF_7'(A_454)) | ~v4_orders_2('#skF_7'(A_454)) | v2_struct_0('#skF_7'(A_454)) | k10_yellow_6(A_454, B_455)=k1_xboole_0 | ~l1_waybel_0(B_455, A_454) | ~v7_waybel_0(B_455) | ~v4_orders_2(B_455) | v2_struct_0(B_455) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(resolution, [status(thm)], [c_830, c_58])).
% 6.28/2.08  tff(c_843, plain, (![A_9, B_53]: (v1_compts_1(A_9) | ~m2_yellow_6(B_53, A_9, '#skF_7'(A_9)) | ~l1_waybel_0('#skF_7'(A_9), A_9) | ~v7_waybel_0('#skF_7'(A_9)) | ~v4_orders_2('#skF_7'(A_9)) | v2_struct_0('#skF_7'(A_9)) | k10_yellow_6(A_9, B_53)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_839])).
% 6.28/2.08  tff(c_847, plain, (![A_456, B_457]: (v1_compts_1(A_456) | ~m2_yellow_6(B_457, A_456, '#skF_7'(A_456)) | ~l1_waybel_0('#skF_7'(A_456), A_456) | ~v7_waybel_0('#skF_7'(A_456)) | ~v4_orders_2('#skF_7'(A_456)) | v2_struct_0('#skF_7'(A_456)) | k10_yellow_6(A_456, B_457)=k1_xboole_0 | ~l1_waybel_0(B_457, A_456) | ~v7_waybel_0(B_457) | ~v4_orders_2(B_457) | v2_struct_0(B_457) | ~l1_pre_topc(A_456) | ~v2_pre_topc(A_456) | v2_struct_0(A_456))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_843])).
% 6.28/2.08  tff(c_855, plain, (v1_compts_1('#skF_8') | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | ~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8') | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_142, c_847])).
% 6.28/2.08  tff(c_859, plain, (v1_compts_1('#skF_8') | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | ~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8') | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_8') | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_855])).
% 6.28/2.08  tff(c_860, plain, (k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | ~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8') | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_859])).
% 6.28/2.08  tff(c_861, plain, (~v4_orders_2('#skF_7'('#skF_8'))), inference(splitLeft, [status(thm)], [c_860])).
% 6.28/2.08  tff(c_871, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_66, c_861])).
% 6.28/2.08  tff(c_874, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_871])).
% 6.28/2.08  tff(c_876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_874])).
% 6.28/2.08  tff(c_878, plain, (v4_orders_2('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_860])).
% 6.28/2.08  tff(c_64, plain, (![A_144]: (v7_waybel_0('#skF_7'(A_144)) | v1_compts_1(A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_274])).
% 6.28/2.08  tff(c_62, plain, (![A_144]: (l1_waybel_0('#skF_7'(A_144), A_144) | v1_compts_1(A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_274])).
% 6.28/2.08  tff(c_10, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.28/2.08  tff(c_145, plain, (![C_185, A_186, B_187]: (v7_waybel_0(C_185) | ~m2_yellow_6(C_185, A_186, B_187) | ~l1_waybel_0(B_187, A_186) | ~v7_waybel_0(B_187) | ~v4_orders_2(B_187) | v2_struct_0(B_187) | ~l1_struct_0(A_186) | v2_struct_0(A_186))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.28/2.08  tff(c_148, plain, (![B_163]: (v7_waybel_0('#skF_10'(B_163)) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(resolution, [status(thm)], [c_142, c_145])).
% 6.28/2.08  tff(c_151, plain, (![B_163]: (v7_waybel_0('#skF_10'(B_163)) | ~l1_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(negUnitSimplification, [status(thm)], [c_78, c_148])).
% 6.28/2.08  tff(c_152, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_151])).
% 6.28/2.08  tff(c_155, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_10, c_152])).
% 6.28/2.08  tff(c_159, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_155])).
% 6.28/2.08  tff(c_161, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_151])).
% 6.28/2.08  tff(c_181, plain, (![C_197, A_198, B_199]: (l1_waybel_0(C_197, A_198) | ~m2_yellow_6(C_197, A_198, B_199) | ~l1_waybel_0(B_199, A_198) | ~v7_waybel_0(B_199) | ~v4_orders_2(B_199) | v2_struct_0(B_199) | ~l1_struct_0(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.28/2.08  tff(c_184, plain, (![B_163]: (l1_waybel_0('#skF_10'(B_163), '#skF_8') | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(resolution, [status(thm)], [c_142, c_181])).
% 6.28/2.08  tff(c_187, plain, (![B_163]: (l1_waybel_0('#skF_10'(B_163), '#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_184])).
% 6.28/2.08  tff(c_188, plain, (![B_163]: (l1_waybel_0('#skF_10'(B_163), '#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(negUnitSimplification, [status(thm)], [c_78, c_187])).
% 6.28/2.08  tff(c_877, plain, (~v7_waybel_0('#skF_7'('#skF_8')) | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8') | v2_struct_0('#skF_7'('#skF_8')) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_860])).
% 6.28/2.08  tff(c_879, plain, (~l1_waybel_0('#skF_10'('#skF_7'('#skF_8')), '#skF_8')), inference(splitLeft, [status(thm)], [c_877])).
% 6.28/2.08  tff(c_882, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_188, c_879])).
% 6.28/2.08  tff(c_885, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_882])).
% 6.28/2.08  tff(c_886, plain, (~v7_waybel_0('#skF_7'('#skF_8'))), inference(splitLeft, [status(thm)], [c_885])).
% 6.28/2.08  tff(c_889, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_64, c_886])).
% 6.28/2.08  tff(c_892, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_889])).
% 6.28/2.08  tff(c_894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_892])).
% 6.28/2.08  tff(c_895, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_885])).
% 6.28/2.08  tff(c_897, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_895])).
% 6.28/2.08  tff(c_900, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_62, c_897])).
% 6.28/2.08  tff(c_903, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_900])).
% 6.28/2.08  tff(c_905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_903])).
% 6.28/2.08  tff(c_906, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_895])).
% 6.28/2.08  tff(c_68, plain, (![A_144]: (~v2_struct_0('#skF_7'(A_144)) | v1_compts_1(A_144) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_274])).
% 6.28/2.08  tff(c_917, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_906, c_68])).
% 6.28/2.08  tff(c_920, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_917])).
% 6.28/2.08  tff(c_922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_920])).
% 6.28/2.08  tff(c_923, plain, (~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_877])).
% 6.28/2.08  tff(c_925, plain, (~v7_waybel_0('#skF_7'('#skF_8'))), inference(splitLeft, [status(thm)], [c_923])).
% 6.28/2.08  tff(c_928, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_64, c_925])).
% 6.28/2.08  tff(c_931, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_928])).
% 6.28/2.08  tff(c_933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_931])).
% 6.28/2.08  tff(c_935, plain, (v7_waybel_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_923])).
% 6.28/2.08  tff(c_160, plain, (![B_163]: (v7_waybel_0('#skF_10'(B_163)) | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(splitRight, [status(thm)], [c_151])).
% 6.28/2.08  tff(c_934, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | ~v7_waybel_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8')) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_923])).
% 6.28/2.08  tff(c_936, plain, (~v7_waybel_0('#skF_10'('#skF_7'('#skF_8')))), inference(splitLeft, [status(thm)], [c_934])).
% 6.28/2.08  tff(c_939, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_160, c_936])).
% 6.28/2.08  tff(c_942, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_935, c_939])).
% 6.28/2.08  tff(c_943, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_942])).
% 6.28/2.08  tff(c_946, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_62, c_943])).
% 6.28/2.08  tff(c_949, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_946])).
% 6.28/2.08  tff(c_951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_949])).
% 6.28/2.08  tff(c_952, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_942])).
% 6.28/2.08  tff(c_963, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_952, c_68])).
% 6.28/2.08  tff(c_966, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_963])).
% 6.28/2.08  tff(c_968, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_966])).
% 6.28/2.08  tff(c_969, plain, (~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | ~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_934])).
% 6.28/2.08  tff(c_971, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8')), inference(splitLeft, [status(thm)], [c_969])).
% 6.28/2.08  tff(c_974, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_62, c_971])).
% 6.28/2.08  tff(c_977, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_974])).
% 6.28/2.08  tff(c_979, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_977])).
% 6.28/2.08  tff(c_981, plain, (l1_waybel_0('#skF_7'('#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_969])).
% 6.28/2.08  tff(c_172, plain, (![C_193, A_194, B_195]: (v4_orders_2(C_193) | ~m2_yellow_6(C_193, A_194, B_195) | ~l1_waybel_0(B_195, A_194) | ~v7_waybel_0(B_195) | ~v4_orders_2(B_195) | v2_struct_0(B_195) | ~l1_struct_0(A_194) | v2_struct_0(A_194))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.28/2.08  tff(c_175, plain, (![B_163]: (v4_orders_2('#skF_10'(B_163)) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(resolution, [status(thm)], [c_142, c_172])).
% 6.28/2.08  tff(c_178, plain, (![B_163]: (v4_orders_2('#skF_10'(B_163)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_175])).
% 6.28/2.08  tff(c_179, plain, (![B_163]: (v4_orders_2('#skF_10'(B_163)) | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(negUnitSimplification, [status(thm)], [c_78, c_178])).
% 6.28/2.08  tff(c_980, plain, (~v4_orders_2('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8')) | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_969])).
% 6.28/2.08  tff(c_982, plain, (~v4_orders_2('#skF_10'('#skF_7'('#skF_8')))), inference(splitLeft, [status(thm)], [c_980])).
% 6.28/2.08  tff(c_985, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_179, c_982])).
% 6.28/2.08  tff(c_988, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_935, c_981, c_985])).
% 6.28/2.08  tff(c_991, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_988, c_68])).
% 6.28/2.08  tff(c_994, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_991])).
% 6.28/2.08  tff(c_996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_994])).
% 6.28/2.08  tff(c_997, plain, (k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0 | v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_980])).
% 6.28/2.08  tff(c_1006, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(splitLeft, [status(thm)], [c_997])).
% 6.28/2.08  tff(c_1009, plain, (v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_1006, c_68])).
% 6.28/2.08  tff(c_1012, plain, (v1_compts_1('#skF_8') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1009])).
% 6.28/2.08  tff(c_1014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116, c_1012])).
% 6.28/2.08  tff(c_1016, plain, (~v2_struct_0('#skF_7'('#skF_8'))), inference(splitRight, [status(thm)], [c_997])).
% 6.28/2.08  tff(c_1015, plain, (v2_struct_0('#skF_10'('#skF_7'('#skF_8'))) | k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_997])).
% 6.28/2.08  tff(c_1017, plain, (k10_yellow_6('#skF_8', '#skF_10'('#skF_7'('#skF_8')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1015])).
% 6.28/2.08  tff(c_102, plain, (![B_163]: (v1_compts_1('#skF_8') | v3_yellow_6('#skF_10'(B_163), '#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_138, plain, (![B_163]: (v3_yellow_6('#skF_10'(B_163), '#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(negUnitSimplification, [status(thm)], [c_116, c_102])).
% 6.28/2.08  tff(c_195, plain, (![A_205, B_206]: (k10_yellow_6(A_205, B_206)!=k1_xboole_0 | ~v3_yellow_6(B_206, A_205) | ~l1_waybel_0(B_206, A_205) | ~v7_waybel_0(B_206) | ~v4_orders_2(B_206) | v2_struct_0(B_206) | ~l1_pre_topc(A_205) | ~v2_pre_topc(A_205) | v2_struct_0(A_205))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.28/2.08  tff(c_201, plain, (![B_163]: (k10_yellow_6('#skF_8', '#skF_10'(B_163))!=k1_xboole_0 | ~l1_waybel_0('#skF_10'(B_163), '#skF_8') | ~v7_waybel_0('#skF_10'(B_163)) | ~v4_orders_2('#skF_10'(B_163)) | v2_struct_0('#skF_10'(B_163)) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(resolution, [status(thm)], [c_138, c_195])).
% 6.28/2.08  tff(c_205, plain, (![B_163]: (k10_yellow_6('#skF_8', '#skF_10'(B_163))!=k1_xboole_0 | ~l1_waybel_0('#skF_10'(B_163), '#skF_8') | ~v7_waybel_0('#skF_10'(B_163)) | ~v4_orders_2('#skF_10'(B_163)) | v2_struct_0('#skF_10'(B_163)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_201])).
% 6.28/2.08  tff(c_222, plain, (![B_218]: (k10_yellow_6('#skF_8', '#skF_10'(B_218))!=k1_xboole_0 | ~l1_waybel_0('#skF_10'(B_218), '#skF_8') | ~v7_waybel_0('#skF_10'(B_218)) | ~v4_orders_2('#skF_10'(B_218)) | v2_struct_0('#skF_10'(B_218)) | ~l1_waybel_0(B_218, '#skF_8') | ~v7_waybel_0(B_218) | ~v4_orders_2(B_218) | v2_struct_0(B_218))), inference(negUnitSimplification, [status(thm)], [c_78, c_205])).
% 6.28/2.08  tff(c_227, plain, (![B_219]: (k10_yellow_6('#skF_8', '#skF_10'(B_219))!=k1_xboole_0 | ~v7_waybel_0('#skF_10'(B_219)) | ~v4_orders_2('#skF_10'(B_219)) | v2_struct_0('#skF_10'(B_219)) | ~l1_waybel_0(B_219, '#skF_8') | ~v7_waybel_0(B_219) | ~v4_orders_2(B_219) | v2_struct_0(B_219))), inference(resolution, [status(thm)], [c_188, c_222])).
% 6.28/2.08  tff(c_232, plain, (![B_220]: (k10_yellow_6('#skF_8', '#skF_10'(B_220))!=k1_xboole_0 | ~v4_orders_2('#skF_10'(B_220)) | v2_struct_0('#skF_10'(B_220)) | ~l1_waybel_0(B_220, '#skF_8') | ~v7_waybel_0(B_220) | ~v4_orders_2(B_220) | v2_struct_0(B_220))), inference(resolution, [status(thm)], [c_160, c_227])).
% 6.28/2.08  tff(c_237, plain, (![B_221]: (k10_yellow_6('#skF_8', '#skF_10'(B_221))!=k1_xboole_0 | v2_struct_0('#skF_10'(B_221)) | ~l1_waybel_0(B_221, '#skF_8') | ~v7_waybel_0(B_221) | ~v4_orders_2(B_221) | v2_struct_0(B_221))), inference(resolution, [status(thm)], [c_179, c_232])).
% 6.28/2.08  tff(c_163, plain, (![C_189, A_190, B_191]: (~v2_struct_0(C_189) | ~m2_yellow_6(C_189, A_190, B_191) | ~l1_waybel_0(B_191, A_190) | ~v7_waybel_0(B_191) | ~v4_orders_2(B_191) | v2_struct_0(B_191) | ~l1_struct_0(A_190) | v2_struct_0(A_190))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.28/2.08  tff(c_166, plain, (![B_163]: (~v2_struct_0('#skF_10'(B_163)) | ~l1_struct_0('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(resolution, [status(thm)], [c_142, c_163])).
% 6.28/2.08  tff(c_169, plain, (![B_163]: (~v2_struct_0('#skF_10'(B_163)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_166])).
% 6.28/2.08  tff(c_170, plain, (![B_163]: (~v2_struct_0('#skF_10'(B_163)) | ~l1_waybel_0(B_163, '#skF_8') | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163))), inference(negUnitSimplification, [status(thm)], [c_78, c_169])).
% 6.28/2.08  tff(c_241, plain, (![B_221]: (k10_yellow_6('#skF_8', '#skF_10'(B_221))!=k1_xboole_0 | ~l1_waybel_0(B_221, '#skF_8') | ~v7_waybel_0(B_221) | ~v4_orders_2(B_221) | v2_struct_0(B_221))), inference(resolution, [status(thm)], [c_237, c_170])).
% 6.28/2.08  tff(c_1062, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1017, c_241])).
% 6.28/2.08  tff(c_1118, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_935, c_981, c_1062])).
% 6.28/2.08  tff(c_1120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1016, c_1118])).
% 6.28/2.08  tff(c_1121, plain, (v2_struct_0('#skF_10'('#skF_7'('#skF_8')))), inference(splitRight, [status(thm)], [c_1015])).
% 6.28/2.08  tff(c_1125, plain, (~l1_waybel_0('#skF_7'('#skF_8'), '#skF_8') | ~v7_waybel_0('#skF_7'('#skF_8')) | ~v4_orders_2('#skF_7'('#skF_8')) | v2_struct_0('#skF_7'('#skF_8'))), inference(resolution, [status(thm)], [c_1121, c_170])).
% 6.28/2.08  tff(c_1128, plain, (v2_struct_0('#skF_7'('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_935, c_981, c_1125])).
% 6.28/2.08  tff(c_1130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1016, c_1128])).
% 6.28/2.08  tff(c_1131, plain, (~v2_struct_0('#skF_9')), inference(splitRight, [status(thm)], [c_88])).
% 6.28/2.08  tff(c_1132, plain, (v1_compts_1('#skF_8')), inference(splitRight, [status(thm)], [c_88])).
% 6.28/2.08  tff(c_86, plain, (v4_orders_2('#skF_9') | ~v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_1134, plain, (v4_orders_2('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_86])).
% 6.28/2.08  tff(c_84, plain, (v7_waybel_0('#skF_9') | ~v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_1137, plain, (v7_waybel_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_84])).
% 6.28/2.08  tff(c_82, plain, (l1_waybel_0('#skF_9', '#skF_8') | ~v1_compts_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_1140, plain, (l1_waybel_0('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_82])).
% 6.28/2.08  tff(c_54, plain, (![A_138, B_142]: (r3_waybel_9(A_138, B_142, '#skF_5'(A_138, B_142)) | ~l1_waybel_0(B_142, A_138) | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.28/2.08  tff(c_56, plain, (![A_138, B_142]: (m1_subset_1('#skF_5'(A_138, B_142), u1_struct_0(A_138)) | ~l1_waybel_0(B_142, A_138) | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.28/2.08  tff(c_1199, plain, (![A_524, B_525, C_526]: (m2_yellow_6('#skF_4'(A_524, B_525, C_526), A_524, B_525) | ~r3_waybel_9(A_524, B_525, C_526) | ~m1_subset_1(C_526, u1_struct_0(A_524)) | ~l1_waybel_0(B_525, A_524) | ~v7_waybel_0(B_525) | ~v4_orders_2(B_525) | v2_struct_0(B_525) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(cnfTransformation, [status(thm)], [f_222])).
% 6.28/2.08  tff(c_34, plain, (![C_98, A_95, B_96]: (l1_waybel_0(C_98, A_95) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.28/2.08  tff(c_1299, plain, (![A_548, B_549, C_550]: (l1_waybel_0('#skF_4'(A_548, B_549, C_550), A_548) | ~l1_struct_0(A_548) | ~r3_waybel_9(A_548, B_549, C_550) | ~m1_subset_1(C_550, u1_struct_0(A_548)) | ~l1_waybel_0(B_549, A_548) | ~v7_waybel_0(B_549) | ~v4_orders_2(B_549) | v2_struct_0(B_549) | ~l1_pre_topc(A_548) | ~v2_pre_topc(A_548) | v2_struct_0(A_548))), inference(resolution, [status(thm)], [c_1199, c_34])).
% 6.28/2.08  tff(c_1351, plain, (![A_595, B_596, B_597]: (l1_waybel_0('#skF_4'(A_595, B_596, '#skF_5'(A_595, B_597)), A_595) | ~l1_struct_0(A_595) | ~r3_waybel_9(A_595, B_596, '#skF_5'(A_595, B_597)) | ~l1_waybel_0(B_596, A_595) | ~v7_waybel_0(B_596) | ~v4_orders_2(B_596) | v2_struct_0(B_596) | ~l1_waybel_0(B_597, A_595) | ~v7_waybel_0(B_597) | ~v4_orders_2(B_597) | v2_struct_0(B_597) | ~v1_compts_1(A_595) | ~l1_pre_topc(A_595) | ~v2_pre_topc(A_595) | v2_struct_0(A_595))), inference(resolution, [status(thm)], [c_56, c_1299])).
% 6.28/2.08  tff(c_42, plain, (![B_101, A_99]: (v3_yellow_6(B_101, A_99) | k10_yellow_6(A_99, B_101)=k1_xboole_0 | ~l1_waybel_0(B_101, A_99) | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.28/2.08  tff(c_80, plain, (![C_162]: (~v3_yellow_6(C_162, '#skF_8') | ~m2_yellow_6(C_162, '#skF_8', '#skF_9') | ~v1_compts_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_299])).
% 6.28/2.08  tff(c_1142, plain, (![C_162]: (~v3_yellow_6(C_162, '#skF_8') | ~m2_yellow_6(C_162, '#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_1132, c_80])).
% 6.28/2.08  tff(c_1215, plain, (![C_526]: (~v3_yellow_6('#skF_4'('#skF_8', '#skF_9', C_526), '#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', C_526) | ~m1_subset_1(C_526, u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1199, c_1142])).
% 6.28/2.08  tff(c_1222, plain, (![C_526]: (~v3_yellow_6('#skF_4'('#skF_8', '#skF_9', C_526), '#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', C_526) | ~m1_subset_1(C_526, u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1134, c_1137, c_1140, c_1215])).
% 6.28/2.08  tff(c_1224, plain, (![C_527]: (~v3_yellow_6('#skF_4'('#skF_8', '#skF_9', C_527), '#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', C_527) | ~m1_subset_1(C_527, u1_struct_0('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_78, c_1131, c_1222])).
% 6.28/2.08  tff(c_1227, plain, (![C_527]: (~r3_waybel_9('#skF_8', '#skF_9', C_527) | ~m1_subset_1(C_527, u1_struct_0('#skF_8')) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', C_527))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', C_527), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', C_527)) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', C_527)) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', C_527)) | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_42, c_1224])).
% 6.28/2.08  tff(c_1230, plain, (![C_527]: (~r3_waybel_9('#skF_8', '#skF_9', C_527) | ~m1_subset_1(C_527, u1_struct_0('#skF_8')) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', C_527))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', C_527), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', C_527)) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', C_527)) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', C_527)) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1227])).
% 6.28/2.08  tff(c_1240, plain, (![C_534]: (~r3_waybel_9('#skF_8', '#skF_9', C_534) | ~m1_subset_1(C_534, u1_struct_0('#skF_8')) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', C_534))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', C_534), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', C_534)) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', C_534)) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', C_534)))), inference(negUnitSimplification, [status(thm)], [c_78, c_1230])).
% 6.28/2.08  tff(c_1248, plain, (![B_142]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_1240])).
% 6.28/2.08  tff(c_1255, plain, (![B_142]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1132, c_1248])).
% 6.28/2.08  tff(c_1256, plain, (![B_142]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)), '#skF_8') | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142))), inference(negUnitSimplification, [status(thm)], [c_78, c_1255])).
% 6.28/2.08  tff(c_1355, plain, (![B_597]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597)) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_597, '#skF_8') | ~v7_waybel_0(B_597) | ~v4_orders_2(B_597) | v2_struct_0(B_597) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1351, c_1256])).
% 6.28/2.08  tff(c_1358, plain, (![B_597]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597)) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_597, '#skF_8') | ~v7_waybel_0(B_597) | ~v4_orders_2(B_597) | v2_struct_0(B_597) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1132, c_1134, c_1137, c_1140, c_1355])).
% 6.28/2.08  tff(c_1359, plain, (![B_597]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_597)) | ~l1_waybel_0(B_597, '#skF_8') | ~v7_waybel_0(B_597) | ~v4_orders_2(B_597) | v2_struct_0(B_597))), inference(negUnitSimplification, [status(thm)], [c_78, c_1131, c_1358])).
% 6.28/2.08  tff(c_1396, plain, (~l1_struct_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1359])).
% 6.28/2.08  tff(c_1400, plain, (~l1_pre_topc('#skF_8')), inference(resolution, [status(thm)], [c_10, c_1396])).
% 6.28/2.08  tff(c_1404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1400])).
% 6.28/2.08  tff(c_1406, plain, (l1_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_1359])).
% 6.28/2.08  tff(c_38, plain, (![C_98, A_95, B_96]: (v4_orders_2(C_98) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.28/2.08  tff(c_1257, plain, (![A_535, B_536, C_537]: (v4_orders_2('#skF_4'(A_535, B_536, C_537)) | ~l1_struct_0(A_535) | ~r3_waybel_9(A_535, B_536, C_537) | ~m1_subset_1(C_537, u1_struct_0(A_535)) | ~l1_waybel_0(B_536, A_535) | ~v7_waybel_0(B_536) | ~v4_orders_2(B_536) | v2_struct_0(B_536) | ~l1_pre_topc(A_535) | ~v2_pre_topc(A_535) | v2_struct_0(A_535))), inference(resolution, [status(thm)], [c_1199, c_38])).
% 6.28/2.08  tff(c_1263, plain, (![A_138, B_536, B_142]: (v4_orders_2('#skF_4'(A_138, B_536, '#skF_5'(A_138, B_142))) | ~l1_struct_0(A_138) | ~r3_waybel_9(A_138, B_536, '#skF_5'(A_138, B_142)) | ~l1_waybel_0(B_536, A_138) | ~v7_waybel_0(B_536) | ~v4_orders_2(B_536) | v2_struct_0(B_536) | ~l1_waybel_0(B_142, A_138) | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_56, c_1257])).
% 6.28/2.08  tff(c_36, plain, (![C_98, A_95, B_96]: (v7_waybel_0(C_98) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.28/2.08  tff(c_1233, plain, (![A_531, B_532, C_533]: (v7_waybel_0('#skF_4'(A_531, B_532, C_533)) | ~l1_struct_0(A_531) | ~r3_waybel_9(A_531, B_532, C_533) | ~m1_subset_1(C_533, u1_struct_0(A_531)) | ~l1_waybel_0(B_532, A_531) | ~v7_waybel_0(B_532) | ~v4_orders_2(B_532) | v2_struct_0(B_532) | ~l1_pre_topc(A_531) | ~v2_pre_topc(A_531) | v2_struct_0(A_531))), inference(resolution, [status(thm)], [c_1199, c_36])).
% 6.28/2.08  tff(c_1239, plain, (![A_138, B_532, B_142]: (v7_waybel_0('#skF_4'(A_138, B_532, '#skF_5'(A_138, B_142))) | ~l1_struct_0(A_138) | ~r3_waybel_9(A_138, B_532, '#skF_5'(A_138, B_142)) | ~l1_waybel_0(B_532, A_138) | ~v7_waybel_0(B_532) | ~v4_orders_2(B_532) | v2_struct_0(B_532) | ~l1_waybel_0(B_142, A_138) | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_56, c_1233])).
% 6.28/2.08  tff(c_1407, plain, (![B_620]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_620)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_620))) | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_620))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_620))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_620)) | ~l1_waybel_0(B_620, '#skF_8') | ~v7_waybel_0(B_620) | ~v4_orders_2(B_620) | v2_struct_0(B_620))), inference(splitRight, [status(thm)], [c_1359])).
% 6.28/2.08  tff(c_1411, plain, (![B_142]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1239, c_1407])).
% 6.28/2.08  tff(c_1414, plain, (![B_142]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1132, c_1134, c_1137, c_1140, c_1406, c_1411])).
% 6.28/2.08  tff(c_1416, plain, (![B_621]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_621)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_621))) | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_621))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_621)) | ~l1_waybel_0(B_621, '#skF_8') | ~v7_waybel_0(B_621) | ~v4_orders_2(B_621) | v2_struct_0(B_621))), inference(negUnitSimplification, [status(thm)], [c_78, c_1131, c_1414])).
% 6.28/2.08  tff(c_1420, plain, (![B_142]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~l1_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_1263, c_1416])).
% 6.28/2.08  tff(c_1423, plain, (![B_142]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | v2_struct_0('#skF_9') | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1132, c_1134, c_1137, c_1140, c_1406, c_1420])).
% 6.28/2.08  tff(c_1425, plain, (![B_622]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_622)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_622))) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_622)) | ~l1_waybel_0(B_622, '#skF_8') | ~v7_waybel_0(B_622) | ~v4_orders_2(B_622) | v2_struct_0(B_622))), inference(negUnitSimplification, [status(thm)], [c_78, c_1131, c_1423])).
% 6.28/2.08  tff(c_40, plain, (![C_98, A_95, B_96]: (~v2_struct_0(C_98) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.28/2.08  tff(c_1217, plain, (![A_524, B_525, C_526]: (~v2_struct_0('#skF_4'(A_524, B_525, C_526)) | ~l1_struct_0(A_524) | ~r3_waybel_9(A_524, B_525, C_526) | ~m1_subset_1(C_526, u1_struct_0(A_524)) | ~l1_waybel_0(B_525, A_524) | ~v7_waybel_0(B_525) | ~v4_orders_2(B_525) | v2_struct_0(B_525) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(resolution, [status(thm)], [c_1199, c_40])).
% 6.28/2.08  tff(c_1427, plain, (![B_622]: (~l1_struct_0('#skF_8') | ~m1_subset_1('#skF_5'('#skF_8', B_622), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_622)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_622)) | ~l1_waybel_0(B_622, '#skF_8') | ~v7_waybel_0(B_622) | ~v4_orders_2(B_622) | v2_struct_0(B_622))), inference(resolution, [status(thm)], [c_1425, c_1217])).
% 6.28/2.08  tff(c_1430, plain, (![B_622]: (~m1_subset_1('#skF_5'('#skF_8', B_622), u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8') | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_622)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_622)) | ~l1_waybel_0(B_622, '#skF_8') | ~v7_waybel_0(B_622) | ~v4_orders_2(B_622) | v2_struct_0(B_622))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1134, c_1137, c_1140, c_1406, c_1427])).
% 6.28/2.08  tff(c_1437, plain, (![B_627]: (~m1_subset_1('#skF_5'('#skF_8', B_627), u1_struct_0('#skF_8')) | k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_627)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_627)) | ~l1_waybel_0(B_627, '#skF_8') | ~v7_waybel_0(B_627) | ~v4_orders_2(B_627) | v2_struct_0(B_627))), inference(negUnitSimplification, [status(thm)], [c_78, c_1131, c_1430])).
% 6.28/2.08  tff(c_1441, plain, (![B_142]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_1437])).
% 6.28/2.08  tff(c_1444, plain, (![B_142]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1132, c_1441])).
% 6.28/2.08  tff(c_1446, plain, (![B_628]: (k10_yellow_6('#skF_8', '#skF_4'('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_628)))=k1_xboole_0 | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_628)) | ~l1_waybel_0(B_628, '#skF_8') | ~v7_waybel_0(B_628) | ~v4_orders_2(B_628) | v2_struct_0(B_628))), inference(negUnitSimplification, [status(thm)], [c_78, c_1444])).
% 6.28/2.08  tff(c_1286, plain, (![C_545, A_546, B_547]: (r2_hidden(C_545, k10_yellow_6(A_546, '#skF_4'(A_546, B_547, C_545))) | ~r3_waybel_9(A_546, B_547, C_545) | ~m1_subset_1(C_545, u1_struct_0(A_546)) | ~l1_waybel_0(B_547, A_546) | ~v7_waybel_0(B_547) | ~v4_orders_2(B_547) | v2_struct_0(B_547) | ~l1_pre_topc(A_546) | ~v2_pre_topc(A_546) | v2_struct_0(A_546))), inference(cnfTransformation, [status(thm)], [f_222])).
% 6.28/2.08  tff(c_1298, plain, (![A_546, B_547, C_545]: (~r1_tarski(k10_yellow_6(A_546, '#skF_4'(A_546, B_547, C_545)), C_545) | ~r3_waybel_9(A_546, B_547, C_545) | ~m1_subset_1(C_545, u1_struct_0(A_546)) | ~l1_waybel_0(B_547, A_546) | ~v7_waybel_0(B_547) | ~v4_orders_2(B_547) | v2_struct_0(B_547) | ~l1_pre_topc(A_546) | ~v2_pre_topc(A_546) | v2_struct_0(A_546))), inference(resolution, [status(thm)], [c_1286, c_8])).
% 6.28/2.08  tff(c_1459, plain, (![B_628]: (~r1_tarski(k1_xboole_0, '#skF_5'('#skF_8', B_628)) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_628)) | ~m1_subset_1('#skF_5'('#skF_8', B_628), u1_struct_0('#skF_8')) | ~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_628)) | ~l1_waybel_0(B_628, '#skF_8') | ~v7_waybel_0(B_628) | ~v4_orders_2(B_628) | v2_struct_0(B_628))), inference(superposition, [status(thm), theory('equality')], [c_1446, c_1298])).
% 6.28/2.08  tff(c_1486, plain, (![B_628]: (~m1_subset_1('#skF_5'('#skF_8', B_628), u1_struct_0('#skF_8')) | v2_struct_0('#skF_9') | v2_struct_0('#skF_8') | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_628)) | ~l1_waybel_0(B_628, '#skF_8') | ~v7_waybel_0(B_628) | ~v4_orders_2(B_628) | v2_struct_0(B_628))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1134, c_1137, c_1140, c_2, c_1459])).
% 6.28/2.08  tff(c_1501, plain, (![B_629]: (~m1_subset_1('#skF_5'('#skF_8', B_629), u1_struct_0('#skF_8')) | ~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_629)) | ~l1_waybel_0(B_629, '#skF_8') | ~v7_waybel_0(B_629) | ~v4_orders_2(B_629) | v2_struct_0(B_629))), inference(negUnitSimplification, [status(thm)], [c_78, c_1131, c_1486])).
% 6.28/2.08  tff(c_1505, plain, (![B_142]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8'))), inference(resolution, [status(thm)], [c_56, c_1501])).
% 6.28/2.08  tff(c_1508, plain, (![B_142]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_142)) | ~l1_waybel_0(B_142, '#skF_8') | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | v2_struct_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1132, c_1505])).
% 6.28/2.08  tff(c_1510, plain, (![B_630]: (~r3_waybel_9('#skF_8', '#skF_9', '#skF_5'('#skF_8', B_630)) | ~l1_waybel_0(B_630, '#skF_8') | ~v7_waybel_0(B_630) | ~v4_orders_2(B_630) | v2_struct_0(B_630))), inference(negUnitSimplification, [status(thm)], [c_78, c_1508])).
% 6.28/2.08  tff(c_1518, plain, (~l1_waybel_0('#skF_9', '#skF_8') | ~v7_waybel_0('#skF_9') | ~v4_orders_2('#skF_9') | v2_struct_0('#skF_9') | ~v1_compts_1('#skF_8') | ~l1_pre_topc('#skF_8') | ~v2_pre_topc('#skF_8') | v2_struct_0('#skF_8')), inference(resolution, [status(thm)], [c_54, c_1510])).
% 6.28/2.08  tff(c_1525, plain, (v2_struct_0('#skF_9') | v2_struct_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_1132, c_1134, c_1137, c_1140, c_1518])).
% 6.28/2.08  tff(c_1527, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_1131, c_1525])).
% 6.28/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.08  
% 6.28/2.08  Inference rules
% 6.28/2.08  ----------------------
% 6.28/2.08  #Ref     : 0
% 6.28/2.08  #Sup     : 256
% 6.28/2.08  #Fact    : 2
% 6.28/2.08  #Define  : 0
% 6.28/2.08  #Split   : 18
% 6.28/2.08  #Chain   : 0
% 6.28/2.08  #Close   : 0
% 6.28/2.08  
% 6.28/2.08  Ordering : KBO
% 6.28/2.08  
% 6.28/2.08  Simplification rules
% 6.28/2.08  ----------------------
% 6.28/2.08  #Subsume      : 67
% 6.28/2.08  #Demod        : 270
% 6.28/2.08  #Tautology    : 46
% 6.28/2.08  #SimpNegUnit  : 59
% 6.28/2.08  #BackRed      : 0
% 6.28/2.08  
% 6.28/2.08  #Partial instantiations: 0
% 6.28/2.08  #Strategies tried      : 1
% 6.28/2.08  
% 6.28/2.08  Timing (in seconds)
% 6.28/2.08  ----------------------
% 6.28/2.08  Preprocessing        : 0.38
% 6.28/2.08  Parsing              : 0.19
% 6.28/2.08  CNF conversion       : 0.04
% 6.28/2.08  Main loop            : 0.85
% 6.28/2.08  Inferencing          : 0.36
% 6.28/2.08  Reduction            : 0.22
% 6.28/2.08  Demodulation         : 0.14
% 6.28/2.08  BG Simplification    : 0.04
% 6.28/2.08  Subsumption          : 0.18
% 6.28/2.08  Abstraction          : 0.03
% 6.28/2.08  MUC search           : 0.00
% 6.28/2.08  Cooper               : 0.00
% 6.28/2.08  Total                : 1.31
% 6.28/2.08  Index Insertion      : 0.00
% 6.28/2.08  Index Deletion       : 0.00
% 6.28/2.08  Index Matching       : 0.00
% 6.28/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
