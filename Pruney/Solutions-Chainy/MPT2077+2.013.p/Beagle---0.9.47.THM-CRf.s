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
% DateTime   : Thu Dec  3 10:31:41 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :  250 (3389 expanded)
%              Number of leaves         :   45 (1121 expanded)
%              Depth                    :   37
%              Number of atoms          : 1302 (24321 expanded)
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

tff(f_271,negated_conjecture,(
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

tff(f_246,axiom,(
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

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_waybel_9)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_waybel_9)).

tff(f_44,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_yellow_6)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_waybel_9)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_82,plain,
    ( ~ v2_struct_0('#skF_8')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_110,plain,(
    ~ v1_compts_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_70,plain,(
    v2_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_68,plain,(
    l1_pre_topc('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_60,plain,(
    ! [A_138] :
      ( v4_orders_2('#skF_6'(A_138))
      | v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_108,plain,(
    ! [B_157] :
      ( v1_compts_1('#skF_7')
      | m2_yellow_6('#skF_9'(B_157),'#skF_7',B_157)
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_129,plain,(
    ! [B_157] :
      ( m2_yellow_6('#skF_9'(B_157),'#skF_7',B_157)
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_108])).

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

tff(c_297,plain,(
    ! [A_258,B_259,D_260] :
      ( m1_connsp_2('#skF_1'(A_258,B_259,k10_yellow_6(A_258,B_259),D_260),A_258,D_260)
      | r2_hidden(D_260,k10_yellow_6(A_258,B_259))
      | ~ m1_subset_1(D_260,u1_struct_0(A_258))
      | ~ m1_subset_1(k10_yellow_6(A_258,B_259),k1_zfmisc_1(u1_struct_0(A_258)))
      | ~ l1_waybel_0(B_259,A_258)
      | ~ v7_waybel_0(B_259)
      | ~ v4_orders_2(B_259)
      | v2_struct_0(B_259)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_300,plain,(
    ! [A_93,B_94,D_260] :
      ( m1_connsp_2('#skF_1'(A_93,B_94,k10_yellow_6(A_93,B_94),D_260),A_93,D_260)
      | r2_hidden(D_260,k10_yellow_6(A_93,B_94))
      | ~ m1_subset_1(D_260,u1_struct_0(A_93))
      | ~ l1_waybel_0(B_94,A_93)
      | ~ v7_waybel_0(B_94)
      | ~ v4_orders_2(B_94)
      | v2_struct_0(B_94)
      | ~ l1_pre_topc(A_93)
      | ~ v2_pre_topc(A_93)
      | v2_struct_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_32,c_297])).

tff(c_305,plain,(
    ! [A_264,B_265,C_266,E_267] :
      ( r2_hidden('#skF_2'(A_264,B_265,C_266),C_266)
      | r1_waybel_0(A_264,B_265,E_267)
      | ~ m1_connsp_2(E_267,A_264,'#skF_2'(A_264,B_265,C_266))
      | k10_yellow_6(A_264,B_265) = C_266
      | ~ m1_subset_1(C_266,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_waybel_0(B_265,A_264)
      | ~ v7_waybel_0(B_265)
      | ~ v4_orders_2(B_265)
      | v2_struct_0(B_265)
      | ~ l1_pre_topc(A_264)
      | ~ v2_pre_topc(A_264)
      | v2_struct_0(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_406,plain,(
    ! [A_351,B_352,C_353,B_354] :
      ( r2_hidden('#skF_2'(A_351,B_352,C_353),C_353)
      | r1_waybel_0(A_351,B_352,'#skF_1'(A_351,B_354,k10_yellow_6(A_351,B_354),'#skF_2'(A_351,B_352,C_353)))
      | k10_yellow_6(A_351,B_352) = C_353
      | ~ m1_subset_1(C_353,k1_zfmisc_1(u1_struct_0(A_351)))
      | ~ l1_waybel_0(B_352,A_351)
      | ~ v7_waybel_0(B_352)
      | ~ v4_orders_2(B_352)
      | v2_struct_0(B_352)
      | r2_hidden('#skF_2'(A_351,B_352,C_353),k10_yellow_6(A_351,B_354))
      | ~ m1_subset_1('#skF_2'(A_351,B_352,C_353),u1_struct_0(A_351))
      | ~ l1_waybel_0(B_354,A_351)
      | ~ v7_waybel_0(B_354)
      | ~ v4_orders_2(B_354)
      | v2_struct_0(B_354)
      | ~ l1_pre_topc(A_351)
      | ~ v2_pre_topc(A_351)
      | v2_struct_0(A_351) ) ),
    inference(resolution,[status(thm)],[c_300,c_305])).

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

tff(c_430,plain,(
    ! [A_355,B_356,C_357] :
      ( ~ m1_subset_1(k10_yellow_6(A_355,B_356),k1_zfmisc_1(u1_struct_0(A_355)))
      | r2_hidden('#skF_2'(A_355,B_356,C_357),C_357)
      | k10_yellow_6(A_355,B_356) = C_357
      | ~ m1_subset_1(C_357,k1_zfmisc_1(u1_struct_0(A_355)))
      | r2_hidden('#skF_2'(A_355,B_356,C_357),k10_yellow_6(A_355,B_356))
      | ~ m1_subset_1('#skF_2'(A_355,B_356,C_357),u1_struct_0(A_355))
      | ~ l1_waybel_0(B_356,A_355)
      | ~ v7_waybel_0(B_356)
      | ~ v4_orders_2(B_356)
      | v2_struct_0(B_356)
      | ~ l1_pre_topc(A_355)
      | ~ v2_pre_topc(A_355)
      | v2_struct_0(A_355) ) ),
    inference(resolution,[status(thm)],[c_406,c_28])).

tff(c_450,plain,(
    ! [A_358,B_359,C_360] :
      ( r2_hidden('#skF_2'(A_358,B_359,C_360),C_360)
      | k10_yellow_6(A_358,B_359) = C_360
      | ~ m1_subset_1(C_360,k1_zfmisc_1(u1_struct_0(A_358)))
      | r2_hidden('#skF_2'(A_358,B_359,C_360),k10_yellow_6(A_358,B_359))
      | ~ m1_subset_1('#skF_2'(A_358,B_359,C_360),u1_struct_0(A_358))
      | ~ l1_waybel_0(B_359,A_358)
      | ~ v7_waybel_0(B_359)
      | ~ v4_orders_2(B_359)
      | v2_struct_0(B_359)
      | ~ l1_pre_topc(A_358)
      | ~ v2_pre_topc(A_358)
      | v2_struct_0(A_358) ) ),
    inference(resolution,[status(thm)],[c_32,c_430])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( ~ r1_tarski(B_7,A_6)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_674,plain,(
    ! [C_391,A_392,B_393] :
      ( ~ r1_tarski(C_391,'#skF_2'(A_392,B_393,C_391))
      | k10_yellow_6(A_392,B_393) = C_391
      | ~ m1_subset_1(C_391,k1_zfmisc_1(u1_struct_0(A_392)))
      | r2_hidden('#skF_2'(A_392,B_393,C_391),k10_yellow_6(A_392,B_393))
      | ~ m1_subset_1('#skF_2'(A_392,B_393,C_391),u1_struct_0(A_392))
      | ~ l1_waybel_0(B_393,A_392)
      | ~ v7_waybel_0(B_393)
      | ~ v4_orders_2(B_393)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(resolution,[status(thm)],[c_450,c_8])).

tff(c_677,plain,(
    ! [A_392,B_393] :
      ( k10_yellow_6(A_392,B_393) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_392)))
      | r2_hidden('#skF_2'(A_392,B_393,k1_xboole_0),k10_yellow_6(A_392,B_393))
      | ~ m1_subset_1('#skF_2'(A_392,B_393,k1_xboole_0),u1_struct_0(A_392))
      | ~ l1_waybel_0(B_393,A_392)
      | ~ v7_waybel_0(B_393)
      | ~ v4_orders_2(B_393)
      | v2_struct_0(B_393)
      | ~ l1_pre_topc(A_392)
      | ~ v2_pre_topc(A_392)
      | v2_struct_0(A_392) ) ),
    inference(resolution,[status(thm)],[c_2,c_674])).

tff(c_684,plain,(
    ! [A_397,B_398] :
      ( k10_yellow_6(A_397,B_398) = k1_xboole_0
      | r2_hidden('#skF_2'(A_397,B_398,k1_xboole_0),k10_yellow_6(A_397,B_398))
      | ~ m1_subset_1('#skF_2'(A_397,B_398,k1_xboole_0),u1_struct_0(A_397))
      | ~ l1_waybel_0(B_398,A_397)
      | ~ v7_waybel_0(B_398)
      | ~ v4_orders_2(B_398)
      | v2_struct_0(B_398)
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_677])).

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

tff(c_705,plain,(
    ! [A_399,B_400] :
      ( r3_waybel_9(A_399,B_400,'#skF_2'(A_399,B_400,k1_xboole_0))
      | k10_yellow_6(A_399,B_400) = k1_xboole_0
      | ~ m1_subset_1('#skF_2'(A_399,B_400,k1_xboole_0),u1_struct_0(A_399))
      | ~ l1_waybel_0(B_400,A_399)
      | ~ v7_waybel_0(B_400)
      | ~ v4_orders_2(B_400)
      | v2_struct_0(B_400)
      | ~ l1_pre_topc(A_399)
      | ~ v2_pre_topc(A_399)
      | v2_struct_0(A_399) ) ),
    inference(resolution,[status(thm)],[c_684,c_46])).

tff(c_708,plain,(
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
    inference(resolution,[status(thm)],[c_12,c_705])).

tff(c_712,plain,(
    ! [A_401,B_402] :
      ( r3_waybel_9(A_401,B_402,'#skF_2'(A_401,B_402,k1_xboole_0))
      | k10_yellow_6(A_401,B_402) = k1_xboole_0
      | ~ l1_waybel_0(B_402,A_401)
      | ~ v7_waybel_0(B_402)
      | ~ v4_orders_2(B_402)
      | v2_struct_0(B_402)
      | ~ l1_pre_topc(A_401)
      | ~ v2_pre_topc(A_401)
      | v2_struct_0(A_401) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_708])).

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

tff(c_766,plain,(
    ! [A_416,B_417,B_418] :
      ( r3_waybel_9(A_416,B_417,'#skF_2'(A_416,B_418,k1_xboole_0))
      | ~ m1_subset_1('#skF_2'(A_416,B_418,k1_xboole_0),u1_struct_0(A_416))
      | ~ m2_yellow_6(B_418,A_416,B_417)
      | ~ l1_waybel_0(B_417,A_416)
      | ~ v7_waybel_0(B_417)
      | ~ v4_orders_2(B_417)
      | v2_struct_0(B_417)
      | k10_yellow_6(A_416,B_418) = k1_xboole_0
      | ~ l1_waybel_0(B_418,A_416)
      | ~ v7_waybel_0(B_418)
      | ~ v4_orders_2(B_418)
      | v2_struct_0(B_418)
      | ~ l1_pre_topc(A_416)
      | ~ v2_pre_topc(A_416)
      | v2_struct_0(A_416) ) ),
    inference(resolution,[status(thm)],[c_712,c_48])).

tff(c_769,plain,(
    ! [A_9,B_417,B_53] :
      ( r3_waybel_9(A_9,B_417,'#skF_2'(A_9,B_53,k1_xboole_0))
      | ~ m2_yellow_6(B_53,A_9,B_417)
      | ~ l1_waybel_0(B_417,A_9)
      | ~ v7_waybel_0(B_417)
      | ~ v4_orders_2(B_417)
      | v2_struct_0(B_417)
      | k10_yellow_6(A_9,B_53) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_waybel_0(B_53,A_9)
      | ~ v7_waybel_0(B_53)
      | ~ v4_orders_2(B_53)
      | v2_struct_0(B_53)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_766])).

tff(c_773,plain,(
    ! [A_419,B_420,B_421] :
      ( r3_waybel_9(A_419,B_420,'#skF_2'(A_419,B_421,k1_xboole_0))
      | ~ m2_yellow_6(B_421,A_419,B_420)
      | ~ l1_waybel_0(B_420,A_419)
      | ~ v7_waybel_0(B_420)
      | ~ v4_orders_2(B_420)
      | v2_struct_0(B_420)
      | k10_yellow_6(A_419,B_421) = k1_xboole_0
      | ~ l1_waybel_0(B_421,A_419)
      | ~ v7_waybel_0(B_421)
      | ~ v4_orders_2(B_421)
      | v2_struct_0(B_421)
      | ~ l1_pre_topc(A_419)
      | ~ v2_pre_topc(A_419)
      | v2_struct_0(A_419) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_769])).

tff(c_54,plain,(
    ! [A_138,C_148] :
      ( ~ r3_waybel_9(A_138,'#skF_6'(A_138),C_148)
      | ~ m1_subset_1(C_148,u1_struct_0(A_138))
      | v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_782,plain,(
    ! [A_422,B_423] :
      ( ~ m1_subset_1('#skF_2'(A_422,B_423,k1_xboole_0),u1_struct_0(A_422))
      | v1_compts_1(A_422)
      | ~ m2_yellow_6(B_423,A_422,'#skF_6'(A_422))
      | ~ l1_waybel_0('#skF_6'(A_422),A_422)
      | ~ v7_waybel_0('#skF_6'(A_422))
      | ~ v4_orders_2('#skF_6'(A_422))
      | v2_struct_0('#skF_6'(A_422))
      | k10_yellow_6(A_422,B_423) = k1_xboole_0
      | ~ l1_waybel_0(B_423,A_422)
      | ~ v7_waybel_0(B_423)
      | ~ v4_orders_2(B_423)
      | v2_struct_0(B_423)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422)
      | v2_struct_0(A_422) ) ),
    inference(resolution,[status(thm)],[c_773,c_54])).

tff(c_786,plain,(
    ! [A_9,B_53] :
      ( v1_compts_1(A_9)
      | ~ m2_yellow_6(B_53,A_9,'#skF_6'(A_9))
      | ~ l1_waybel_0('#skF_6'(A_9),A_9)
      | ~ v7_waybel_0('#skF_6'(A_9))
      | ~ v4_orders_2('#skF_6'(A_9))
      | v2_struct_0('#skF_6'(A_9))
      | k10_yellow_6(A_9,B_53) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_9)))
      | ~ l1_waybel_0(B_53,A_9)
      | ~ v7_waybel_0(B_53)
      | ~ v4_orders_2(B_53)
      | v2_struct_0(B_53)
      | ~ l1_pre_topc(A_9)
      | ~ v2_pre_topc(A_9)
      | v2_struct_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_782])).

tff(c_790,plain,(
    ! [A_424,B_425] :
      ( v1_compts_1(A_424)
      | ~ m2_yellow_6(B_425,A_424,'#skF_6'(A_424))
      | ~ l1_waybel_0('#skF_6'(A_424),A_424)
      | ~ v7_waybel_0('#skF_6'(A_424))
      | ~ v4_orders_2('#skF_6'(A_424))
      | v2_struct_0('#skF_6'(A_424))
      | k10_yellow_6(A_424,B_425) = k1_xboole_0
      | ~ l1_waybel_0(B_425,A_424)
      | ~ v7_waybel_0(B_425)
      | ~ v4_orders_2(B_425)
      | v2_struct_0(B_425)
      | ~ l1_pre_topc(A_424)
      | ~ v2_pre_topc(A_424)
      | v2_struct_0(A_424) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_786])).

tff(c_798,plain,
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
    inference(resolution,[status(thm)],[c_129,c_790])).

tff(c_802,plain,
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
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_798])).

tff(c_803,plain,
    ( k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_802])).

tff(c_804,plain,(
    ~ v4_orders_2('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_803])).

tff(c_814,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_804])).

tff(c_817,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_814])).

tff(c_819,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_817])).

tff(c_821,plain,(
    v4_orders_2('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_803])).

tff(c_58,plain,(
    ! [A_138] :
      ( v7_waybel_0('#skF_6'(A_138))
      | v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_56,plain,(
    ! [A_138] :
      ( l1_waybel_0('#skF_6'(A_138),A_138)
      | v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_10,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_133,plain,(
    ! [C_177,A_178,B_179] :
      ( ~ v2_struct_0(C_177)
      | ~ m2_yellow_6(C_177,A_178,B_179)
      | ~ l1_waybel_0(B_179,A_178)
      | ~ v7_waybel_0(B_179)
      | ~ v4_orders_2(B_179)
      | v2_struct_0(B_179)
      | ~ l1_struct_0(A_178)
      | v2_struct_0(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_136,plain,(
    ! [B_157] :
      ( ~ v2_struct_0('#skF_9'(B_157))
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(resolution,[status(thm)],[c_129,c_133])).

tff(c_139,plain,(
    ! [B_157] :
      ( ~ v2_struct_0('#skF_9'(B_157))
      | ~ l1_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_136])).

tff(c_140,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_150,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_140])).

tff(c_154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_150])).

tff(c_156,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_176,plain,(
    ! [C_192,A_193,B_194] :
      ( l1_waybel_0(C_192,A_193)
      | ~ m2_yellow_6(C_192,A_193,B_194)
      | ~ l1_waybel_0(B_194,A_193)
      | ~ v7_waybel_0(B_194)
      | ~ v4_orders_2(B_194)
      | v2_struct_0(B_194)
      | ~ l1_struct_0(A_193)
      | v2_struct_0(A_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_179,plain,(
    ! [B_157] :
      ( l1_waybel_0('#skF_9'(B_157),'#skF_7')
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(resolution,[status(thm)],[c_129,c_176])).

tff(c_182,plain,(
    ! [B_157] :
      ( l1_waybel_0('#skF_9'(B_157),'#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_179])).

tff(c_183,plain,(
    ! [B_157] :
      ( l1_waybel_0('#skF_9'(B_157),'#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_182])).

tff(c_820,plain,
    ( ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7')
    | v2_struct_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_803])).

tff(c_822,plain,(
    ~ l1_waybel_0('#skF_9'('#skF_6'('#skF_7')),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_820])).

tff(c_825,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_183,c_822])).

tff(c_828,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_825])).

tff(c_829,plain,(
    ~ v7_waybel_0('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_828])).

tff(c_832,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_829])).

tff(c_835,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_832])).

tff(c_837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_835])).

tff(c_838,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_828])).

tff(c_840,plain,(
    ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_838])).

tff(c_843,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_840])).

tff(c_846,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_843])).

tff(c_848,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_846])).

tff(c_849,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_838])).

tff(c_62,plain,(
    ! [A_138] :
      ( ~ v2_struct_0('#skF_6'(A_138))
      | v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_860,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_849,c_62])).

tff(c_863,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_860])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_863])).

tff(c_866,plain,
    ( ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_820])).

tff(c_868,plain,(
    ~ v7_waybel_0('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_866])).

tff(c_871,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_868])).

tff(c_874,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_871])).

tff(c_876,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_874])).

tff(c_878,plain,(
    v7_waybel_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_866])).

tff(c_158,plain,(
    ! [C_184,A_185,B_186] :
      ( v7_waybel_0(C_184)
      | ~ m2_yellow_6(C_184,A_185,B_186)
      | ~ l1_waybel_0(B_186,A_185)
      | ~ v7_waybel_0(B_186)
      | ~ v4_orders_2(B_186)
      | v2_struct_0(B_186)
      | ~ l1_struct_0(A_185)
      | v2_struct_0(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_161,plain,(
    ! [B_157] :
      ( v7_waybel_0('#skF_9'(B_157))
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(resolution,[status(thm)],[c_129,c_158])).

tff(c_164,plain,(
    ! [B_157] :
      ( v7_waybel_0('#skF_9'(B_157))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_161])).

tff(c_165,plain,(
    ! [B_157] :
      ( v7_waybel_0('#skF_9'(B_157))
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_164])).

tff(c_877,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_866])).

tff(c_879,plain,(
    ~ v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_877])).

tff(c_882,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_165,c_879])).

tff(c_885,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_878,c_882])).

tff(c_886,plain,(
    ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_885])).

tff(c_889,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_886])).

tff(c_892,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_889])).

tff(c_894,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_892])).

tff(c_895,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_885])).

tff(c_906,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_895,c_62])).

tff(c_909,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_906])).

tff(c_911,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_909])).

tff(c_912,plain,
    ( ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_877])).

tff(c_914,plain,(
    ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_912])).

tff(c_917,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_914])).

tff(c_920,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_917])).

tff(c_922,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_920])).

tff(c_924,plain,(
    l1_waybel_0('#skF_6'('#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_912])).

tff(c_167,plain,(
    ! [C_188,A_189,B_190] :
      ( v4_orders_2(C_188)
      | ~ m2_yellow_6(C_188,A_189,B_190)
      | ~ l1_waybel_0(B_190,A_189)
      | ~ v7_waybel_0(B_190)
      | ~ v4_orders_2(B_190)
      | v2_struct_0(B_190)
      | ~ l1_struct_0(A_189)
      | v2_struct_0(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_170,plain,(
    ! [B_157] :
      ( v4_orders_2('#skF_9'(B_157))
      | ~ l1_struct_0('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(resolution,[status(thm)],[c_129,c_167])).

tff(c_173,plain,(
    ! [B_157] :
      ( v4_orders_2('#skF_9'(B_157))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_170])).

tff(c_174,plain,(
    ! [B_157] :
      ( v4_orders_2('#skF_9'(B_157))
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_173])).

tff(c_923,plain,
    ( ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_912])).

tff(c_925,plain,(
    ~ v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitLeft,[status(thm)],[c_923])).

tff(c_928,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_174,c_925])).

tff(c_931,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_878,c_924,c_928])).

tff(c_934,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_931,c_62])).

tff(c_937,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_934])).

tff(c_939,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_937])).

tff(c_940,plain,
    ( k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0
    | v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_923])).

tff(c_949,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_940])).

tff(c_952,plain,
    ( v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_949,c_62])).

tff(c_955,plain,
    ( v1_compts_1('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_952])).

tff(c_957,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_110,c_955])).

tff(c_959,plain,(
    ~ v2_struct_0('#skF_6'('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_958,plain,
    ( v2_struct_0('#skF_9'('#skF_6'('#skF_7')))
    | k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_960,plain,(
    k10_yellow_6('#skF_7','#skF_9'('#skF_6'('#skF_7'))) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_96,plain,(
    ! [B_157] :
      ( v1_compts_1('#skF_7')
      | v3_yellow_6('#skF_9'(B_157),'#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_126,plain,(
    ! [B_157] :
      ( v3_yellow_6('#skF_9'(B_157),'#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_96])).

tff(c_189,plain,(
    ! [A_198,B_199] :
      ( k10_yellow_6(A_198,B_199) != k1_xboole_0
      | ~ v3_yellow_6(B_199,A_198)
      | ~ l1_waybel_0(B_199,A_198)
      | ~ v7_waybel_0(B_199)
      | ~ v4_orders_2(B_199)
      | v2_struct_0(B_199)
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | v2_struct_0(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_192,plain,(
    ! [B_157] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_157)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_9'(B_157),'#skF_7')
      | ~ v7_waybel_0('#skF_9'(B_157))
      | ~ v4_orders_2('#skF_9'(B_157))
      | v2_struct_0('#skF_9'(B_157))
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(resolution,[status(thm)],[c_126,c_189])).

tff(c_195,plain,(
    ! [B_157] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_157)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_9'(B_157),'#skF_7')
      | ~ v7_waybel_0('#skF_9'(B_157))
      | ~ v4_orders_2('#skF_9'(B_157))
      | v2_struct_0('#skF_9'(B_157))
      | v2_struct_0('#skF_7')
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_192])).

tff(c_197,plain,(
    ! [B_200] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_200)) != k1_xboole_0
      | ~ l1_waybel_0('#skF_9'(B_200),'#skF_7')
      | ~ v7_waybel_0('#skF_9'(B_200))
      | ~ v4_orders_2('#skF_9'(B_200))
      | v2_struct_0('#skF_9'(B_200))
      | ~ l1_waybel_0(B_200,'#skF_7')
      | ~ v7_waybel_0(B_200)
      | ~ v4_orders_2(B_200)
      | v2_struct_0(B_200) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_195])).

tff(c_214,plain,(
    ! [B_207] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_207)) != k1_xboole_0
      | ~ v7_waybel_0('#skF_9'(B_207))
      | ~ v4_orders_2('#skF_9'(B_207))
      | v2_struct_0('#skF_9'(B_207))
      | ~ l1_waybel_0(B_207,'#skF_7')
      | ~ v7_waybel_0(B_207)
      | ~ v4_orders_2(B_207)
      | v2_struct_0(B_207) ) ),
    inference(resolution,[status(thm)],[c_183,c_197])).

tff(c_219,plain,(
    ! [B_208] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_208)) != k1_xboole_0
      | ~ v4_orders_2('#skF_9'(B_208))
      | v2_struct_0('#skF_9'(B_208))
      | ~ l1_waybel_0(B_208,'#skF_7')
      | ~ v7_waybel_0(B_208)
      | ~ v4_orders_2(B_208)
      | v2_struct_0(B_208) ) ),
    inference(resolution,[status(thm)],[c_165,c_214])).

tff(c_225,plain,(
    ! [B_212] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_212)) != k1_xboole_0
      | v2_struct_0('#skF_9'(B_212))
      | ~ l1_waybel_0(B_212,'#skF_7')
      | ~ v7_waybel_0(B_212)
      | ~ v4_orders_2(B_212)
      | v2_struct_0(B_212) ) ),
    inference(resolution,[status(thm)],[c_174,c_219])).

tff(c_155,plain,(
    ! [B_157] :
      ( ~ v2_struct_0('#skF_9'(B_157))
      | ~ l1_waybel_0(B_157,'#skF_7')
      | ~ v7_waybel_0(B_157)
      | ~ v4_orders_2(B_157)
      | v2_struct_0(B_157) ) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_229,plain,(
    ! [B_212] :
      ( k10_yellow_6('#skF_7','#skF_9'(B_212)) != k1_xboole_0
      | ~ l1_waybel_0(B_212,'#skF_7')
      | ~ v7_waybel_0(B_212)
      | ~ v4_orders_2(B_212)
      | v2_struct_0(B_212) ) ),
    inference(resolution,[status(thm)],[c_225,c_155])).

tff(c_1005,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_229])).

tff(c_1061,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_878,c_924,c_1005])).

tff(c_1063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_959,c_1061])).

tff(c_1064,plain,(
    v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_1068,plain,
    ( ~ l1_waybel_0('#skF_6'('#skF_7'),'#skF_7')
    | ~ v7_waybel_0('#skF_6'('#skF_7'))
    | ~ v4_orders_2('#skF_6'('#skF_7'))
    | v2_struct_0('#skF_6'('#skF_7')) ),
    inference(resolution,[status(thm)],[c_1064,c_155])).

tff(c_1071,plain,(
    v2_struct_0('#skF_6'('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_878,c_924,c_1068])).

tff(c_1073,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_959,c_1071])).

tff(c_1074,plain,(
    ~ v2_struct_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1075,plain,(
    v1_compts_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_80,plain,
    ( v4_orders_2('#skF_8')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_1077,plain,(
    v4_orders_2('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_80])).

tff(c_78,plain,
    ( v7_waybel_0('#skF_8')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_1080,plain,(
    v7_waybel_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_78])).

tff(c_76,plain,
    ( l1_waybel_0('#skF_8','#skF_7')
    | ~ v1_compts_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_1083,plain,(
    l1_waybel_0('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_76])).

tff(c_64,plain,(
    ! [A_138,B_145] :
      ( r3_waybel_9(A_138,B_145,'#skF_5'(A_138,B_145))
      | ~ l1_waybel_0(B_145,A_138)
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_66,plain,(
    ! [A_138,B_145] :
      ( m1_subset_1('#skF_5'(A_138,B_145),u1_struct_0(A_138))
      | ~ l1_waybel_0(B_145,A_138)
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_246])).

tff(c_1129,plain,(
    ! [A_486,B_487,C_488] :
      ( m2_yellow_6('#skF_4'(A_486,B_487,C_488),A_486,B_487)
      | ~ r3_waybel_9(A_486,B_487,C_488)
      | ~ m1_subset_1(C_488,u1_struct_0(A_486))
      | ~ l1_waybel_0(B_487,A_486)
      | ~ v7_waybel_0(B_487)
      | ~ v4_orders_2(B_487)
      | v2_struct_0(B_487)
      | ~ l1_pre_topc(A_486)
      | ~ v2_pre_topc(A_486)
      | v2_struct_0(A_486) ) ),
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

tff(c_1213,plain,(
    ! [A_513,B_514,C_515] :
      ( l1_waybel_0('#skF_4'(A_513,B_514,C_515),A_513)
      | ~ l1_struct_0(A_513)
      | ~ r3_waybel_9(A_513,B_514,C_515)
      | ~ m1_subset_1(C_515,u1_struct_0(A_513))
      | ~ l1_waybel_0(B_514,A_513)
      | ~ v7_waybel_0(B_514)
      | ~ v4_orders_2(B_514)
      | v2_struct_0(B_514)
      | ~ l1_pre_topc(A_513)
      | ~ v2_pre_topc(A_513)
      | v2_struct_0(A_513) ) ),
    inference(resolution,[status(thm)],[c_1129,c_34])).

tff(c_1268,plain,(
    ! [A_560,B_561,B_562] :
      ( l1_waybel_0('#skF_4'(A_560,B_561,'#skF_5'(A_560,B_562)),A_560)
      | ~ l1_struct_0(A_560)
      | ~ r3_waybel_9(A_560,B_561,'#skF_5'(A_560,B_562))
      | ~ l1_waybel_0(B_561,A_560)
      | ~ v7_waybel_0(B_561)
      | ~ v4_orders_2(B_561)
      | v2_struct_0(B_561)
      | ~ l1_waybel_0(B_562,A_560)
      | ~ v7_waybel_0(B_562)
      | ~ v4_orders_2(B_562)
      | v2_struct_0(B_562)
      | ~ v1_compts_1(A_560)
      | ~ l1_pre_topc(A_560)
      | ~ v2_pre_topc(A_560)
      | v2_struct_0(A_560) ) ),
    inference(resolution,[status(thm)],[c_66,c_1213])).

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

tff(c_74,plain,(
    ! [C_156] :
      ( ~ v3_yellow_6(C_156,'#skF_7')
      | ~ m2_yellow_6(C_156,'#skF_7','#skF_8')
      | ~ v1_compts_1('#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_1085,plain,(
    ! [C_156] :
      ( ~ v3_yellow_6(C_156,'#skF_7')
      | ~ m2_yellow_6(C_156,'#skF_7','#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1075,c_74])).

tff(c_1145,plain,(
    ! [C_488] :
      ( ~ v3_yellow_6('#skF_4'('#skF_7','#skF_8',C_488),'#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8',C_488)
      | ~ m1_subset_1(C_488,u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1129,c_1085])).

tff(c_1152,plain,(
    ! [C_488] :
      ( ~ v3_yellow_6('#skF_4'('#skF_7','#skF_8',C_488),'#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8',C_488)
      | ~ m1_subset_1(C_488,u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1077,c_1080,c_1083,c_1145])).

tff(c_1154,plain,(
    ! [C_489] :
      ( ~ v3_yellow_6('#skF_4'('#skF_7','#skF_8',C_489),'#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8',C_489)
      | ~ m1_subset_1(C_489,u1_struct_0('#skF_7')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1074,c_1152])).

tff(c_1157,plain,(
    ! [C_489] :
      ( ~ r3_waybel_9('#skF_7','#skF_8',C_489)
      | ~ m1_subset_1(C_489,u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8',C_489)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8',C_489),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8',C_489))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8',C_489))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8',C_489))
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_1154])).

tff(c_1160,plain,(
    ! [C_489] :
      ( ~ r3_waybel_9('#skF_7','#skF_8',C_489)
      | ~ m1_subset_1(C_489,u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8',C_489)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8',C_489),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8',C_489))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8',C_489))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8',C_489))
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1157])).

tff(c_1195,plain,(
    ! [C_509] :
      ( ~ r3_waybel_9('#skF_7','#skF_8',C_509)
      | ~ m1_subset_1(C_509,u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8',C_509)) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8',C_509),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8',C_509))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8',C_509))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8',C_509)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1160])).

tff(c_1203,plain,(
    ! [B_145] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1195])).

tff(c_1210,plain,(
    ! [B_145] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1075,c_1203])).

tff(c_1211,plain,(
    ! [B_145] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))) = k1_xboole_0
      | ~ l1_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)),'#skF_7')
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1210])).

tff(c_1272,plain,(
    ! [B_562] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_562))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_562,'#skF_7')
      | ~ v7_waybel_0(B_562)
      | ~ v4_orders_2(B_562)
      | v2_struct_0(B_562)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1268,c_1211])).

tff(c_1275,plain,(
    ! [B_562] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_562))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_562,'#skF_7')
      | ~ v7_waybel_0(B_562)
      | ~ v4_orders_2(B_562)
      | v2_struct_0(B_562)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1075,c_1077,c_1080,c_1083,c_1272])).

tff(c_1276,plain,(
    ! [B_562] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_562)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_562))
      | ~ l1_waybel_0(B_562,'#skF_7')
      | ~ v7_waybel_0(B_562)
      | ~ v4_orders_2(B_562)
      | v2_struct_0(B_562) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1074,c_1275])).

tff(c_1277,plain,(
    ~ l1_struct_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1276])).

tff(c_1280,plain,(
    ~ l1_pre_topc('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_1277])).

tff(c_1284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1280])).

tff(c_1286,plain,(
    l1_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1276])).

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

tff(c_1162,plain,(
    ! [A_490,B_491,C_492] :
      ( v4_orders_2('#skF_4'(A_490,B_491,C_492))
      | ~ l1_struct_0(A_490)
      | ~ r3_waybel_9(A_490,B_491,C_492)
      | ~ m1_subset_1(C_492,u1_struct_0(A_490))
      | ~ l1_waybel_0(B_491,A_490)
      | ~ v7_waybel_0(B_491)
      | ~ v4_orders_2(B_491)
      | v2_struct_0(B_491)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(resolution,[status(thm)],[c_1129,c_38])).

tff(c_1165,plain,(
    ! [A_138,B_491,B_145] :
      ( v4_orders_2('#skF_4'(A_138,B_491,'#skF_5'(A_138,B_145)))
      | ~ l1_struct_0(A_138)
      | ~ r3_waybel_9(A_138,B_491,'#skF_5'(A_138,B_145))
      | ~ l1_waybel_0(B_491,A_138)
      | ~ v7_waybel_0(B_491)
      | ~ v4_orders_2(B_491)
      | v2_struct_0(B_491)
      | ~ l1_waybel_0(B_145,A_138)
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_66,c_1162])).

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

tff(c_1171,plain,(
    ! [A_500,B_501,C_502] :
      ( v7_waybel_0('#skF_4'(A_500,B_501,C_502))
      | ~ l1_struct_0(A_500)
      | ~ r3_waybel_9(A_500,B_501,C_502)
      | ~ m1_subset_1(C_502,u1_struct_0(A_500))
      | ~ l1_waybel_0(B_501,A_500)
      | ~ v7_waybel_0(B_501)
      | ~ v4_orders_2(B_501)
      | v2_struct_0(B_501)
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(resolution,[status(thm)],[c_1129,c_36])).

tff(c_1174,plain,(
    ! [A_138,B_501,B_145] :
      ( v7_waybel_0('#skF_4'(A_138,B_501,'#skF_5'(A_138,B_145)))
      | ~ l1_struct_0(A_138)
      | ~ r3_waybel_9(A_138,B_501,'#skF_5'(A_138,B_145))
      | ~ l1_waybel_0(B_501,A_138)
      | ~ v7_waybel_0(B_501)
      | ~ v4_orders_2(B_501)
      | v2_struct_0(B_501)
      | ~ l1_waybel_0(B_145,A_138)
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ v1_compts_1(A_138)
      | ~ l1_pre_topc(A_138)
      | ~ v2_pre_topc(A_138)
      | v2_struct_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_66,c_1171])).

tff(c_1288,plain,(
    ! [B_565] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_565))) = k1_xboole_0
      | ~ v7_waybel_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_565)))
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_565)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_565)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_565))
      | ~ l1_waybel_0(B_565,'#skF_7')
      | ~ v7_waybel_0(B_565)
      | ~ v4_orders_2(B_565)
      | v2_struct_0(B_565) ) ),
    inference(splitRight,[status(thm)],[c_1276])).

tff(c_1292,plain,(
    ! [B_145] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1174,c_1288])).

tff(c_1295,plain,(
    ! [B_145] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1075,c_1077,c_1080,c_1083,c_1286,c_1292])).

tff(c_1297,plain,(
    ! [B_566] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_566))) = k1_xboole_0
      | ~ v4_orders_2('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_566)))
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_566)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_566))
      | ~ l1_waybel_0(B_566,'#skF_7')
      | ~ v7_waybel_0(B_566)
      | ~ v4_orders_2(B_566)
      | v2_struct_0(B_566) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1074,c_1295])).

tff(c_1301,plain,(
    ! [B_145] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ l1_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1165,c_1297])).

tff(c_1304,plain,(
    ! [B_145] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | v2_struct_0('#skF_8')
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1075,c_1077,c_1080,c_1083,c_1286,c_1301])).

tff(c_1306,plain,(
    ! [B_567] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_567))) = k1_xboole_0
      | v2_struct_0('#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_567)))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_567))
      | ~ l1_waybel_0(B_567,'#skF_7')
      | ~ v7_waybel_0(B_567)
      | ~ v4_orders_2(B_567)
      | v2_struct_0(B_567) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1074,c_1304])).

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

tff(c_1148,plain,(
    ! [A_486,B_487,C_488] :
      ( ~ v2_struct_0('#skF_4'(A_486,B_487,C_488))
      | ~ l1_struct_0(A_486)
      | ~ r3_waybel_9(A_486,B_487,C_488)
      | ~ m1_subset_1(C_488,u1_struct_0(A_486))
      | ~ l1_waybel_0(B_487,A_486)
      | ~ v7_waybel_0(B_487)
      | ~ v4_orders_2(B_487)
      | v2_struct_0(B_487)
      | ~ l1_pre_topc(A_486)
      | ~ v2_pre_topc(A_486)
      | v2_struct_0(A_486) ) ),
    inference(resolution,[status(thm)],[c_1129,c_40])).

tff(c_1308,plain,(
    ! [B_567] :
      ( ~ l1_struct_0('#skF_7')
      | ~ m1_subset_1('#skF_5'('#skF_7',B_567),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_567))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_567))
      | ~ l1_waybel_0(B_567,'#skF_7')
      | ~ v7_waybel_0(B_567)
      | ~ v4_orders_2(B_567)
      | v2_struct_0(B_567) ) ),
    inference(resolution,[status(thm)],[c_1306,c_1148])).

tff(c_1311,plain,(
    ! [B_567] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_567),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7')
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_567))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_567))
      | ~ l1_waybel_0(B_567,'#skF_7')
      | ~ v7_waybel_0(B_567)
      | ~ v4_orders_2(B_567)
      | v2_struct_0(B_567) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1077,c_1080,c_1083,c_1286,c_1308])).

tff(c_1313,plain,(
    ! [B_568] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_568),u1_struct_0('#skF_7'))
      | k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_568))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_568))
      | ~ l1_waybel_0(B_568,'#skF_7')
      | ~ v7_waybel_0(B_568)
      | ~ v4_orders_2(B_568)
      | v2_struct_0(B_568) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1074,c_1311])).

tff(c_1317,plain,(
    ! [B_145] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1313])).

tff(c_1320,plain,(
    ! [B_145] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1075,c_1317])).

tff(c_1326,plain,(
    ! [B_572] :
      ( k10_yellow_6('#skF_7','#skF_4'('#skF_7','#skF_8','#skF_5'('#skF_7',B_572))) = k1_xboole_0
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_572))
      | ~ l1_waybel_0(B_572,'#skF_7')
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1320])).

tff(c_1175,plain,(
    ! [C_503,A_504,B_505] :
      ( r2_hidden(C_503,k10_yellow_6(A_504,'#skF_4'(A_504,B_505,C_503)))
      | ~ r3_waybel_9(A_504,B_505,C_503)
      | ~ m1_subset_1(C_503,u1_struct_0(A_504))
      | ~ l1_waybel_0(B_505,A_504)
      | ~ v7_waybel_0(B_505)
      | ~ v4_orders_2(B_505)
      | v2_struct_0(B_505)
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_1187,plain,(
    ! [A_504,B_505,C_503] :
      ( ~ r1_tarski(k10_yellow_6(A_504,'#skF_4'(A_504,B_505,C_503)),C_503)
      | ~ r3_waybel_9(A_504,B_505,C_503)
      | ~ m1_subset_1(C_503,u1_struct_0(A_504))
      | ~ l1_waybel_0(B_505,A_504)
      | ~ v7_waybel_0(B_505)
      | ~ v4_orders_2(B_505)
      | v2_struct_0(B_505)
      | ~ l1_pre_topc(A_504)
      | ~ v2_pre_topc(A_504)
      | v2_struct_0(A_504) ) ),
    inference(resolution,[status(thm)],[c_1175,c_8])).

tff(c_1337,plain,(
    ! [B_572] :
      ( ~ r1_tarski(k1_xboole_0,'#skF_5'('#skF_7',B_572))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_572))
      | ~ m1_subset_1('#skF_5'('#skF_7',B_572),u1_struct_0('#skF_7'))
      | ~ l1_waybel_0('#skF_8','#skF_7')
      | ~ v7_waybel_0('#skF_8')
      | ~ v4_orders_2('#skF_8')
      | v2_struct_0('#skF_8')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_572))
      | ~ l1_waybel_0(B_572,'#skF_7')
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1326,c_1187])).

tff(c_1361,plain,(
    ! [B_572] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_572),u1_struct_0('#skF_7'))
      | v2_struct_0('#skF_8')
      | v2_struct_0('#skF_7')
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_572))
      | ~ l1_waybel_0(B_572,'#skF_7')
      | ~ v7_waybel_0(B_572)
      | ~ v4_orders_2(B_572)
      | v2_struct_0(B_572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1077,c_1080,c_1083,c_2,c_1337])).

tff(c_1376,plain,(
    ! [B_573] :
      ( ~ m1_subset_1('#skF_5'('#skF_7',B_573),u1_struct_0('#skF_7'))
      | ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_573))
      | ~ l1_waybel_0(B_573,'#skF_7')
      | ~ v7_waybel_0(B_573)
      | ~ v4_orders_2(B_573)
      | v2_struct_0(B_573) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1074,c_1361])).

tff(c_1380,plain,(
    ! [B_145] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ v1_compts_1('#skF_7')
      | ~ l1_pre_topc('#skF_7')
      | ~ v2_pre_topc('#skF_7')
      | v2_struct_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_66,c_1376])).

tff(c_1383,plain,(
    ! [B_145] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_145))
      | ~ l1_waybel_0(B_145,'#skF_7')
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | v2_struct_0('#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1075,c_1380])).

tff(c_1385,plain,(
    ! [B_574] :
      ( ~ r3_waybel_9('#skF_7','#skF_8','#skF_5'('#skF_7',B_574))
      | ~ l1_waybel_0(B_574,'#skF_7')
      | ~ v7_waybel_0(B_574)
      | ~ v4_orders_2(B_574)
      | v2_struct_0(B_574) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1383])).

tff(c_1393,plain,
    ( ~ l1_waybel_0('#skF_8','#skF_7')
    | ~ v7_waybel_0('#skF_8')
    | ~ v4_orders_2('#skF_8')
    | v2_struct_0('#skF_8')
    | ~ v1_compts_1('#skF_7')
    | ~ l1_pre_topc('#skF_7')
    | ~ v2_pre_topc('#skF_7')
    | v2_struct_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_1385])).

tff(c_1400,plain,
    ( v2_struct_0('#skF_8')
    | v2_struct_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1075,c_1077,c_1080,c_1083,c_1393])).

tff(c_1402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1074,c_1400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.22  
% 6.06/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.22  %$ r3_waybel_9 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > v3_yellow_6 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > v1_compts_1 > l1_struct_0 > l1_pre_topc > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_9 > #skF_4 > #skF_7 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_6
% 6.06/2.22  
% 6.06/2.22  %Foreground sorts:
% 6.06/2.22  
% 6.06/2.22  
% 6.06/2.22  %Background operators:
% 6.06/2.22  
% 6.06/2.22  
% 6.06/2.22  %Foreground operators:
% 6.06/2.22  tff('#skF_9', type, '#skF_9': $i > $i).
% 6.06/2.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.06/2.22  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 6.06/2.22  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 6.06/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.06/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.06/2.22  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 6.06/2.22  tff(v3_yellow_6, type, v3_yellow_6: ($i * $i) > $o).
% 6.06/2.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.06/2.22  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 6.06/2.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.06/2.22  tff('#skF_7', type, '#skF_7': $i).
% 6.06/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.22  tff(r3_waybel_9, type, r3_waybel_9: ($i * $i * $i) > $o).
% 6.06/2.22  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 6.06/2.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.06/2.22  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.06/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.06/2.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.06/2.22  tff('#skF_8', type, '#skF_8': $i).
% 6.06/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.22  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 6.06/2.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.06/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.06/2.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.06/2.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.06/2.22  tff(v1_compts_1, type, v1_compts_1: $i > $o).
% 6.06/2.22  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.06/2.22  tff('#skF_6', type, '#skF_6': $i > $i).
% 6.06/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.06/2.22  
% 6.06/2.26  tff(f_271, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m2_yellow_6(C, A, B) & v3_yellow_6(C, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_yellow19)).
% 6.06/2.26  tff(f_246, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (v1_compts_1(A) <=> (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (?[C]: (m1_subset_1(C, u1_struct_0(A)) & r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_yellow19)).
% 6.06/2.26  tff(f_29, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.06/2.26  tff(f_76, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 6.06/2.26  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.06/2.26  tff(f_94, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 6.06/2.26  tff(f_40, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.06/2.26  tff(f_166, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_hidden(C, k10_yellow_6(A, B)) => r3_waybel_9(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_waybel_9)).
% 6.06/2.26  tff(f_193, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r3_waybel_9(A, C, D) => r3_waybel_9(A, B, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_waybel_9)).
% 6.06/2.26  tff(f_44, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.06/2.26  tff(f_120, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 6.06/2.26  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (v3_yellow_6(B, A) <=> ~(k10_yellow_6(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_yellow_6)).
% 6.06/2.26  tff(f_222, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r3_waybel_9(A, B, C) & (![D]: (m2_yellow_6(D, A, B) => ~r2_hidden(C, k10_yellow_6(A, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_waybel_9)).
% 6.06/2.26  tff(c_72, plain, (~v2_struct_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_82, plain, (~v2_struct_0('#skF_8') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_110, plain, (~v1_compts_1('#skF_7')), inference(splitLeft, [status(thm)], [c_82])).
% 6.06/2.26  tff(c_70, plain, (v2_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_68, plain, (l1_pre_topc('#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_60, plain, (![A_138]: (v4_orders_2('#skF_6'(A_138)) | v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.06/2.26  tff(c_108, plain, (![B_157]: (v1_compts_1('#skF_7') | m2_yellow_6('#skF_9'(B_157), '#skF_7', B_157) | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_129, plain, (![B_157]: (m2_yellow_6('#skF_9'(B_157), '#skF_7', B_157) | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(negUnitSimplification, [status(thm)], [c_110, c_108])).
% 6.06/2.26  tff(c_4, plain, (![A_2]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.06/2.26  tff(c_12, plain, (![A_9, B_53, C_75]: (m1_subset_1('#skF_2'(A_9, B_53, C_75), u1_struct_0(A_9)) | k10_yellow_6(A_9, B_53)=C_75 | ~m1_subset_1(C_75, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.06/2.26  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.06/2.26  tff(c_32, plain, (![A_93, B_94]: (m1_subset_1(k10_yellow_6(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.06/2.26  tff(c_297, plain, (![A_258, B_259, D_260]: (m1_connsp_2('#skF_1'(A_258, B_259, k10_yellow_6(A_258, B_259), D_260), A_258, D_260) | r2_hidden(D_260, k10_yellow_6(A_258, B_259)) | ~m1_subset_1(D_260, u1_struct_0(A_258)) | ~m1_subset_1(k10_yellow_6(A_258, B_259), k1_zfmisc_1(u1_struct_0(A_258))) | ~l1_waybel_0(B_259, A_258) | ~v7_waybel_0(B_259) | ~v4_orders_2(B_259) | v2_struct_0(B_259) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.06/2.26  tff(c_300, plain, (![A_93, B_94, D_260]: (m1_connsp_2('#skF_1'(A_93, B_94, k10_yellow_6(A_93, B_94), D_260), A_93, D_260) | r2_hidden(D_260, k10_yellow_6(A_93, B_94)) | ~m1_subset_1(D_260, u1_struct_0(A_93)) | ~l1_waybel_0(B_94, A_93) | ~v7_waybel_0(B_94) | ~v4_orders_2(B_94) | v2_struct_0(B_94) | ~l1_pre_topc(A_93) | ~v2_pre_topc(A_93) | v2_struct_0(A_93))), inference(resolution, [status(thm)], [c_32, c_297])).
% 6.06/2.26  tff(c_305, plain, (![A_264, B_265, C_266, E_267]: (r2_hidden('#skF_2'(A_264, B_265, C_266), C_266) | r1_waybel_0(A_264, B_265, E_267) | ~m1_connsp_2(E_267, A_264, '#skF_2'(A_264, B_265, C_266)) | k10_yellow_6(A_264, B_265)=C_266 | ~m1_subset_1(C_266, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_waybel_0(B_265, A_264) | ~v7_waybel_0(B_265) | ~v4_orders_2(B_265) | v2_struct_0(B_265) | ~l1_pre_topc(A_264) | ~v2_pre_topc(A_264) | v2_struct_0(A_264))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.06/2.26  tff(c_406, plain, (![A_351, B_352, C_353, B_354]: (r2_hidden('#skF_2'(A_351, B_352, C_353), C_353) | r1_waybel_0(A_351, B_352, '#skF_1'(A_351, B_354, k10_yellow_6(A_351, B_354), '#skF_2'(A_351, B_352, C_353))) | k10_yellow_6(A_351, B_352)=C_353 | ~m1_subset_1(C_353, k1_zfmisc_1(u1_struct_0(A_351))) | ~l1_waybel_0(B_352, A_351) | ~v7_waybel_0(B_352) | ~v4_orders_2(B_352) | v2_struct_0(B_352) | r2_hidden('#skF_2'(A_351, B_352, C_353), k10_yellow_6(A_351, B_354)) | ~m1_subset_1('#skF_2'(A_351, B_352, C_353), u1_struct_0(A_351)) | ~l1_waybel_0(B_354, A_351) | ~v7_waybel_0(B_354) | ~v4_orders_2(B_354) | v2_struct_0(B_354) | ~l1_pre_topc(A_351) | ~v2_pre_topc(A_351) | v2_struct_0(A_351))), inference(resolution, [status(thm)], [c_300, c_305])).
% 6.06/2.26  tff(c_28, plain, (![A_9, B_53, D_86]: (~r1_waybel_0(A_9, B_53, '#skF_1'(A_9, B_53, k10_yellow_6(A_9, B_53), D_86)) | r2_hidden(D_86, k10_yellow_6(A_9, B_53)) | ~m1_subset_1(D_86, u1_struct_0(A_9)) | ~m1_subset_1(k10_yellow_6(A_9, B_53), k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.06/2.26  tff(c_430, plain, (![A_355, B_356, C_357]: (~m1_subset_1(k10_yellow_6(A_355, B_356), k1_zfmisc_1(u1_struct_0(A_355))) | r2_hidden('#skF_2'(A_355, B_356, C_357), C_357) | k10_yellow_6(A_355, B_356)=C_357 | ~m1_subset_1(C_357, k1_zfmisc_1(u1_struct_0(A_355))) | r2_hidden('#skF_2'(A_355, B_356, C_357), k10_yellow_6(A_355, B_356)) | ~m1_subset_1('#skF_2'(A_355, B_356, C_357), u1_struct_0(A_355)) | ~l1_waybel_0(B_356, A_355) | ~v7_waybel_0(B_356) | ~v4_orders_2(B_356) | v2_struct_0(B_356) | ~l1_pre_topc(A_355) | ~v2_pre_topc(A_355) | v2_struct_0(A_355))), inference(resolution, [status(thm)], [c_406, c_28])).
% 6.06/2.26  tff(c_450, plain, (![A_358, B_359, C_360]: (r2_hidden('#skF_2'(A_358, B_359, C_360), C_360) | k10_yellow_6(A_358, B_359)=C_360 | ~m1_subset_1(C_360, k1_zfmisc_1(u1_struct_0(A_358))) | r2_hidden('#skF_2'(A_358, B_359, C_360), k10_yellow_6(A_358, B_359)) | ~m1_subset_1('#skF_2'(A_358, B_359, C_360), u1_struct_0(A_358)) | ~l1_waybel_0(B_359, A_358) | ~v7_waybel_0(B_359) | ~v4_orders_2(B_359) | v2_struct_0(B_359) | ~l1_pre_topc(A_358) | ~v2_pre_topc(A_358) | v2_struct_0(A_358))), inference(resolution, [status(thm)], [c_32, c_430])).
% 6.06/2.26  tff(c_8, plain, (![B_7, A_6]: (~r1_tarski(B_7, A_6) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.06/2.26  tff(c_674, plain, (![C_391, A_392, B_393]: (~r1_tarski(C_391, '#skF_2'(A_392, B_393, C_391)) | k10_yellow_6(A_392, B_393)=C_391 | ~m1_subset_1(C_391, k1_zfmisc_1(u1_struct_0(A_392))) | r2_hidden('#skF_2'(A_392, B_393, C_391), k10_yellow_6(A_392, B_393)) | ~m1_subset_1('#skF_2'(A_392, B_393, C_391), u1_struct_0(A_392)) | ~l1_waybel_0(B_393, A_392) | ~v7_waybel_0(B_393) | ~v4_orders_2(B_393) | v2_struct_0(B_393) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(resolution, [status(thm)], [c_450, c_8])).
% 6.06/2.26  tff(c_677, plain, (![A_392, B_393]: (k10_yellow_6(A_392, B_393)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_392))) | r2_hidden('#skF_2'(A_392, B_393, k1_xboole_0), k10_yellow_6(A_392, B_393)) | ~m1_subset_1('#skF_2'(A_392, B_393, k1_xboole_0), u1_struct_0(A_392)) | ~l1_waybel_0(B_393, A_392) | ~v7_waybel_0(B_393) | ~v4_orders_2(B_393) | v2_struct_0(B_393) | ~l1_pre_topc(A_392) | ~v2_pre_topc(A_392) | v2_struct_0(A_392))), inference(resolution, [status(thm)], [c_2, c_674])).
% 6.06/2.26  tff(c_684, plain, (![A_397, B_398]: (k10_yellow_6(A_397, B_398)=k1_xboole_0 | r2_hidden('#skF_2'(A_397, B_398, k1_xboole_0), k10_yellow_6(A_397, B_398)) | ~m1_subset_1('#skF_2'(A_397, B_398, k1_xboole_0), u1_struct_0(A_397)) | ~l1_waybel_0(B_398, A_397) | ~v7_waybel_0(B_398) | ~v4_orders_2(B_398) | v2_struct_0(B_398) | ~l1_pre_topc(A_397) | ~v2_pre_topc(A_397) | v2_struct_0(A_397))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_677])).
% 6.06/2.26  tff(c_46, plain, (![A_102, B_106, C_108]: (r3_waybel_9(A_102, B_106, C_108) | ~r2_hidden(C_108, k10_yellow_6(A_102, B_106)) | ~m1_subset_1(C_108, u1_struct_0(A_102)) | ~l1_waybel_0(B_106, A_102) | ~v7_waybel_0(B_106) | ~v4_orders_2(B_106) | v2_struct_0(B_106) | ~l1_pre_topc(A_102) | ~v2_pre_topc(A_102) | v2_struct_0(A_102))), inference(cnfTransformation, [status(thm)], [f_166])).
% 6.06/2.26  tff(c_705, plain, (![A_399, B_400]: (r3_waybel_9(A_399, B_400, '#skF_2'(A_399, B_400, k1_xboole_0)) | k10_yellow_6(A_399, B_400)=k1_xboole_0 | ~m1_subset_1('#skF_2'(A_399, B_400, k1_xboole_0), u1_struct_0(A_399)) | ~l1_waybel_0(B_400, A_399) | ~v7_waybel_0(B_400) | ~v4_orders_2(B_400) | v2_struct_0(B_400) | ~l1_pre_topc(A_399) | ~v2_pre_topc(A_399) | v2_struct_0(A_399))), inference(resolution, [status(thm)], [c_684, c_46])).
% 6.06/2.26  tff(c_708, plain, (![A_9, B_53]: (r3_waybel_9(A_9, B_53, '#skF_2'(A_9, B_53, k1_xboole_0)) | k10_yellow_6(A_9, B_53)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_705])).
% 6.06/2.26  tff(c_712, plain, (![A_401, B_402]: (r3_waybel_9(A_401, B_402, '#skF_2'(A_401, B_402, k1_xboole_0)) | k10_yellow_6(A_401, B_402)=k1_xboole_0 | ~l1_waybel_0(B_402, A_401) | ~v7_waybel_0(B_402) | ~v4_orders_2(B_402) | v2_struct_0(B_402) | ~l1_pre_topc(A_401) | ~v2_pre_topc(A_401) | v2_struct_0(A_401))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_708])).
% 6.06/2.26  tff(c_48, plain, (![A_109, B_117, D_123, C_121]: (r3_waybel_9(A_109, B_117, D_123) | ~r3_waybel_9(A_109, C_121, D_123) | ~m1_subset_1(D_123, u1_struct_0(A_109)) | ~m2_yellow_6(C_121, A_109, B_117) | ~l1_waybel_0(B_117, A_109) | ~v7_waybel_0(B_117) | ~v4_orders_2(B_117) | v2_struct_0(B_117) | ~l1_pre_topc(A_109) | ~v2_pre_topc(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_193])).
% 6.06/2.26  tff(c_766, plain, (![A_416, B_417, B_418]: (r3_waybel_9(A_416, B_417, '#skF_2'(A_416, B_418, k1_xboole_0)) | ~m1_subset_1('#skF_2'(A_416, B_418, k1_xboole_0), u1_struct_0(A_416)) | ~m2_yellow_6(B_418, A_416, B_417) | ~l1_waybel_0(B_417, A_416) | ~v7_waybel_0(B_417) | ~v4_orders_2(B_417) | v2_struct_0(B_417) | k10_yellow_6(A_416, B_418)=k1_xboole_0 | ~l1_waybel_0(B_418, A_416) | ~v7_waybel_0(B_418) | ~v4_orders_2(B_418) | v2_struct_0(B_418) | ~l1_pre_topc(A_416) | ~v2_pre_topc(A_416) | v2_struct_0(A_416))), inference(resolution, [status(thm)], [c_712, c_48])).
% 6.06/2.26  tff(c_769, plain, (![A_9, B_417, B_53]: (r3_waybel_9(A_9, B_417, '#skF_2'(A_9, B_53, k1_xboole_0)) | ~m2_yellow_6(B_53, A_9, B_417) | ~l1_waybel_0(B_417, A_9) | ~v7_waybel_0(B_417) | ~v4_orders_2(B_417) | v2_struct_0(B_417) | k10_yellow_6(A_9, B_53)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_766])).
% 6.06/2.26  tff(c_773, plain, (![A_419, B_420, B_421]: (r3_waybel_9(A_419, B_420, '#skF_2'(A_419, B_421, k1_xboole_0)) | ~m2_yellow_6(B_421, A_419, B_420) | ~l1_waybel_0(B_420, A_419) | ~v7_waybel_0(B_420) | ~v4_orders_2(B_420) | v2_struct_0(B_420) | k10_yellow_6(A_419, B_421)=k1_xboole_0 | ~l1_waybel_0(B_421, A_419) | ~v7_waybel_0(B_421) | ~v4_orders_2(B_421) | v2_struct_0(B_421) | ~l1_pre_topc(A_419) | ~v2_pre_topc(A_419) | v2_struct_0(A_419))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_769])).
% 6.06/2.26  tff(c_54, plain, (![A_138, C_148]: (~r3_waybel_9(A_138, '#skF_6'(A_138), C_148) | ~m1_subset_1(C_148, u1_struct_0(A_138)) | v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.06/2.26  tff(c_782, plain, (![A_422, B_423]: (~m1_subset_1('#skF_2'(A_422, B_423, k1_xboole_0), u1_struct_0(A_422)) | v1_compts_1(A_422) | ~m2_yellow_6(B_423, A_422, '#skF_6'(A_422)) | ~l1_waybel_0('#skF_6'(A_422), A_422) | ~v7_waybel_0('#skF_6'(A_422)) | ~v4_orders_2('#skF_6'(A_422)) | v2_struct_0('#skF_6'(A_422)) | k10_yellow_6(A_422, B_423)=k1_xboole_0 | ~l1_waybel_0(B_423, A_422) | ~v7_waybel_0(B_423) | ~v4_orders_2(B_423) | v2_struct_0(B_423) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422) | v2_struct_0(A_422))), inference(resolution, [status(thm)], [c_773, c_54])).
% 6.06/2.26  tff(c_786, plain, (![A_9, B_53]: (v1_compts_1(A_9) | ~m2_yellow_6(B_53, A_9, '#skF_6'(A_9)) | ~l1_waybel_0('#skF_6'(A_9), A_9) | ~v7_waybel_0('#skF_6'(A_9)) | ~v4_orders_2('#skF_6'(A_9)) | v2_struct_0('#skF_6'(A_9)) | k10_yellow_6(A_9, B_53)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_9))) | ~l1_waybel_0(B_53, A_9) | ~v7_waybel_0(B_53) | ~v4_orders_2(B_53) | v2_struct_0(B_53) | ~l1_pre_topc(A_9) | ~v2_pre_topc(A_9) | v2_struct_0(A_9))), inference(resolution, [status(thm)], [c_12, c_782])).
% 6.06/2.26  tff(c_790, plain, (![A_424, B_425]: (v1_compts_1(A_424) | ~m2_yellow_6(B_425, A_424, '#skF_6'(A_424)) | ~l1_waybel_0('#skF_6'(A_424), A_424) | ~v7_waybel_0('#skF_6'(A_424)) | ~v4_orders_2('#skF_6'(A_424)) | v2_struct_0('#skF_6'(A_424)) | k10_yellow_6(A_424, B_425)=k1_xboole_0 | ~l1_waybel_0(B_425, A_424) | ~v7_waybel_0(B_425) | ~v4_orders_2(B_425) | v2_struct_0(B_425) | ~l1_pre_topc(A_424) | ~v2_pre_topc(A_424) | v2_struct_0(A_424))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_786])).
% 6.06/2.26  tff(c_798, plain, (v1_compts_1('#skF_7') | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_129, c_790])).
% 6.06/2.26  tff(c_802, plain, (v1_compts_1('#skF_7') | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_798])).
% 6.06/2.26  tff(c_803, plain, (k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_802])).
% 6.06/2.26  tff(c_804, plain, (~v4_orders_2('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_803])).
% 6.06/2.26  tff(c_814, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_60, c_804])).
% 6.06/2.26  tff(c_817, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_814])).
% 6.06/2.26  tff(c_819, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_817])).
% 6.06/2.26  tff(c_821, plain, (v4_orders_2('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_803])).
% 6.06/2.26  tff(c_58, plain, (![A_138]: (v7_waybel_0('#skF_6'(A_138)) | v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.06/2.26  tff(c_56, plain, (![A_138]: (l1_waybel_0('#skF_6'(A_138), A_138) | v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.06/2.26  tff(c_10, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.06/2.26  tff(c_133, plain, (![C_177, A_178, B_179]: (~v2_struct_0(C_177) | ~m2_yellow_6(C_177, A_178, B_179) | ~l1_waybel_0(B_179, A_178) | ~v7_waybel_0(B_179) | ~v4_orders_2(B_179) | v2_struct_0(B_179) | ~l1_struct_0(A_178) | v2_struct_0(A_178))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.06/2.26  tff(c_136, plain, (![B_157]: (~v2_struct_0('#skF_9'(B_157)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(resolution, [status(thm)], [c_129, c_133])).
% 6.06/2.26  tff(c_139, plain, (![B_157]: (~v2_struct_0('#skF_9'(B_157)) | ~l1_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(negUnitSimplification, [status(thm)], [c_72, c_136])).
% 6.06/2.26  tff(c_140, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_139])).
% 6.06/2.26  tff(c_150, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_10, c_140])).
% 6.06/2.26  tff(c_154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_150])).
% 6.06/2.26  tff(c_156, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_139])).
% 6.06/2.26  tff(c_176, plain, (![C_192, A_193, B_194]: (l1_waybel_0(C_192, A_193) | ~m2_yellow_6(C_192, A_193, B_194) | ~l1_waybel_0(B_194, A_193) | ~v7_waybel_0(B_194) | ~v4_orders_2(B_194) | v2_struct_0(B_194) | ~l1_struct_0(A_193) | v2_struct_0(A_193))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.06/2.26  tff(c_179, plain, (![B_157]: (l1_waybel_0('#skF_9'(B_157), '#skF_7') | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(resolution, [status(thm)], [c_129, c_176])).
% 6.06/2.26  tff(c_182, plain, (![B_157]: (l1_waybel_0('#skF_9'(B_157), '#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_179])).
% 6.06/2.26  tff(c_183, plain, (![B_157]: (l1_waybel_0('#skF_9'(B_157), '#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(negUnitSimplification, [status(thm)], [c_72, c_182])).
% 6.06/2.26  tff(c_820, plain, (~v7_waybel_0('#skF_6'('#skF_7')) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7') | v2_struct_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_803])).
% 6.06/2.26  tff(c_822, plain, (~l1_waybel_0('#skF_9'('#skF_6'('#skF_7')), '#skF_7')), inference(splitLeft, [status(thm)], [c_820])).
% 6.06/2.26  tff(c_825, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_183, c_822])).
% 6.06/2.26  tff(c_828, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_821, c_825])).
% 6.06/2.26  tff(c_829, plain, (~v7_waybel_0('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_828])).
% 6.06/2.26  tff(c_832, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_58, c_829])).
% 6.06/2.26  tff(c_835, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_832])).
% 6.06/2.26  tff(c_837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_835])).
% 6.06/2.26  tff(c_838, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_828])).
% 6.06/2.26  tff(c_840, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_838])).
% 6.06/2.26  tff(c_843, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_56, c_840])).
% 6.06/2.26  tff(c_846, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_843])).
% 6.06/2.26  tff(c_848, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_846])).
% 6.06/2.26  tff(c_849, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_838])).
% 6.06/2.26  tff(c_62, plain, (![A_138]: (~v2_struct_0('#skF_6'(A_138)) | v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.06/2.26  tff(c_860, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_849, c_62])).
% 6.06/2.26  tff(c_863, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_860])).
% 6.06/2.26  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_863])).
% 6.06/2.26  tff(c_866, plain, (~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_820])).
% 6.06/2.26  tff(c_868, plain, (~v7_waybel_0('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_866])).
% 6.06/2.26  tff(c_871, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_58, c_868])).
% 6.06/2.26  tff(c_874, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_871])).
% 6.06/2.26  tff(c_876, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_874])).
% 6.06/2.26  tff(c_878, plain, (v7_waybel_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_866])).
% 6.06/2.26  tff(c_158, plain, (![C_184, A_185, B_186]: (v7_waybel_0(C_184) | ~m2_yellow_6(C_184, A_185, B_186) | ~l1_waybel_0(B_186, A_185) | ~v7_waybel_0(B_186) | ~v4_orders_2(B_186) | v2_struct_0(B_186) | ~l1_struct_0(A_185) | v2_struct_0(A_185))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.06/2.26  tff(c_161, plain, (![B_157]: (v7_waybel_0('#skF_9'(B_157)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(resolution, [status(thm)], [c_129, c_158])).
% 6.06/2.26  tff(c_164, plain, (![B_157]: (v7_waybel_0('#skF_9'(B_157)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_161])).
% 6.06/2.26  tff(c_165, plain, (![B_157]: (v7_waybel_0('#skF_9'(B_157)) | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(negUnitSimplification, [status(thm)], [c_72, c_164])).
% 6.06/2.26  tff(c_877, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~v7_waybel_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_866])).
% 6.06/2.26  tff(c_879, plain, (~v7_waybel_0('#skF_9'('#skF_6'('#skF_7')))), inference(splitLeft, [status(thm)], [c_877])).
% 6.06/2.26  tff(c_882, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_165, c_879])).
% 6.06/2.26  tff(c_885, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_821, c_878, c_882])).
% 6.06/2.26  tff(c_886, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_885])).
% 6.06/2.26  tff(c_889, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_56, c_886])).
% 6.06/2.26  tff(c_892, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_889])).
% 6.06/2.26  tff(c_894, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_892])).
% 6.06/2.26  tff(c_895, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_885])).
% 6.06/2.26  tff(c_906, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_895, c_62])).
% 6.06/2.26  tff(c_909, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_906])).
% 6.06/2.26  tff(c_911, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_909])).
% 6.06/2.26  tff(c_912, plain, (~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | ~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_877])).
% 6.06/2.26  tff(c_914, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_912])).
% 6.06/2.26  tff(c_917, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_56, c_914])).
% 6.06/2.26  tff(c_920, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_917])).
% 6.06/2.26  tff(c_922, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_920])).
% 6.06/2.26  tff(c_924, plain, (l1_waybel_0('#skF_6'('#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_912])).
% 6.06/2.26  tff(c_167, plain, (![C_188, A_189, B_190]: (v4_orders_2(C_188) | ~m2_yellow_6(C_188, A_189, B_190) | ~l1_waybel_0(B_190, A_189) | ~v7_waybel_0(B_190) | ~v4_orders_2(B_190) | v2_struct_0(B_190) | ~l1_struct_0(A_189) | v2_struct_0(A_189))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.06/2.26  tff(c_170, plain, (![B_157]: (v4_orders_2('#skF_9'(B_157)) | ~l1_struct_0('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(resolution, [status(thm)], [c_129, c_167])).
% 6.06/2.26  tff(c_173, plain, (![B_157]: (v4_orders_2('#skF_9'(B_157)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_170])).
% 6.06/2.26  tff(c_174, plain, (![B_157]: (v4_orders_2('#skF_9'(B_157)) | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(negUnitSimplification, [status(thm)], [c_72, c_173])).
% 6.06/2.26  tff(c_923, plain, (~v4_orders_2('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7')) | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_912])).
% 6.06/2.26  tff(c_925, plain, (~v4_orders_2('#skF_9'('#skF_6'('#skF_7')))), inference(splitLeft, [status(thm)], [c_923])).
% 6.06/2.26  tff(c_928, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_174, c_925])).
% 6.06/2.26  tff(c_931, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_821, c_878, c_924, c_928])).
% 6.06/2.26  tff(c_934, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_931, c_62])).
% 6.06/2.26  tff(c_937, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_934])).
% 6.06/2.26  tff(c_939, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_937])).
% 6.06/2.26  tff(c_940, plain, (k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0 | v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_923])).
% 6.06/2.26  tff(c_949, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(splitLeft, [status(thm)], [c_940])).
% 6.06/2.26  tff(c_952, plain, (v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_949, c_62])).
% 6.06/2.26  tff(c_955, plain, (v1_compts_1('#skF_7') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_952])).
% 6.06/2.26  tff(c_957, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_110, c_955])).
% 6.06/2.26  tff(c_959, plain, (~v2_struct_0('#skF_6'('#skF_7'))), inference(splitRight, [status(thm)], [c_940])).
% 6.06/2.26  tff(c_958, plain, (v2_struct_0('#skF_9'('#skF_6'('#skF_7'))) | k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_940])).
% 6.06/2.26  tff(c_960, plain, (k10_yellow_6('#skF_7', '#skF_9'('#skF_6'('#skF_7')))=k1_xboole_0), inference(splitLeft, [status(thm)], [c_958])).
% 6.06/2.26  tff(c_96, plain, (![B_157]: (v1_compts_1('#skF_7') | v3_yellow_6('#skF_9'(B_157), '#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_126, plain, (![B_157]: (v3_yellow_6('#skF_9'(B_157), '#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(negUnitSimplification, [status(thm)], [c_110, c_96])).
% 6.06/2.26  tff(c_189, plain, (![A_198, B_199]: (k10_yellow_6(A_198, B_199)!=k1_xboole_0 | ~v3_yellow_6(B_199, A_198) | ~l1_waybel_0(B_199, A_198) | ~v7_waybel_0(B_199) | ~v4_orders_2(B_199) | v2_struct_0(B_199) | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198) | v2_struct_0(A_198))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.06/2.26  tff(c_192, plain, (![B_157]: (k10_yellow_6('#skF_7', '#skF_9'(B_157))!=k1_xboole_0 | ~l1_waybel_0('#skF_9'(B_157), '#skF_7') | ~v7_waybel_0('#skF_9'(B_157)) | ~v4_orders_2('#skF_9'(B_157)) | v2_struct_0('#skF_9'(B_157)) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(resolution, [status(thm)], [c_126, c_189])).
% 6.06/2.26  tff(c_195, plain, (![B_157]: (k10_yellow_6('#skF_7', '#skF_9'(B_157))!=k1_xboole_0 | ~l1_waybel_0('#skF_9'(B_157), '#skF_7') | ~v7_waybel_0('#skF_9'(B_157)) | ~v4_orders_2('#skF_9'(B_157)) | v2_struct_0('#skF_9'(B_157)) | v2_struct_0('#skF_7') | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_192])).
% 6.06/2.26  tff(c_197, plain, (![B_200]: (k10_yellow_6('#skF_7', '#skF_9'(B_200))!=k1_xboole_0 | ~l1_waybel_0('#skF_9'(B_200), '#skF_7') | ~v7_waybel_0('#skF_9'(B_200)) | ~v4_orders_2('#skF_9'(B_200)) | v2_struct_0('#skF_9'(B_200)) | ~l1_waybel_0(B_200, '#skF_7') | ~v7_waybel_0(B_200) | ~v4_orders_2(B_200) | v2_struct_0(B_200))), inference(negUnitSimplification, [status(thm)], [c_72, c_195])).
% 6.06/2.26  tff(c_214, plain, (![B_207]: (k10_yellow_6('#skF_7', '#skF_9'(B_207))!=k1_xboole_0 | ~v7_waybel_0('#skF_9'(B_207)) | ~v4_orders_2('#skF_9'(B_207)) | v2_struct_0('#skF_9'(B_207)) | ~l1_waybel_0(B_207, '#skF_7') | ~v7_waybel_0(B_207) | ~v4_orders_2(B_207) | v2_struct_0(B_207))), inference(resolution, [status(thm)], [c_183, c_197])).
% 6.06/2.26  tff(c_219, plain, (![B_208]: (k10_yellow_6('#skF_7', '#skF_9'(B_208))!=k1_xboole_0 | ~v4_orders_2('#skF_9'(B_208)) | v2_struct_0('#skF_9'(B_208)) | ~l1_waybel_0(B_208, '#skF_7') | ~v7_waybel_0(B_208) | ~v4_orders_2(B_208) | v2_struct_0(B_208))), inference(resolution, [status(thm)], [c_165, c_214])).
% 6.06/2.26  tff(c_225, plain, (![B_212]: (k10_yellow_6('#skF_7', '#skF_9'(B_212))!=k1_xboole_0 | v2_struct_0('#skF_9'(B_212)) | ~l1_waybel_0(B_212, '#skF_7') | ~v7_waybel_0(B_212) | ~v4_orders_2(B_212) | v2_struct_0(B_212))), inference(resolution, [status(thm)], [c_174, c_219])).
% 6.06/2.26  tff(c_155, plain, (![B_157]: (~v2_struct_0('#skF_9'(B_157)) | ~l1_waybel_0(B_157, '#skF_7') | ~v7_waybel_0(B_157) | ~v4_orders_2(B_157) | v2_struct_0(B_157))), inference(splitRight, [status(thm)], [c_139])).
% 6.06/2.26  tff(c_229, plain, (![B_212]: (k10_yellow_6('#skF_7', '#skF_9'(B_212))!=k1_xboole_0 | ~l1_waybel_0(B_212, '#skF_7') | ~v7_waybel_0(B_212) | ~v4_orders_2(B_212) | v2_struct_0(B_212))), inference(resolution, [status(thm)], [c_225, c_155])).
% 6.06/2.26  tff(c_1005, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_229])).
% 6.06/2.26  tff(c_1061, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_821, c_878, c_924, c_1005])).
% 6.06/2.26  tff(c_1063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_959, c_1061])).
% 6.06/2.26  tff(c_1064, plain, (v2_struct_0('#skF_9'('#skF_6'('#skF_7')))), inference(splitRight, [status(thm)], [c_958])).
% 6.06/2.26  tff(c_1068, plain, (~l1_waybel_0('#skF_6'('#skF_7'), '#skF_7') | ~v7_waybel_0('#skF_6'('#skF_7')) | ~v4_orders_2('#skF_6'('#skF_7')) | v2_struct_0('#skF_6'('#skF_7'))), inference(resolution, [status(thm)], [c_1064, c_155])).
% 6.06/2.26  tff(c_1071, plain, (v2_struct_0('#skF_6'('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_821, c_878, c_924, c_1068])).
% 6.06/2.26  tff(c_1073, plain, $false, inference(negUnitSimplification, [status(thm)], [c_959, c_1071])).
% 6.06/2.26  tff(c_1074, plain, (~v2_struct_0('#skF_8')), inference(splitRight, [status(thm)], [c_82])).
% 6.06/2.26  tff(c_1075, plain, (v1_compts_1('#skF_7')), inference(splitRight, [status(thm)], [c_82])).
% 6.06/2.26  tff(c_80, plain, (v4_orders_2('#skF_8') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_1077, plain, (v4_orders_2('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_80])).
% 6.06/2.26  tff(c_78, plain, (v7_waybel_0('#skF_8') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_1080, plain, (v7_waybel_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_78])).
% 6.06/2.26  tff(c_76, plain, (l1_waybel_0('#skF_8', '#skF_7') | ~v1_compts_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_1083, plain, (l1_waybel_0('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_76])).
% 6.06/2.26  tff(c_64, plain, (![A_138, B_145]: (r3_waybel_9(A_138, B_145, '#skF_5'(A_138, B_145)) | ~l1_waybel_0(B_145, A_138) | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.06/2.26  tff(c_66, plain, (![A_138, B_145]: (m1_subset_1('#skF_5'(A_138, B_145), u1_struct_0(A_138)) | ~l1_waybel_0(B_145, A_138) | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_246])).
% 6.06/2.26  tff(c_1129, plain, (![A_486, B_487, C_488]: (m2_yellow_6('#skF_4'(A_486, B_487, C_488), A_486, B_487) | ~r3_waybel_9(A_486, B_487, C_488) | ~m1_subset_1(C_488, u1_struct_0(A_486)) | ~l1_waybel_0(B_487, A_486) | ~v7_waybel_0(B_487) | ~v4_orders_2(B_487) | v2_struct_0(B_487) | ~l1_pre_topc(A_486) | ~v2_pre_topc(A_486) | v2_struct_0(A_486))), inference(cnfTransformation, [status(thm)], [f_222])).
% 6.06/2.26  tff(c_34, plain, (![C_98, A_95, B_96]: (l1_waybel_0(C_98, A_95) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.06/2.26  tff(c_1213, plain, (![A_513, B_514, C_515]: (l1_waybel_0('#skF_4'(A_513, B_514, C_515), A_513) | ~l1_struct_0(A_513) | ~r3_waybel_9(A_513, B_514, C_515) | ~m1_subset_1(C_515, u1_struct_0(A_513)) | ~l1_waybel_0(B_514, A_513) | ~v7_waybel_0(B_514) | ~v4_orders_2(B_514) | v2_struct_0(B_514) | ~l1_pre_topc(A_513) | ~v2_pre_topc(A_513) | v2_struct_0(A_513))), inference(resolution, [status(thm)], [c_1129, c_34])).
% 6.06/2.26  tff(c_1268, plain, (![A_560, B_561, B_562]: (l1_waybel_0('#skF_4'(A_560, B_561, '#skF_5'(A_560, B_562)), A_560) | ~l1_struct_0(A_560) | ~r3_waybel_9(A_560, B_561, '#skF_5'(A_560, B_562)) | ~l1_waybel_0(B_561, A_560) | ~v7_waybel_0(B_561) | ~v4_orders_2(B_561) | v2_struct_0(B_561) | ~l1_waybel_0(B_562, A_560) | ~v7_waybel_0(B_562) | ~v4_orders_2(B_562) | v2_struct_0(B_562) | ~v1_compts_1(A_560) | ~l1_pre_topc(A_560) | ~v2_pre_topc(A_560) | v2_struct_0(A_560))), inference(resolution, [status(thm)], [c_66, c_1213])).
% 6.06/2.26  tff(c_42, plain, (![B_101, A_99]: (v3_yellow_6(B_101, A_99) | k10_yellow_6(A_99, B_101)=k1_xboole_0 | ~l1_waybel_0(B_101, A_99) | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101) | ~l1_pre_topc(A_99) | ~v2_pre_topc(A_99) | v2_struct_0(A_99))), inference(cnfTransformation, [status(thm)], [f_142])).
% 6.06/2.26  tff(c_74, plain, (![C_156]: (~v3_yellow_6(C_156, '#skF_7') | ~m2_yellow_6(C_156, '#skF_7', '#skF_8') | ~v1_compts_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_271])).
% 6.06/2.26  tff(c_1085, plain, (![C_156]: (~v3_yellow_6(C_156, '#skF_7') | ~m2_yellow_6(C_156, '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1075, c_74])).
% 6.06/2.26  tff(c_1145, plain, (![C_488]: (~v3_yellow_6('#skF_4'('#skF_7', '#skF_8', C_488), '#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', C_488) | ~m1_subset_1(C_488, u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1129, c_1085])).
% 6.06/2.26  tff(c_1152, plain, (![C_488]: (~v3_yellow_6('#skF_4'('#skF_7', '#skF_8', C_488), '#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', C_488) | ~m1_subset_1(C_488, u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1077, c_1080, c_1083, c_1145])).
% 6.06/2.26  tff(c_1154, plain, (![C_489]: (~v3_yellow_6('#skF_4'('#skF_7', '#skF_8', C_489), '#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', C_489) | ~m1_subset_1(C_489, u1_struct_0('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_72, c_1074, c_1152])).
% 6.06/2.26  tff(c_1157, plain, (![C_489]: (~r3_waybel_9('#skF_7', '#skF_8', C_489) | ~m1_subset_1(C_489, u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', C_489))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', C_489), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', C_489)) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', C_489)) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', C_489)) | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_42, c_1154])).
% 6.06/2.26  tff(c_1160, plain, (![C_489]: (~r3_waybel_9('#skF_7', '#skF_8', C_489) | ~m1_subset_1(C_489, u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', C_489))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', C_489), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', C_489)) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', C_489)) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', C_489)) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1157])).
% 6.06/2.26  tff(c_1195, plain, (![C_509]: (~r3_waybel_9('#skF_7', '#skF_8', C_509) | ~m1_subset_1(C_509, u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', C_509))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', C_509), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', C_509)) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', C_509)) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', C_509)))), inference(negUnitSimplification, [status(thm)], [c_72, c_1160])).
% 6.06/2.26  tff(c_1203, plain, (![B_145]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1195])).
% 6.06/2.26  tff(c_1210, plain, (![B_145]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1075, c_1203])).
% 6.06/2.26  tff(c_1211, plain, (![B_145]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)))=k1_xboole_0 | ~l1_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)), '#skF_7') | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145))), inference(negUnitSimplification, [status(thm)], [c_72, c_1210])).
% 6.06/2.26  tff(c_1272, plain, (![B_562]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562)) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_562, '#skF_7') | ~v7_waybel_0(B_562) | ~v4_orders_2(B_562) | v2_struct_0(B_562) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1268, c_1211])).
% 6.06/2.26  tff(c_1275, plain, (![B_562]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_562, '#skF_7') | ~v7_waybel_0(B_562) | ~v4_orders_2(B_562) | v2_struct_0(B_562) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1075, c_1077, c_1080, c_1083, c_1272])).
% 6.06/2.26  tff(c_1276, plain, (![B_562]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_562)) | ~l1_waybel_0(B_562, '#skF_7') | ~v7_waybel_0(B_562) | ~v4_orders_2(B_562) | v2_struct_0(B_562))), inference(negUnitSimplification, [status(thm)], [c_72, c_1074, c_1275])).
% 6.06/2.26  tff(c_1277, plain, (~l1_struct_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1276])).
% 6.06/2.26  tff(c_1280, plain, (~l1_pre_topc('#skF_7')), inference(resolution, [status(thm)], [c_10, c_1277])).
% 6.06/2.26  tff(c_1284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1280])).
% 6.06/2.26  tff(c_1286, plain, (l1_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_1276])).
% 6.06/2.26  tff(c_38, plain, (![C_98, A_95, B_96]: (v4_orders_2(C_98) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.06/2.26  tff(c_1162, plain, (![A_490, B_491, C_492]: (v4_orders_2('#skF_4'(A_490, B_491, C_492)) | ~l1_struct_0(A_490) | ~r3_waybel_9(A_490, B_491, C_492) | ~m1_subset_1(C_492, u1_struct_0(A_490)) | ~l1_waybel_0(B_491, A_490) | ~v7_waybel_0(B_491) | ~v4_orders_2(B_491) | v2_struct_0(B_491) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(resolution, [status(thm)], [c_1129, c_38])).
% 6.06/2.26  tff(c_1165, plain, (![A_138, B_491, B_145]: (v4_orders_2('#skF_4'(A_138, B_491, '#skF_5'(A_138, B_145))) | ~l1_struct_0(A_138) | ~r3_waybel_9(A_138, B_491, '#skF_5'(A_138, B_145)) | ~l1_waybel_0(B_491, A_138) | ~v7_waybel_0(B_491) | ~v4_orders_2(B_491) | v2_struct_0(B_491) | ~l1_waybel_0(B_145, A_138) | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_66, c_1162])).
% 6.06/2.26  tff(c_36, plain, (![C_98, A_95, B_96]: (v7_waybel_0(C_98) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.06/2.26  tff(c_1171, plain, (![A_500, B_501, C_502]: (v7_waybel_0('#skF_4'(A_500, B_501, C_502)) | ~l1_struct_0(A_500) | ~r3_waybel_9(A_500, B_501, C_502) | ~m1_subset_1(C_502, u1_struct_0(A_500)) | ~l1_waybel_0(B_501, A_500) | ~v7_waybel_0(B_501) | ~v4_orders_2(B_501) | v2_struct_0(B_501) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(resolution, [status(thm)], [c_1129, c_36])).
% 6.06/2.26  tff(c_1174, plain, (![A_138, B_501, B_145]: (v7_waybel_0('#skF_4'(A_138, B_501, '#skF_5'(A_138, B_145))) | ~l1_struct_0(A_138) | ~r3_waybel_9(A_138, B_501, '#skF_5'(A_138, B_145)) | ~l1_waybel_0(B_501, A_138) | ~v7_waybel_0(B_501) | ~v4_orders_2(B_501) | v2_struct_0(B_501) | ~l1_waybel_0(B_145, A_138) | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~v1_compts_1(A_138) | ~l1_pre_topc(A_138) | ~v2_pre_topc(A_138) | v2_struct_0(A_138))), inference(resolution, [status(thm)], [c_66, c_1171])).
% 6.06/2.26  tff(c_1288, plain, (![B_565]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_565)))=k1_xboole_0 | ~v7_waybel_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_565))) | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_565))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_565))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_565)) | ~l1_waybel_0(B_565, '#skF_7') | ~v7_waybel_0(B_565) | ~v4_orders_2(B_565) | v2_struct_0(B_565))), inference(splitRight, [status(thm)], [c_1276])).
% 6.06/2.26  tff(c_1292, plain, (![B_145]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1174, c_1288])).
% 6.06/2.26  tff(c_1295, plain, (![B_145]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1075, c_1077, c_1080, c_1083, c_1286, c_1292])).
% 6.06/2.26  tff(c_1297, plain, (![B_566]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_566)))=k1_xboole_0 | ~v4_orders_2('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_566))) | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_566))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_566)) | ~l1_waybel_0(B_566, '#skF_7') | ~v7_waybel_0(B_566) | ~v4_orders_2(B_566) | v2_struct_0(B_566))), inference(negUnitSimplification, [status(thm)], [c_72, c_1074, c_1295])).
% 6.06/2.26  tff(c_1301, plain, (![B_145]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~l1_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_1165, c_1297])).
% 6.06/2.26  tff(c_1304, plain, (![B_145]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | v2_struct_0('#skF_8') | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1075, c_1077, c_1080, c_1083, c_1286, c_1301])).
% 6.06/2.26  tff(c_1306, plain, (![B_567]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_567)))=k1_xboole_0 | v2_struct_0('#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_567))) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_567)) | ~l1_waybel_0(B_567, '#skF_7') | ~v7_waybel_0(B_567) | ~v4_orders_2(B_567) | v2_struct_0(B_567))), inference(negUnitSimplification, [status(thm)], [c_72, c_1074, c_1304])).
% 6.06/2.26  tff(c_40, plain, (![C_98, A_95, B_96]: (~v2_struct_0(C_98) | ~m2_yellow_6(C_98, A_95, B_96) | ~l1_waybel_0(B_96, A_95) | ~v7_waybel_0(B_96) | ~v4_orders_2(B_96) | v2_struct_0(B_96) | ~l1_struct_0(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.06/2.26  tff(c_1148, plain, (![A_486, B_487, C_488]: (~v2_struct_0('#skF_4'(A_486, B_487, C_488)) | ~l1_struct_0(A_486) | ~r3_waybel_9(A_486, B_487, C_488) | ~m1_subset_1(C_488, u1_struct_0(A_486)) | ~l1_waybel_0(B_487, A_486) | ~v7_waybel_0(B_487) | ~v4_orders_2(B_487) | v2_struct_0(B_487) | ~l1_pre_topc(A_486) | ~v2_pre_topc(A_486) | v2_struct_0(A_486))), inference(resolution, [status(thm)], [c_1129, c_40])).
% 6.06/2.26  tff(c_1308, plain, (![B_567]: (~l1_struct_0('#skF_7') | ~m1_subset_1('#skF_5'('#skF_7', B_567), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_567)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_567)) | ~l1_waybel_0(B_567, '#skF_7') | ~v7_waybel_0(B_567) | ~v4_orders_2(B_567) | v2_struct_0(B_567))), inference(resolution, [status(thm)], [c_1306, c_1148])).
% 6.06/2.26  tff(c_1311, plain, (![B_567]: (~m1_subset_1('#skF_5'('#skF_7', B_567), u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7') | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_567)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_567)) | ~l1_waybel_0(B_567, '#skF_7') | ~v7_waybel_0(B_567) | ~v4_orders_2(B_567) | v2_struct_0(B_567))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1077, c_1080, c_1083, c_1286, c_1308])).
% 6.06/2.26  tff(c_1313, plain, (![B_568]: (~m1_subset_1('#skF_5'('#skF_7', B_568), u1_struct_0('#skF_7')) | k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_568)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_568)) | ~l1_waybel_0(B_568, '#skF_7') | ~v7_waybel_0(B_568) | ~v4_orders_2(B_568) | v2_struct_0(B_568))), inference(negUnitSimplification, [status(thm)], [c_72, c_1074, c_1311])).
% 6.06/2.26  tff(c_1317, plain, (![B_145]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1313])).
% 6.06/2.26  tff(c_1320, plain, (![B_145]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1075, c_1317])).
% 6.06/2.26  tff(c_1326, plain, (![B_572]: (k10_yellow_6('#skF_7', '#skF_4'('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_572)))=k1_xboole_0 | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_572)) | ~l1_waybel_0(B_572, '#skF_7') | ~v7_waybel_0(B_572) | ~v4_orders_2(B_572) | v2_struct_0(B_572))), inference(negUnitSimplification, [status(thm)], [c_72, c_1320])).
% 6.06/2.26  tff(c_1175, plain, (![C_503, A_504, B_505]: (r2_hidden(C_503, k10_yellow_6(A_504, '#skF_4'(A_504, B_505, C_503))) | ~r3_waybel_9(A_504, B_505, C_503) | ~m1_subset_1(C_503, u1_struct_0(A_504)) | ~l1_waybel_0(B_505, A_504) | ~v7_waybel_0(B_505) | ~v4_orders_2(B_505) | v2_struct_0(B_505) | ~l1_pre_topc(A_504) | ~v2_pre_topc(A_504) | v2_struct_0(A_504))), inference(cnfTransformation, [status(thm)], [f_222])).
% 6.06/2.26  tff(c_1187, plain, (![A_504, B_505, C_503]: (~r1_tarski(k10_yellow_6(A_504, '#skF_4'(A_504, B_505, C_503)), C_503) | ~r3_waybel_9(A_504, B_505, C_503) | ~m1_subset_1(C_503, u1_struct_0(A_504)) | ~l1_waybel_0(B_505, A_504) | ~v7_waybel_0(B_505) | ~v4_orders_2(B_505) | v2_struct_0(B_505) | ~l1_pre_topc(A_504) | ~v2_pre_topc(A_504) | v2_struct_0(A_504))), inference(resolution, [status(thm)], [c_1175, c_8])).
% 6.06/2.26  tff(c_1337, plain, (![B_572]: (~r1_tarski(k1_xboole_0, '#skF_5'('#skF_7', B_572)) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_572)) | ~m1_subset_1('#skF_5'('#skF_7', B_572), u1_struct_0('#skF_7')) | ~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_572)) | ~l1_waybel_0(B_572, '#skF_7') | ~v7_waybel_0(B_572) | ~v4_orders_2(B_572) | v2_struct_0(B_572))), inference(superposition, [status(thm), theory('equality')], [c_1326, c_1187])).
% 6.06/2.26  tff(c_1361, plain, (![B_572]: (~m1_subset_1('#skF_5'('#skF_7', B_572), u1_struct_0('#skF_7')) | v2_struct_0('#skF_8') | v2_struct_0('#skF_7') | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_572)) | ~l1_waybel_0(B_572, '#skF_7') | ~v7_waybel_0(B_572) | ~v4_orders_2(B_572) | v2_struct_0(B_572))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1077, c_1080, c_1083, c_2, c_1337])).
% 6.06/2.26  tff(c_1376, plain, (![B_573]: (~m1_subset_1('#skF_5'('#skF_7', B_573), u1_struct_0('#skF_7')) | ~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_573)) | ~l1_waybel_0(B_573, '#skF_7') | ~v7_waybel_0(B_573) | ~v4_orders_2(B_573) | v2_struct_0(B_573))), inference(negUnitSimplification, [status(thm)], [c_72, c_1074, c_1361])).
% 6.06/2.26  tff(c_1380, plain, (![B_145]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7'))), inference(resolution, [status(thm)], [c_66, c_1376])).
% 6.06/2.26  tff(c_1383, plain, (![B_145]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_145)) | ~l1_waybel_0(B_145, '#skF_7') | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | v2_struct_0('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1075, c_1380])).
% 6.06/2.26  tff(c_1385, plain, (![B_574]: (~r3_waybel_9('#skF_7', '#skF_8', '#skF_5'('#skF_7', B_574)) | ~l1_waybel_0(B_574, '#skF_7') | ~v7_waybel_0(B_574) | ~v4_orders_2(B_574) | v2_struct_0(B_574))), inference(negUnitSimplification, [status(thm)], [c_72, c_1383])).
% 6.06/2.26  tff(c_1393, plain, (~l1_waybel_0('#skF_8', '#skF_7') | ~v7_waybel_0('#skF_8') | ~v4_orders_2('#skF_8') | v2_struct_0('#skF_8') | ~v1_compts_1('#skF_7') | ~l1_pre_topc('#skF_7') | ~v2_pre_topc('#skF_7') | v2_struct_0('#skF_7')), inference(resolution, [status(thm)], [c_64, c_1385])).
% 6.06/2.26  tff(c_1400, plain, (v2_struct_0('#skF_8') | v2_struct_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1075, c_1077, c_1080, c_1083, c_1393])).
% 6.06/2.26  tff(c_1402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_1074, c_1400])).
% 6.06/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.26  
% 6.06/2.26  Inference rules
% 6.06/2.26  ----------------------
% 6.06/2.26  #Ref     : 0
% 6.06/2.26  #Sup     : 231
% 6.06/2.26  #Fact    : 2
% 6.06/2.26  #Define  : 0
% 6.06/2.26  #Split   : 17
% 6.06/2.26  #Chain   : 0
% 6.06/2.26  #Close   : 0
% 6.06/2.26  
% 6.06/2.26  Ordering : KBO
% 6.06/2.26  
% 6.06/2.26  Simplification rules
% 6.06/2.26  ----------------------
% 6.06/2.26  #Subsume      : 65
% 6.06/2.26  #Demod        : 257
% 6.06/2.26  #Tautology    : 40
% 6.06/2.26  #SimpNegUnit  : 56
% 6.06/2.26  #BackRed      : 0
% 6.06/2.26  
% 6.06/2.26  #Partial instantiations: 0
% 6.06/2.26  #Strategies tried      : 1
% 6.06/2.26  
% 6.06/2.26  Timing (in seconds)
% 6.06/2.26  ----------------------
% 6.06/2.27  Preprocessing        : 0.44
% 6.06/2.27  Parsing              : 0.19
% 6.06/2.27  CNF conversion       : 0.06
% 6.06/2.27  Main loop            : 0.94
% 6.06/2.27  Inferencing          : 0.37
% 6.06/2.27  Reduction            : 0.25
% 6.06/2.27  Demodulation         : 0.16
% 6.06/2.27  BG Simplification    : 0.07
% 6.06/2.27  Subsumption          : 0.23
% 6.06/2.27  Abstraction          : 0.04
% 6.06/2.27  MUC search           : 0.00
% 6.06/2.27  Cooper               : 0.00
% 6.06/2.27  Total                : 1.48
% 6.06/2.27  Index Insertion      : 0.00
% 6.06/2.27  Index Deletion       : 0.00
% 6.06/2.27  Index Matching       : 0.00
% 6.06/2.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
